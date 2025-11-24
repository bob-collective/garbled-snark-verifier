//! High-level driver showcasing the cut-and-choose Setup/Evaluate flow from
//! `docs/gsv_spec.md` using the Groth16 verifier gadget.
use std::{path::PathBuf, thread};

use ark_ff::AdditiveGroup;
use ark_secp256k1::Fr;
use bitcoin::{
    Address, Amount, Network, OutPoint, ScriptBuf, Transaction, TxIn, TxOut, absolute::LockTime, address::NetworkUnchecked, consensus, script::PushBytes, taproot::LeafVersion, transaction::Version
};
use crossbeam::channel::{self};
use garbled_snark_verifier::{
    EvaluatedWire,
    ark::{
        self, Bn254, CircuitSpecificSetupSNARK, Groth16 as ArkGroth16, ProvingKey as ArkProvingKey,
        SNARK, UniformRand,
    },
    circuit::CiphertextSender,
    cut_and_choose::{
        Evaluator, EvaluatorCaseInput, FileCiphertextHandlerProvider, VsssGarbler,
        vsss::{
            Challenge, EvaluatorAdaptorSigs, FinalizeChallenge, SetupBroadcast, SetupResponse,
            VsssStreamReceivers, rand_schnorr_sk,
        },
    },
    garbled_groth16::{self, EvaluatorCompressedInput},
    groth16_cut_and_choose::{self as ccn, DEFAULT_CAPACITY},
    hashers::DefaultLabelCommitHasher,
};
use itertools::Itertools;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use tracing::info;

const MY_RAND_SEED: u64 = 9874971987365;
// Configuration constants - modify these as needed
const TOTAL_INSTANCES: usize = 4;
const FINALIZE_INSTANCES: usize = 2;
const OUT_DIR: &str = "target/cut_and_choose";
const K_CONSTRAINTS: u32 = 5; // 2^k constraints
const IS_PROOF_CORRECT: bool = true;

// Calculate and display total gates to process
const GATES_PER_INSTANCE: u64 = 11_174_708_821;

// note: uncomment to use a dummy circuit for faster tetsing. Note that the evaluation will fail
// due to the input being incorrect.
use dummy_circuit::verify_compressed as circuit_verify;
// use garbled_groth16::verify_compressed as circuit_verify;

use crate::taproot_tx::{address_from_spend_info, spend_info_from_script};

mod dummy_circuit {
    use garbled_snark_verifier::{
        CircuitContext, Gate, WireId,
        circuit::{TRUE_WIRE, WiresObject},
        gadgets::groth16::Groth16VerifyCompressedInputWires,
    };

    #[allow(unused)]
    pub fn verify_compressed<C: CircuitContext>(
        circuit: &mut C,
        input: &Groth16VerifyCompressedInputWires,
    ) -> WireId {
        let input_wires = input.to_wires_vec();
        let output_wire = circuit.issue_wire();

        let mut it = input_wires.iter();
        let mut one_bits: Vec<WireId> = Vec::new();
        let mut zero_bits: Vec<WireId> = Vec::new();
        for i in 0.. {
            zero_bits.extend(it.by_ref().take(i));
            match it.next() {
                Some(wire) => {
                    one_bits.push(wire.clone());
                }
                None => {
                    break;
                }
            }
        }

        let ones_ok = one_bits
            .into_iter()
            .reduce(|a, b| {
                let c = circuit.issue_wire();
                circuit.add_gate(Gate::and(a, b, c));
                c
            })
            .unwrap();

        let zeroes_not_ok = zero_bits
            .into_iter()
            .reduce(|a, b| {
                let c = circuit.issue_wire();
                circuit.add_gate(Gate::or(a, b, c));
                c
            })
            .unwrap();

        let zeroes_ok = circuit.issue_wire();
        circuit.add_gate(Gate::xor(zeroes_not_ok, TRUE_WIRE, zeroes_ok));

        circuit.add_gate(Gate::and(ones_ok, zeroes_ok, output_wire));

        output_wire
    }
}

// Simple multiplicative circuit used to produce a valid Groth16 proof.
#[derive(Copy, Clone)]
#[allow(unused)]
struct DummyCircuit<F: ark::PrimeField> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_variables: usize,
    pub num_constraints: usize,
}

impl<F: ark::PrimeField> ark::ConstraintSynthesizer<F> for DummyCircuit<F> {
    fn generate_constraints(
        self,
        cs: ark::ConstraintSystemRef<F>,
    ) -> Result<(), ark::SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(ark::SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(ark::SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let a = self.a.ok_or(ark::SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(ark::SynthesisError::AssignmentMissing)?;
            Ok(a * b)
        })?;

        // pad witnesses
        for _ in 0..(self.num_variables - 3) {
            let _ =
                cs.new_witness_variable(|| self.a.ok_or(ark::SynthesisError::AssignmentMissing))?;
        }

        // repeat the same multiplicative constraint
        for _ in 0..self.num_constraints - 1 {
            cs.enforce_constraint(ark::lc!() + a, ark::lc!() + b, ark::lc!() + c)?;
        }

        // final no-op constraint keeps ark-relations happy
        cs.enforce_constraint(ark::lc!(), ark::lc!(), ark::lc!())?;
        Ok(())
    }
}

fn main() {
    // taproot_tx::test_fail();
    // return;

    if !garbled_snark_verifier::hardware_aes_available() {
        eprintln!(
            "Warning: AES hardware acceleration not detected; using software AES (not constant-time)."
        );
    }

    garbled_snark_verifier::init_tracing();

    // Configuration
    let total = TOTAL_INSTANCES;
    let finalize = FINALIZE_INSTANCES;
    let out_dir: PathBuf = OUT_DIR.into();
    let k = K_CONSTRAINTS; // 2^k constraints

    // 1) Build and prove a tiny multiplicative circuit
    let mut rng = ChaCha20Rng::seed_from_u64(12345);
    let circuit = DummyCircuit::<ark::Fr> {
        a: Some(ark::Fr::rand(&mut rng)),
        b: Some(ark::Fr::rand(&mut rng)),
        num_variables: 10,
        num_constraints: 1 << k,
    };
    let (pk, vk) = ark::Groth16::<ark::Bn254>::setup(circuit, &mut rng).expect("setup");
    let public_input = if IS_PROOF_CORRECT {
        circuit.a.unwrap() * circuit.b.unwrap()
    } else {
        ark::Fr::ZERO
    };

    // Package inputs for garbling/evaluation gadgets
    let g_input = garbled_groth16::GarblerInput {
        public_params_len: 1,
        vk: vk.clone(),
    }
    .compress();

    let total_gates = GATES_PER_INSTANCE * total as u64;
    info!("Starting cut-and-choose with {} instances", total);

    info!(
        "Total gates to process in first stage: {:.2}B",
        total_gates as f64 / 1_000_000_000.0
    );

    info!(
        "Gates per instance: {:.2}B",
        GATES_PER_INSTANCE as f64 / 1_000_000_000.0
    );

    let (g2e_tx, g2e_rx) = channel::unbounded::<SetupBroadcast<DefaultLabelCommitHasher>>();
    let (e2g_tx, e2g_rx) = channel::unbounded::<SetupResponse<CiphertextSender>>();

    let garbler_cfg = ccn::Config::new(total, finalize, g_input.clone());
    let evaluator_cfg = garbler_cfg.clone();

    let garbler = thread::spawn(move || {
        run_garbler(
            garbler_cfg,
            pk.clone(),
            circuit,
            public_input,
            g2e_tx,
            e2g_rx,
        );
    });

    let evaluator = thread::spawn(move || run_evaluator(evaluator_cfg, out_dir, g2e_rx, e2g_tx));

    garbler.join().unwrap();
    let evaluator = evaluator.join().unwrap();

    let errors = evaluator
        .iter()
        .filter_map(|(i, ew)| (ew.value != IS_PROOF_CORRECT).then_some(i))
        .collect::<Vec<_>>();

    assert!(errors.is_empty(), "errors: {errors:?}")
}

#[allow(unused)]
fn run_garbler(
    cfg: ccn::Config,
    pk: ArkProvingKey<Bn254>,
    circuit: DummyCircuit<ark::Fr>,
    public_input: ark::Fr,
    g2e_tx: channel::Sender<SetupBroadcast<DefaultLabelCommitHasher>>,
    e2g_rx: channel::Receiver<SetupResponse<CiphertextSender>>,
) {
    let mut seed_rng = ChaCha20Rng::seed_from_u64(MY_RAND_SEED);

    info!(
        "Garbler: {total}/{to_finalize}",
        total = cfg.total(),
        to_finalize = cfg.to_finalize(),
    );

    info!("Garbler: creating instances...");
    let mut g = ccn::VsssGarbler::from_inner(VsssGarbler::create(
        &mut seed_rng,
        cfg.clone(),
        DEFAULT_CAPACITY,
        circuit_verify,
    ));

    info!("Garbler: generating commits...");
    let commits = g.commit::<DefaultLabelCommitHasher>();
    info!("Garbler: sending commits...");
    g2e_tx
        .send(SetupBroadcast::Commit(
            g.commit::<DefaultLabelCommitHasher>(),
        ))
        .expect("send commits");

    // Step 2 — Evaluator challenges the Garbler with the finalize set.
    info!("Garbler: waiting for FinalizeChallenge...");
    let SetupResponse::FinalizeChallenge(challenge) = e2g_rx.recv().expect("recv finalize senders");
    info!("Garbler: received FinalizeChallenge...");

    info!("Garbler: opening instances...");
    let finalize_indices = challenge.to_finalize.iter().map(|x| x.index).collect_vec();
    let (opened_instance_data, finalized_instance_data) = g
        .inner()
        .open_commit(challenge.to_finalize.clone(), circuit_verify);

    let finalized_instance_data_indices = finalized_instance_data
        .iter()
        .map(|x| x.index)
        .collect_vec();

    let opened_instance_data_indices = opened_instance_data.iter().map(|x| x.index).collect_vec();

    let (garbling_threads, wide_label_looksup): (Vec<_>, Vec<_>) = finalized_instance_data
        .into_iter()
        .map(|x| (x.garbling_thread, (x.index, x.wide_label_lookup)))
        .unzip();

    info!("Garbler: sending OpenInstances...");

    g2e_tx
        .send(SetupBroadcast::OpenInstances(
            opened_instance_data,
            wide_label_looksup,
        ))
        .expect("send open instances");

    garbling_threads.into_iter().for_each(|thread| {
        thread.join().unwrap();
    });

    info!("Garbler: generating proof...");
    let challenge_proof =
        ArkGroth16::<Bn254>::prove(&pk, circuit, &mut ChaCha20Rng::seed_from_u64(42))
            .expect("prove");
    info!("Garbler: finished generating proof...");

    // Verify the proof is valid before garbling
    let is_valid = ArkGroth16::<Bn254>::verify(&cfg.input().vk, &[public_input], &challenge_proof)
        .expect("verify");

    assert_eq!(
        is_valid, IS_PROOF_CORRECT,
        "Proof must be valid before garbling!"
    );

    info!("Garbler: generating adaptor signatures...");
    let inputs = g
        .prepare_input_labels(vec![public_input], challenge_proof, challenge.assert_index)
        .input;
    let wide_labels = g.wide_labels_for(challenge.assert_index);
    let sigs = challenge.compute_signatures(&wide_labels, &inputs);
    info!("Garbler: finished generating adaptor signatures...");

    info!("Garbler: sending Assert...");
    g2e_tx
        .send(SetupBroadcast::Assert(sigs))
        .expect("send open instances");
}

#[allow(unused)]
fn run_evaluator(
    cfg: ccn::Config,
    out_dir: PathBuf,
    g2e_rx: channel::Receiver<SetupBroadcast<DefaultLabelCommitHasher>>,
    e2g_tx: channel::Sender<SetupResponse<CiphertextSender>>,
) -> Vec<(usize, EvaluatedWire)> {
    let mut rng = ChaCha20Rng::seed_from_u64(MY_RAND_SEED);

    let finalize = cfg.to_finalize();

    // Step 1 — receive Commits.
    info!("Evaluator: waiting for commits...");
    let SetupBroadcast::Commit(commits) = g2e_rx.recv().expect("recv commits") else {
        panic!("unexpected message; expected commits")
    };
    info!("Evaluator: received commits...");

    // Evaluator chooses which instances to finalize with first commits
    info!("Evaluator: setting up evaluator...");
    let mut eval: Evaluator<garbled_groth16::GarblerCompressedInput, DefaultLabelCommitHasher> =
        Evaluator::create_vsss(&mut rng, cfg.clone(), commits.clone());
    let finalize_indices: Vec<usize> = eval.finalized_indexes().to_vec();

    let (tx_data, receivers): (Vec<_>, Vec<_>) = finalize_indices
        .iter()
        .map(|&index| {
            let (label_tx, label_rx) = channel::unbounded();
            let tx = FinalizeChallenge {
                index,
                ciphertext_handler: label_tx,
            };
            let rx = VsssStreamReceivers {
                index,
                ciphertext_receiver: label_rx,
            };
            (tx, rx)
        })
        .unzip();

        
    info!("Evaluator: setting up adaptor sigs...");
    let num_sigs = commits.share_commits.len().div_ceil(256);
    println!("num_sigs: {}", num_sigs);

    let secret = rand_schnorr_sk(&mut rng);
    let script = taproot_tx::script_for(secret, num_sigs);

    let mut tx = Transaction {
        version: Version::non_standard(3),
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: OutPoint {
                txid: "7fcf7ae9574d5b1efe8fc3777d0f45ffb8f0599a65db52642460e2b97cf2d19b".parse().unwrap(),
                vout: 1
            },
            ..Default::default()
        }],
        output: vec![TxOut {
            value: Amount::from_sat(240),
            script_pubkey: bitcoin::ScriptBuf::new_p2a(),
        },
        TxOut {
            value: Amount::ZERO,
            script_pubkey: bitcoin::ScriptBuf::new_op_return::<&PushBytes>((& hex::decode("0b0b").unwrap()[..]).try_into().unwrap()),
        }
        ],
    };
    println!("txid of input: {}", tx.input[0].previous_output.txid);
    let spend_info = spend_info_from_script(script.clone());
    let address = address_from_spend_info(&spend_info, Network::Bitcoin);

    println!("The address with the script: {}", address);
    println!("Script pubkey: {}", hex::encode(address.script_pubkey().to_bytes()));
    let prevouts = vec![TxOut {
        value: Amount::from_sat(330),
        script_pubkey: address.script_pubkey(),
    }];
    let sighashes = taproot_tx::sighashes(&tx, &prevouts, &script, num_sigs);

    let adaptor_sigs = {
        EvaluatorAdaptorSigs::new(
            &mut rng,
            secret,
            &finalize_indices,
            &commits.share_commits,
            &sighashes,
        )
    };

    info!("Evaluator: sending FinalizeChallenge...");
    e2g_tx
        .send(SetupResponse::FinalizeChallenge(Challenge {
            to_finalize: tx_data,
            adaptor_sigs: adaptor_sigs.adaptor_sigs.clone(),
            assert_index: adaptor_sigs.assert_index,
        }))
        .expect("send finalize challenge");

    info!("Evaluator: waiting for OpenInstances...");
    let SetupBroadcast::OpenInstances(open_instance_data, wide_label_lookups) =
        g2e_rx.recv().expect("recv commits")
    else {
        panic!("unexpected message; expected commits")
    };
    info!("Evaluator: received OpenInstances...");

    let out_dir = PathBuf::from("target/cut_and_choose_test_simple");
    let handler_provider =
        FileCiphertextHandlerProvider::new(out_dir.clone(), None).expect("create sink provider");

    info!("Evaluator: regarbling...");
    eval.run_regarbling_vsss(
        &open_instance_data,
        &receivers,
        &handler_provider,
        DEFAULT_CAPACITY,
        circuit_verify,
        &wide_label_lookups,
    )
    .expect("regarbling ok");

    info!("Evaluator: waiting for asserts...");
    let SetupBroadcast::Assert(signatures) = g2e_rx.recv().expect("recv asserts") else {
        panic!("unexpected message; expected asserts")
    };
    info!("Evaluator: received asserts...");

    info!("Evaluator: evaluating wires...");
    let inputs = adaptor_sigs
        .evaluated_wires(
            &signatures,
            &wide_label_lookups,
            &open_instance_data,
            cfg.total(),
        )
        .into_iter()
        .map(|(index, wires)| {
            let input =
                EvaluatorCompressedInput::from_evaluated_inputs(1, wires, cfg.input().vk.clone());
            EvaluatorCaseInput { index, input }
        })
        .collect();

    info!("Evaluator: running asserts...");

    let control_block = spend_info
        .control_block(&(script.clone(), LeafVersion::TapScript))
        .unwrap()
        .serialize();

    println!("Non-witness witness weight: {} vsize {}", tx.weight(), tx.vsize());

    assert!(signatures.len() == num_sigs);
    tx.input[0].witness = [
        signatures
            .iter()
            .cloned()
            .map(|x| x.to_vec())
            .rev()
            .collect::<Vec<_>>(),
        vec![script.to_bytes(), control_block.clone()],
    ]
    .concat()
    .into();

    let witness_bytes = tx.input[0].witness.to_vec().iter().flatten().count();
    info!("Witness weight: {witness_bytes}");

    // let ret = bitvm::dry_run_taproot_input(&tx, 0, &prevouts[..]);
    // info!("Evaluator: dry run taproot input: {ret:?}");
    // assert!(ret.success);

    println!("Tx vsize = {} vbytes, weight = {}", tx.vsize(), tx.weight());
    // ,
    // let op_return = hex::decode("000b0b").unwrap();
    // TxOut {
    //     value: Amount::ZERO,
    //     script_pubkey: bitcoin::ScriptBuf::new_op_return::<&PushBytes>((&op_return[..]).try_into().unwrap()),
    // }

    let wallet_address = "bc1q2gw7nqj6q6040xm0yte95vzkv04x8fdz09mkpl".parse::<Address<NetworkUnchecked>>().unwrap().assume_checked();
    let mut child_tx = Transaction {
        version: Version::non_standard(3),
        lock_time: LockTime::ZERO,
        input: vec![TxIn { // p2a
            previous_output: OutPoint {
                txid: tx.txid(),
                vout: 0
            },
            ..Default::default()
        },
        TxIn { // input
            previous_output: OutPoint {
                txid: "7fcf7ae9574d5b1efe8fc3777d0f45ffb8f0599a65db52642460e2b97cf2d19b".parse().unwrap(),
                vout: 0
            },
            ..Default::default()
        }],
        output: 
            vec![TxOut {
                value: Amount::from_sat(23301),
                script_pubkey: wallet_address.script_pubkey(),
            }
        
        ],
    };
    let parent_vsize = tx.vsize();
    println!("Parent weight in vbytes: {}", parent_vsize);
    let child_vsize = child_tx.vsize();
    println!("Child weight in vbytes: {}", child_vsize);

    child_tx.output[0].value -= Amount::from_sat((parent_vsize + child_vsize) as u64 * 2 - (330-240));


    let raw_parent_tx = consensus::serialize(&tx);
    println!("Parent tx: {}", hex::encode(raw_parent_tx));
    println!("Parent txid: {}", tx.txid());
    println!("P2A script pubkey: {}", hex::encode(bitcoin::ScriptBuf::new_p2a().to_bytes()));
    let raw_child_tx = consensus::serialize(&child_tx);
    println!("Unfunded child tx: {}", hex::encode(raw_child_tx));


    info!("Evaluator: circuits...");
    let results = eval
        .evaluate_from(&out_dir, inputs, DEFAULT_CAPACITY, circuit_verify)
        .expect("consistency checks should pass for true inputs");

    // println!("ret: {ret:?}");

    results
}

mod taproot_tx {
    use std::str::FromStr;

    use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
    use ark_ff::{BigInteger, PrimeField};
    use ark_secp256k1::{Fr, Projective};
    pub use bitcoin::{
        self, Address, Amount, Network, ScriptBuf, TapSighash, TapSighashType, Transaction, TxIn,
        TxOut, Witness, XOnlyPublicKey,
        absolute::LockTime,
        hashes::Hash,
        key::{Secp256k1, UntweakedPublicKey},
        sighash::{Prevouts, ScriptPath, SighashCache},
        taproot::{LeafVersion, TaprootBuilder, TaprootSpendInfo},
        transaction::Version,
    };
    use bitcoin_script::script;
    use garbled_snark_verifier::{cac::adaptor_sigs::{AdaptorInfo, WideAdaptorInfo}, cut_and_choose::vsss::{self, rand_schnorr_sk}};
    use k256::{
        elliptic_curve::point::AffineCoordinates,
        schnorr::{Signature as KSig, SigningKey, VerifyingKey},
    };

    use super::*;

    pub(crate) fn unspendable_pubkey() -> UntweakedPublicKey {
        XOnlyPublicKey::from_str("50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0")
            .unwrap()
    }

    pub fn spend_info_from_script(script: ScriptBuf) -> TaprootSpendInfo {
        let secp = Secp256k1::new();

        TaprootBuilder::with_huffman_tree(vec![(1, script)])
            .unwrap()
            .finalize(&secp, unspendable_pubkey())
            .unwrap()
    }

    pub fn address_from_spend_info(spend_info: &TaprootSpendInfo, network: Network) -> Address {
        let secp = Secp256k1::new();
        Address::p2tr(
            &secp,
            spend_info.internal_key(),
            spend_info.merkle_root(),
            network,
        )
    }

    pub fn test_fail() {
        let tx: Transaction = consensus::deserialize(&hex::decode("030000000001019bd1f27cb9e260246452db659a59f0b8ff450f7d77c38ffe1e5b4d57e97acf7f0100000000ffffffff02f0000000000000000451024e730000000000000000046a020b0ba2406fe9b9c41965eca6bcc74499ef76a7b3b197c369fb23657d566b2a0f47d9943191eb6467ddb50b4193ae646d8b65595db6a2d81cadda7ade9530b32018052ddc407e0c32e85a7e8755bb1ec98813db048be148c7b29d185fa1fabec4d5c2c8ea0c9253a560b776ecd85da5120ef2c5ee7e7d7e9cd5944531a9a212351ec0c978ad402766ada3c14e31ff27f15c0bc6662a075e0d41758d7718335d8f93aa4a22d894419a42d4306db0cd9a3116c04492666b2b67eed0b75039f5f4532e59ce7d5227406f2fa1a5a34f762c01fba98b7e96c6c5427fac041a3e2c1891f79c401d114dcc75353ecbbbb1645562f43333e615ac9feeca5626fefd435501580640b1b8bf17407174cbe1c402ed0f18cb3e3380ae9d4d6aaec3f88c22ddb359144ecde9c75d675f52fef50620bd8f7dfecfb5ce41271668e0a193796d01969bcd186c46fc0186401d0f023111369662dd5d168da818d00c880989703156d40cf2615b15f53b8194ffa6607bbb87c9ef90613198d6c9f3cf7bfb61aaccf14b90c9703ae12bb2f0c44060d55f16639a07e22daff71f1479c0f6b75b1fa378c40f5ef55d764dec4abb1ed91888b23d49463b466e26fdba2411c347d82063fe7ec8c24307d302207c013b403f10e8176f39507c096351adc388c7f11cbd7c3a812d999367c23bd6825d42abac230da64453460f94db4228348869cfdd313fb1ea678f65021c65b3581280b44020568d9ca689cf86f17195b7feab42ab8aa694dbe82b9b6f6f69f7ef5afc8bc28b03a3991b98ac1440c5967388363593d98228af9d3bd3b3d2e1f4068ef3beb54047e486619d615e971d07a8d5f60115b2d374b5218649e3e5ade471e8b288c2f631911aa566ad7b53619acff7c30457197abe5c9c76ddcfa22355cdb672d12b2e40475c05ae94dcc4b17d60eb995be6c1c9474dd77a7689e3e5d0abb8c198739eda65316e6fc7dccc4c02dc6e7eebcee8fcaaed4f71beac9c8a930645351740ed77409da8afc41a4a2faf758bfc3a83f0b09aaf0a4bab9f4f917b81cfcb8845062f7e8e20f4cb7c210e60ff16666f4b96f40fb208a8369c23a8a476d4b535f7a941724067f6aec4532ffe5c15835e92d752f4713ceab3af2b1d476940044d3be2c53119314c483233845ab1c153a7afb820fffcd8aa117eb0c1299885e8e81949499558402e68d8a3195e8cd2406b8ef2dce6f1b94e477ba0f665e5fef5b87dc9562714f5c76aed357c192aeb88a10360234d228157f1e1f5d7f73bbd0778dec0e7d4b163402c12c977a95bb75ff4c407a14d001536936ed580bd619eaab7b8b85591ba39363f453527b02f2c93e3171b69d6c8b21ae66312eed403342dc36bf95790198ad4400a6217f9a594cb63869d84e778d42e659ef540b7307e1f6958d589015d6c254580c480447878313537058565a9249c0b7fb73046cc0aecde37acffe4c03743d640d77d57a84800f36d81f59aa8b81d2e28f440ee697000e1c7252d38c642202f5ef91a4791d928d302888ec8846608e4e6477e7c2986da1495c6fdf91aec3256ad4051523a70d5fa56bf31da839847f6401be6110f599716660e625e8c159ef0f9859c976a4a7a9d7db550ea1669b8edb1b8e187d4b5fa25019e900d789ebce37fcf408925d6cd8d5fad01aeabf23cf0c3540f86240c48468eeea18a75e5ea1f81dd51c23242eec7c3261ca924a8d44cf1dc8c5f2b055f74ea522862553b7a21f6f017406f528db0116251aef8139cb489fcf40fa5dc92b508afbb0be97d467edab1479427c602d66aec3b03af479ab9eec63530391312a75851e69edf14c254370d152a40a5991298b6b8d8267a2d8e86b4a15f18040c86c965a65938927f00a9961c5e3aeb6ab57b35338a337c687bbb849c8c3b1d258bfc8b483e09eb2bea634ac46a24403bc980d7e8fae9e07da31912c3d3285a369f2225ca54fc37a69f3816249e2be9910a4006313f5606f9f330b179161afb0c0b2265772f6bd670eca6ccc20653f2407445fd73e938aa505ead3e4424ead7e19efccd0a34baa960a4cffb0af74b4f8f42ea8876ddeb2c0384e98ea23065d70714c411e3391d232948970143a7d70721406d6cf9cfbdb5ec231ba34d500eb0132c20a619c14fac35bcc9d2f232166f7b60079510c30d193dc0ca8650e31a2fe5ed1e8115b5b28adfce9714f9cc57fffdea40155c8850d31b128bdba03f33e3f595cb67308302252886594196f51cfe1f88cae2b9c6278430ca7f07ddda14b118a496d70d439ce3673916265e817462e833f5408b15fe0280ff1c57d0c55f2528d2988a126e64c26b176bfc2c195f9aa47138625300c2deca46b264e0d8b0568c1123a580c49d73eddb74533b9a3c28af4ff387405b21f21829586b9eddd51fb8f509596796ee3fd6e9e55c7d699983d175c3fcd7fe87520cb58b4180398ba87c39788aafb291eb064bd8aa22a8d16374a572526a4074092b59f76c8dc3338b5c43e8bcc0ff1093c01ec71dda608f741c618e899f025939fa0004cdce2fdebc9ae514c771107030a07523d46d5ecab1d105a2674ad940e69ac31fe531098162b1f4fb20997d45a99e73e2c0e48bfa86cf2a4d9b330b9363e6315b663c15180d2654349d9007f88355a962d505a47cba2429b6d5b9a644403e64e97b566c638eadd21ae5936343772d798c9549d9378ed868693849ca871fcad3f151f43eaa705f20279ba3a92e161304f6b0a0e13ef5e567574e37b38af540aab64b3553d7837d35d6a4b2edcca660618ae1da39f134649e8abf55b2919bd545b3a50e20ac196d3b91512049800f31fb2742c5ed5bb20b2956c5f146e92f5e40ccc01eac12be9af64b8245db9f65852e380af323bac34b782530a8144da733d275d88fdb68a16a4592d0102816f470c40dc82ddfa916e237328aa6704e0c2bc14096cf20afa78abc1b0df6f80355491f43278abeb1de62d93f5d9ab3f29519d2a8388d2356e81a752ad3323cd5c52a1b9bedd9fcd633434bbed541734dc1ca98c94039c35a876a741beadc665e63402a259d171c9ae976430e7bb49ede5e217749451670347d9f0fce8f3cdb8a24eda15575ab30641ca6c494d662107acbc5eb8f7c405a30989ee64026f582fc66432990ec84aedc5ef981997c5876ee4820fd1d45fadb993dfadae6ff5b44755916dfa1d792d031ac533a9ed458036fd5624d5d118e40937bd395bcc70592a3fbbc2ae3cd4bd5de0194c3688fdbf5654bf00de3869edad113fe85ba17e0809ff6fe76bad1c990313443de32ad81ef7f63e2938207c91a4071f21af78256cc8c3bb9d040e4299441d6bbd3500a2f5f65fd37f275ecf613a458b611f93666ff5d069d101232977695043ccb979f50033a61f5602741ccbd8d400a0d59fa5354bb470019d83b5f3d9ae1e48f4916c10d648bbe89e0b4a30b30dfad2ab61bd313441eedb4446498fa66c9e010b8ec4605caef51958bf9b0e01e46404cc76659bd5e74d4b1b4a95c4ec49c776540af1e4b6b18578e18db29089cfbc36e23fe2ca51be165812ff46564527346241e0606e3a883da645ebb60417ec7ea40b999e494a0da82f43ce0009e2b7302949d68e609ff3adfcb0fd75fbb61c073f3e362862a659c2ecb8c6a4f4266973e0c3c2bac515c5a81925eda83b554954c4940331c985498811cca3f461ee161fad88f68ca911f4f8275cfb193132a60c2c80f6c39c4b05ee5c38670fff0e8898cde977ccb4a4a9a9206310ccd1b6f80cfd8d4401988b82832aa0d7ec60f8e1472d6f92dec9af5aa911930f06f478084d27e4e2ffd83d3888517147e49c7626c20d769acf0ef2cdbb045806e63b66aa31561bcfc406b8988e02b72017c46e0446d647abc9cb15f4712f5054f3ec0bc4f8c9d990f1aa5bbac9db24f4488e5b70066794f273ef700468dcd6392fdf9b1e4608c9a0afb407543b942f2aa66127fc52d96be8ae638de5b897af77045c99523721be5f649e8a949ae0dc1d26530f06b8301d66d4073b6329decc962927ac1a7557b8681629740ccf21e46e2fe796ec19eba8230ac9259804ba07ccb8e3fb12628bcb6d0b88160287c2f83d1f30003dae797e973ba5e7626d6728acb6d9c4cb8b6327c5b9dca68406a022297e57f7519806e53836e271512cc33a0d7967e0a170e918516f69c3dc0fafe62b98b0dddeeb791e352caa5692e825c321a45a174f635548cc067c21f1d40e352b9dc945b35c2656315fb9421e1245e910381081a1ee04612ad15a869d50676ac608364baa0693d33be6022a939a76506fb6f2283a345d550abfb5badf46440c77a030dd17e01f5480c3c9da8865f6ff799f6722439aaf100cf3e97de5ab78087a46e9c963e32657a09aec09e87dc682690eaf02cf45fd9f67cf30793718a664074f5d867fdfec8498c721496196204ae8eaa1cfdb9fe662a1b6907f05d8a3225c3d2bcda5f0779c55859898d258dff4a792f0c2ed6b02b849f39938ad1988ba6404197c08f42761dd25f6fc0c5ea3f9d12fe3f0321dea6d61cde4671e693310b9e4fbfa5c0db5daa663fd2200a08328d754588f5376d1744307d65a2f448de8c9040ea7edc4f8daa288918f81d19616a862cd2dcca16a7c84f0bb27578076d5db1475d10609964885da63dcfae475676f0a5c2d854b3f0fa2e1ed9b092543e72efeb405a49411fd5ca2a38a4221976c80c85d0cdae78d4b61a9a87ab76ecb5c067df8cc8df3370f0ec16bf1cb796a2f3119e06295eeb06b4111d91673a343296d0026f407f681b23abb67a3ea35b9eb08e95296ad2221e374310033954249b1ea6792f795ddab5b3b8a809ecfdcb0d8c8a232979d2df2f795f8bd7c1f51af46c6517183b40984b9b482d84c34e4095bd1f4ec26a35857728922dc61f3cb35bb9087007e6d8f19415a5642b5fc7a7d6bc60346ad6e8dc3fa6507d414b3a6f8699dc8a2cb4a6406f73a12ab21b6e9e81f003bb77b260acdff388211fd75c3609eeb2b6010802056089bca7cf5377b7dede8398e87e9a4f8de4b0d0afde16f477a2807f9c51016f40439c9e8a4faea27491bf2456224201f09b5d4470eed1d867c53ec90fd52ed2fc6648662c8e11180ede11accfac0637b7cdc86c7078260c38a828ad21b1b1f41e4081a54ef5b9e2e449d519f8a6a6e516379c03e062c811e3a9f429d38890e2bacab645252d74cc7542104852e6662215e3e3137b93d2c07dc135ea6d71b91e930a4054f4957021850ea0f47e3eef61cbe687abcdeff326ba7af037c60acb1320c3acf0b3bd3b3105740b3da2ea75c6aa3bfbaf86eaf9bb477a79b2623a58e5735e0340d171d737ef437400cbd1185ac3d758c131b13b50b72e9f8aed64fd60daebb9e83d05727d5a3a38cf0d09c88078ff32ea03bcc90d942c7b19908388de3eeed5b940a7f3c707ff3cd13531c3fa10465e85f09a32f1fbe7f05dfa393df1fb31319c9e271a884046abe740d256b17591cae0625deafdabab175fba6d29cfe4f9ac858e405c2ed11e5a1dffdd29e730bf93580bd9588981a9c2b59cb1cc39b409919f34c38dc2f893805523fe94b84cfa32a404b363f217ac3dc3288dde946fcf2dee441f40474185f25db33107962927b96aaa777e8b3f0ac0699e183e4a021d2850e97c40bdf647e9dc2a2710c4c8b7f734a950c8c125d2e15a3412bad32bc1596f55f91140275abda73e6ab4ec7dcb12f788c367e828d6a07248319fd49e9f1e6810ff713f0ca0bb2b7e3796ed732f252975e69c8b7615f455e8117f69c8f378ca25ebd21a40f2b8e3d982399203a401f58e75e2b480c0f9c024c76202ae506c16a8b842608d7a0cb5c9edded99fe4fa15d97d902e5b31108f5cfd84b00e8da7f2981701bba4405bd534eba794c7b0fcc94774245ee4e119c5971459731b680d104716d840c075489d6be09de731bb0ce5c6bf4473524abfce8244dfc055ecd7641f2a8b25d64740a9848218b053327ff52ad0db16999122f1baec4878d6523355245a8003c66e138b22ced54c863edd08a1ae629a39228127b1048006abccbad040bce39958fd7c4052ba721a839d14142344f836da1d73a766fb7746b4d871ee2abf92b7ae9cc9439aa1a7bdeb9c7db4c65c90264fe2bf0ba2d64a9611a3c7824943c12b96024ea94078793d7d48f10f0ec8c0ae11cf6e44a43b06d7a031a02eb7d9bde4a7c141d1bafcbd4583fa7143473d66217c9f38387a0f0b02102dc22e55bd0fcbbcb643706140fed7e84e95f2f658b65061b55907a477887ba82d2337a2e95fbadb419d154e0137997953f601ef6af3d614bd52546918c29fb3040a661e0e399530c89768dbc34068c20f3759203b6fab260ea5364d782719a648727046be672968c0646837092293625c55b7c13e0a726bb031bc1f3471244bbe5850d12244bd9c36894323e08e4022b0e5f0f0f09f0d3a03dcceaf9a1fe6f0ebb1773bf2eb2362c4640b81627bba58a0c86b2e68f103a1e34e4d5c3b332045c29a4d797a4cb11aa71a3c18865b29405123676ff1b64b33e96ddcefcd680f98d4d445e7f01494ecd86a17d0ced4f8dc52fa4166470e87cd07a5a35c3c3aba6804afbc1943bece13e4ffc213ff7cd0494044fe1983dc029b0c1e64bc9eac18092e120c98490873c4558cfc2eee437280e6cf093891b2870ef130ebfc853a3db00194113853387d7ef078bb551d1db47d4d40c76aa013bfcd003c4c6c9697994fe6c34eab56709c0f357df26ae88b613f5935810f7fd6f4435811ca36fd87c1ce13f565d3ab2bd75bd05c06a88802b0d14d50403f68c13967efefdaa82005ca199d6465fe4a6e6abd98b7b77b61c9f78f0b9b8fad1d41edf76a2c9d3725a3ab5238066ec25f01d1fc47fbccbafede505520cf5c40bc11ecf7d8e7fc25988ad11f27a815e1e4449b76900a147f3abda61d182893a16c00a828ca0f68e5d21e95c96aedc613c28d04bad00dfbafcea97271d66c94d64014b32173d800bfd286fb64aed1123fc0e8d33f0262ca473c800aa91b106270bd6f3fea74eebf2dce9b083d5ecd9df11d540d4680e39157d5428830e2d52dfe0940bab9c1685433b04d7ae6a04be824d61143c615bb72c3f92ade2ac05fa9a0378be580668beb422afd75bed2fadf7a40698c37bfac3a52d6259caabb5c240a0e8d40bda70687b8172d8ecfbc5439ad6679f74025aa134fe29f5cd2243f42a8affeebb47652c9929f9f6363c66da0c1459f51361426754956b24429ea2d18e9a6d76440ee4a8d652a6a4b8aab8a36ccbebd93e5bbaf04c7d73f7094090c006e6b81c12e72922b8510b37cd51d4642f7c239a4eb98a76b6c84a1046a92f1679fa1153ee840401f3f5f4f71030b64b076630996f4cb5232614e776414786a2f22f1fb52956b6705ac826316ce3db922a023c07e22961fe0acaf2c27ffaa74a7588e2e2f0e9c409901d2924392f0278eb9da9d4cb0492b7ffc75f472419bebfb6c3201a74a01e7e0f48cb9eddcc264f481ed89956951f9baed98b5bb63a26ff0b1c1de4ebf9d6740ebfa1df33d7e42c5ec5552e388af1301603e3001c0e9d1ddbffa5f46c87495fc6c1e3139b92657b3c23c89e74020024d403a49dec6cb91980923a98a9768552940788e9defa844fe29b7ad5615b56194abf9f6b3848194ac59dc6014d0528e0a24e67817f13520863b3c755372d1c3ef64cf8a26b381061232adb09e136156e8e6407fab1d3a99d070019dd567ef9587cf091d1b5059e34f6b797a3a5a419795e5bdbff652e551f04b67fd9ae388b432b435afba97cd1337c96d898fc41d6d0eef8d405bcc96dc10b69d2a4db211333e7ab0a70e89f0e10c3d07ba696774abf37797d9b5ec8844ace3662f20da8dde332e101f8db843a57b481286430ae702e4a1eaab40e93a37633f2e8ffa1f30a898a6eb08a97dce5b4263fdcf3856be4b86f548ac53a088259e29427f24feef5520182c4005d8ccb24b76e93403b52093934b11b94d400b7a16131ed9ca8d56e3cccabace566f09a36e30a57d59451727861547aede1ab171ce490c5ca83cd24b8684945bb626513176855108bae414604569ecf21190400367d3d51bb57bb2af8a3eb351f6b207f47008cc76c2affd94136fdc95284effe632f6efd127e0d6293b5225d5bfcf9453991f872bcd8c0c924342ed1695c91440daf887dfb07f6d2d5908739fcadd3213623c105a2f524c6fd29ea038c6df1befa8b2393bca2d4ca30102923239ffa15199b93d95eedc6f8f9887bb67ea8838cc4050d32c396136e0e85a19f7af424ef2ee5cd093a81ebfd42b5bb713d14f29d7e5ee6c253576a52a5b72fcab0dca8a2697f102889ed44fc4fab985bf5710ea5683400cc589559756df07fb1a34e1b9f05c9f27fa7c6ef4adb4a3f47978d67632319e3f0aecf18d01c00d92cd9b955c88e8a6c68f8953330c9f08c633b7218907ac6b40262d749de70f8e554db2aefb676e3b2fe50d1800b42e798b12cb697cc234673cc30d2eedc3930feea7fead132677a7a3884f7ceae7d9e13a4fb0935a72772699400d57678c810794b7c82ba128503cec360044b7b6a40b9885c07c1d9fa41ef0b221aecd40420f07aba75ec2c8b109f3b4ed8830cca827270a3ed3f4657c750ea940a2fb45c88e4f1e2687afc0e03476e59a27eeebf456b50c83fd543d64cb8b19297b1817d95740c149aaa6e070d4c5592eccf3776a9b5e38852c02f00eaa661f104046ab86f8faed085068224d4f0554b69b48086e8370708b831723378d66f2f2357da492afeaeda5810ba52418b115e012040ec0e672f2378e3eb78391cb61297540a2baafc26f0ab210b11a15b5eb1aebf274cb944921a541d970b50ff5332fd717c1c8a49b09a6b9e6ba19bed6a98290462e97d148d44a1e09a91149fcdf2bacd140d9284fe2b25c0ff31d684772233921fda891abe2768557171a768621f9d986902c8b325f3ec59fb0f5c4c31a57dcc8b89c8ea0464371f9f7544c6c5302e77b2c40f4d56bd51ed318582676ae05b147ce88b1c4b97873e89a0f772ae08389f01416860657479c8c5ae9135e1a4fdec85a84e641109c02518eef8444f64f31d16b92407126278c158957365c05dba15dc509db733e314a85fcb966fe4ec662123246fac44771e7e3ff70ee1b8d4869cc47064b1d3350264c615d473f4c7ec95d9d382840f5e719772dda24fc5729920bde6c69676f511c1e67f5e565fc794b4774e4ad85b8e0edaaf4235a4e0ef3a0c34ec281ef05fee69f5f43064b777de36cd99b353940af21e8ee70c10a5ee42250e277fb5db6f843cc1faae5b8ffb871577d0a2ed504e5a3135f4f7874a211e339a536d39a847b5e022bc184a1bcf82709cbba48cda0409e1a1c883bde0439f493afbed7fda0a09ed5b01ad7cfc6693a1710b66569ba5eff13b9fe3bb14f54e349b2c79f04a7cc541e3c0593d74aaf5f04a03d6201ba774006ae6bcc051796fb5afee0aa8d6a0852f0be357a05cc61daf0f85dec56adb83aec8f39f0e4d30b939174bc336dbfb674c6a0b2e2bcea89617be2223d60468009401f92069d28804c320c519f6e253594a589c487aed2a604540020f1adbe88fee3478f32b7f3e6f190e8fa6475a027094497ce35dc4d92805a8b6077c0a6f4b3d34085d440cb1d6182e22e23ac169b9acfcbcc62ff544deb61b35ea6bcfc34c5055bfcc82c5f57763783ce57ea53634ad1ff40db3f13bdfd0e83f4be225ee38e918f4021eb83f7d5119f477b2fb3ed63c175299b4c789495b62e2725b51a0e24e11854f42fec41c54e726853ee4dfe19b7cee01874b919c55e5ed3e9834ed39ff9280140efca69f4e5d590949cf503c8865e410ae0394510b82ef7d5c13b198c4672fb8edddad7b39f58ef4508b2c9601867bf021491dc0d118603d3adc2c98f2828875540ecbf6a2299268314e8d5dd751e5db11d27c90a628ce3f8514a197f3d8ab10393b1ea79c4dbb15f3ab848936fe0af3ee123deb520bf00edadbd81d62fdc45523f40c14c5d5f625dd1050c574a6533dc28c81ffc3b483cf0037ef37ca481f8e4fe0a28a4d40adc446ff13bd674abd63f345e58b340034af66cb1f9cc6758b4a2873540358ec2577f5114f6f58768baf0d4d6823d3015989d23a26b2872829e4fe31de36ec6ad4510624bf0954cb887fac6263a2c5382d04872775c8be39830d74b248f409cd09098b94455870a54a8584f6c4d42ca4d9e87e7a20839a5c4a0fa3d155c331b91a26a326ddd5b29c2938da868fe135890cf220b619fa0f066af46563eb153406e47e64db74b29db42be78196a16883127ff7515f95e88a3ea2690b0000b930c46f7f6c62bdbe24e37b14c7b1acac670ae4263f894d5a7c8e694970c0a7560e84060fd5cabf72eee190dc3af91e6d261afd8860d322d746a2ae31928a8d13a56a18817872437245b15dc82700f475e5fffb129a1c0c1f3de569e0be834edf8ad124093d7a494d4c5b4fa253cb33421ea2e9aa27316f0ca44a16ac7c4cbb192bccb47055795f60e73088f450c6e335f63460ecf31558295024687c5ef76dcd83fbeef40fc2f4353478d5265e766e416899a7ff74e4a74b440fe91cdf37e32d3c4362146a161434a86f30e07d69ffa385f009755008596ae1b70ba17cb3839eab03fcf37407c2c2be3c83acea34b65f69cc0b0f74b246ad8cca91d9d4df5cb41a8b5ac52be2fc97ded0394c878d3c25cd942056944be0e21576c68e9269627092a3fb580b340bdeef27566a822e742293a5203628f8908fe5e664bf4704483289c657422ed9ad3b639f9c44ef27cf54b0a74ca05deb86b57c6092e842a42540137c9c8b7e43440d069882d116aaca95f09b68646a2b9b34db258a3341f2e4b33d234c632eb6438aab430681a0c3d13a1b835128d9ae37f8bc205e23dc76d70b67ff5ae79fa785e40c1a8f92290957b3134aca85b723c4857ee2b9d9521de7731404ed8b1e25cd337b9a4973ee2487694f95d298e2a2cf96db9cc9a836d91ace4789791d47f7858a34058cd50980693359588870bacbcba957e4add18b9421aa145410479a0126b396dba9caf63ea9c38b97dabb11b4d37dc9b331e5f30e0cb042ce32b63285f5a37a4406506fb3b7eca5ded46f14b75871edebbbbd0c85ffc23089b1774f23fcfb99c8e1a99ec309f4a64ce7eff588968238ef0b7d8008a80f999718565b2801e607e51407d6cff8c9f76d56c08b24993c0f4ec1a5787c91197c27d52cca7666e433950fe74214c08a2432db636aee57e7c46feb8508655508aad58a574ff54b3b33cdb0a403fcc354531d6f78a633a161babfb7aafda7b5cd75b9078561b360f8ae58d1483fb9aed1dfaea3c9e340df8d808c0e4a6547e49edd6ce875ee6978690e86734054093f7add91efb7ad7ee5c148e6f7ca20e3fa936f91b549b54d152c2f34111b7ceb1f54503424aae2563b58ced42eec41126f3e3850fe9be3a1fe347abd485660a407f174df554937db61a2597e5c3596fd037ce7b07634a94189946ca7838eefa286a1358ff1a358b11799821fffd8ce2c60d5499e2593df08b63fa85b9753a1bc840e0d0299b563d092db2426e975b3f0f61337fa40be3034aee4ed33af95f38d6297584e5622f75f5795108218a6ffe7308713aef3af225f23e9d0c2fcfe16c56b940d94962406510ecb3b4199c0203b52628bc150b943aacc0f21f3d4d1830c199abe8fa710e342c3b76f0645971c40ba158ea740574a04b2cecae59c9715761b20e408ed522bf49334c4c3f608f00adbd0ad7cfb4a1fa735dc4d4b9d50d34d3a73d321c908e2ab2f2cfba59a2959612ae89b0c2ba812630923303de100cfe6c942b6240f40ead39112b754b48627db3ee9b7b0489f32b681b6b46d1e0ff5eac47c38c6e90afdb0af7405d88335cd0d00944b4028ccdcccb4ffc36cb5e6ed461ad9ac7ac40fb9fbca12bda6db5c792f157b07f8101a2c1d2a1fb3d62572dfd1640f6fae1d53ab51a46fb4055e5d120a3ac882b196293d09d1e97b2b85d7e5b8164e3e16f8d4059d56051a28cba65993781cddb1b73084c66c63f768a69743b9755bace35d1bc8eedeef25bffe26221c2a639539b14aeca3c3cfd1c9b986e6166e64d6841253c40d551fbd054fc3948b56d83418c18d04510fb5c4d935fa73770bee459b2b51e53424c9961733b48a1815d1374dc8b61550513fddc330baabbf4e6b2765aa05f3140186f1637cf3442460c13a2bc4b6869853d930ef676325eadd5a03b22e042a554f6dfa124f5a9d2552cd908ae1cdea3570bb22feb6648532f14ebf58821351170408362c31f09c994dc5e86633a4c15b200e7356a1bf777e9999c7e955bb6923d0f6b2a1c4cb2dc63981b64c6b01e40dd322aed743d8b5b6ffce66b99ac85628fc1404a0af5d3c37d3e23151eccd70b9eef4c012777b959607d965fe313d91e04a48dac28e59331c0cb69c6aded264d54cfc61f40f98efcb85ae359131bc0439502cf4017c95d04e3a6565ed072d4e070e854e6685dcec80c3a059c1b6c2f5975d80e63ac99142b5af28c272b1eec899bd3975b6bd54ee5ea06c2dba02cd62f60fd9319404acdbda1906396ca8fd7b6a6260fabe02ae68046bfe3cd546cc61a76b2879eb3ff9f7ea3f7d2f6cc0cb700d0cbda3eea9bc5a9dc06014e546ef1562a1fdb6988403c11e629b453c6ae0df5bdbcd91b343f2b7886734433c2cace51868bdfc391fe82c2d3a6c375bdea2275677e2688662de653214b4041f5a45204a3d5bfc2ecbe40abcaf5a3f6cb87ab54043c97d0099056567b95fd3897f62057c74ad73832c863d265526dd155f0e8491a46e0f353ba75c588fba1c9a6cffaf6fef09319bfbcfb40775c114dcc6bf77cc02cca4160eda4dbb9a48294cc225928648b36ded0e383a250f9a8d11f886d6113c395e0be4132509f5966871e500863266a567886079847409e03afc1c88411d704db310087ba9d0db2f0b986599322df6c2bc8dcf0226e5b43e367cbe56ef0a06f105f27384dec5fdff1c8d9883d0e28f5788163c854985340575fd9f47389a19ef4beecfa8f1582a754a5f7bca301f6af3cf11639a2cb11f8843d0780da255158d35e79a6150afb84807026ceceea8addbd5f7e3628daacd8408504e1c8e7feada15f821707a13caffffe13d541e7e4b5ea2fdb84206921900d6544a293899e069d8b9e7a5f80697ce331014efdf2709fa38f53a219cb9a9ab84038fd24d863400e0521b16725ca55dc194c3bc39ee5f8104c79749094f461408e4829f2e3fcb4d3477ee25c9cb1896e89255b86cdf4cf772ee0c9d73e59246bf940092095ec9c2c9125cd0c045a59bb39089b60b17f4052e0d31b9a30b98a5ef0d0616c5dd866012983699f1c39d8823dfd5a5f3dd962a5a005bbcc3d681cc082eb40c9e29948cd2f365d08a23d4d8402c77748fef7296f32dbaced57ba06d893a66a6161682f12624ea9216509c1a57b8b8fdd7b8519e3e47108a5fc3772e42f33be40ad06965829a7e749c916c5e5ffddfdb8884a7b0790f5de93717957e0e13f9e374ebfbcd2e1b6c4fea99fc97524fefbbc6dd700411703e271fd29cfe8d26844694040c3ee568c4c2afffa8e45c827f87f6409d837358590736c1fbb4bd1c413432ae07729d28e01172e95d889a90ddf2c438ef79b3ed6207c688493ae9ef49d0463402303bf48d32173e04795a118902e7663a96f414f3c6ffcdfa05602f8eef6ebc9845d7578c15d1759b8fa6fc5f8b3449cb23482c1968d4c13b9734b76c61d68ea408ed9e8b038d4174556fa4668ba376d5c113e02419108d8392e59703616a0b2823785c70608b8b9cb0abe4bd3747fedd95be65d205486595b0bac5845595f40f840236eedd6e84822528c4c9ce49b7b36dfe009841f8a7991dadf7fad7e24faaa0a65c03fd31ae1dc59665289d6fc1abc20622369248bc0b143cdfc035ebdab49b940de7b69fe9bb35f4de04934b838508f7faf7fe8b22c0d37cae958c38fd56b8ca2c986e9c9dc3272e2ea0e747bfbd6dc2080f1a9360db234615acedd82172d1ccd4089b1cb0ff375b31ce171fa7334c867205c6d087e939f7635772be3e2ad7401c80c4b8153330e12a9608a875d2a9033ded9183eeed7ec857ad2e44077b010aaf8400b427027330acedb6837c0443402fb93a6f1e2d4a74634c4c43098185cd55c429f9ed69798fad312d8e1a65684517c3a1f31e1623c744e3266d2d06f77c079cc40fd30e1d7c056f41dd1d739a1f4c47db0b94546c40e9c599bbea082604981afa24112b26e7a6e99eaaefb8845981a03a5613c190bb67477d7ed10e19a48e3e5a640ac869cc3d4321705d5e505fb804bae496cfb2266ff98acbf96f9c0dd21203577460b3946bad97583ed0966654de0905a7fecdb2d82947f0a86677049197a3e4040e85507027df8f48c20fc6c55ae754f65be94ece63ec77a68d190c23f27be066787a9dd32cffab892f86bc49b471004c79d0b63cabafbaacfd6bc467185e6efd140b9efe2b97b52aee18a62764f3ff15cca30255af1a8cb959a37e04eb4bf6d1cfe70bbee42f253cf40b15f81dfead0db93702b3529f9477ab8e0158ebca98a0f7c40e917ddc1871172016bcf2bdc0f003e71cf8b406d4f4a064e1d604af808df4d01ae0e9568f666fb7de80f2bb31e84507b979c6b17acfe0bcf67010e04ccc47ae2fdff0120879c8e72ed8526708f795ddb356273d1e26accc969e8f0b294ff817d88d3e2eb7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadab7dadabac21c150929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac000000000").unwrap()).unwrap();

        let prevouts = vec![TxOut {
            value: Amount::from_sat(330),
            script_pubkey: ScriptBuf::from_bytes(hex::decode("5120fe08bd466713fb1af3cd4be99453bb6179d1d970e607ec58b25fc164356605d2").unwrap()),
        }];

        let ret = bitvm::dry_run_taproot_input(&tx, 0, &prevouts[..]);
        info!("Evaluator: dry run taproot input: {ret:?}");
        assert!(ret.success);
    }
    pub fn test_wide() {
        let num_inputs = 16;

        let total = 4;
        let to_finalize = 2;
        let mut rng = rand::thread_rng();
        use garbled_snark_verifier::cac::vsss::Polynomial;

        let secp = garbled_snark_verifier::cac::vsss::Secp256k1::new();
        let polynomials = (0..num_inputs)
            .chunks(8)
            .into_iter()
            .flat_map(|chunk| {
                let num_bits = chunk.count();
                let num_labels = 2u32.pow(num_bits as u32);
                (0..num_labels)
                    .map(|_| Polynomial::rand(&mut rng, total - to_finalize))
                    .collect_vec()
            })
            .collect_vec();

        let shares = polynomials
            .iter()
            .map(|polynomial| {
                polynomial
                    .shares(total)
                    .into_iter()
                    .map(|(_, share)| share)
                    .collect_vec()
            })
            .collect_vec();

        let (share_commits, polynomial_commits): (Vec<_>, Vec<_>) = polynomials
            .iter()
            .map(|polynomial| {
                let share_commits = polynomial.share_commits(&secp, total).to_canonical();
                let polynomial_commits = polynomial.coefficient_commits(&secp).to_canonical();
                (share_commits, polynomial_commits)
            })
            .unzip();

        let num_sigs = share_commits.len().div_ceil(256);
        let secret = rand_schnorr_sk(&mut rng);
        let script = taproot_tx::script_for(secret, num_sigs);
        let mut tx = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn::default()],
            output: vec![TxOut {
                value: Amount::from_sat(2000),
                script_pubkey: bitcoin::ScriptBuf::new_p2a(),
            }],
        };
        let spend_info = spend_info_from_script(script.clone());
        let address = address_from_spend_info(&spend_info, Network::Bitcoin);
        let prevouts = vec![TxOut {
            value: Amount::from_sat(2000),
            script_pubkey: address.script_pubkey(),
        }];
        let sighashes = taproot_tx::sighashes(&tx, &prevouts, &script, num_sigs);

        let evaluator_adaptor_sigs =
            EvaluatorAdaptorSigs::new(&mut rng, secret, &[0], &share_commits, &sighashes);

        let wire_values = (0..num_inputs).map(|i| true).collect_vec();
        let wide_labels = shares.iter().map(|share| share[0]).collect_vec();
        let signatures = wide_labels
            .chunks(256)
            .zip(wire_values.chunks(8))
            .map(|(wide_labels, bit_vals)| {
                let wide_label_idx = bit_vals.iter().fold(0, |acc, &val| acc * 2 + val as u8);
                wide_labels[wide_label_idx as usize]
            })
            .zip_eq(evaluator_adaptor_sigs.adaptor_sigs.iter())
            .map(|(wide_label, adaptor_sig)| adaptor_sig.garbler_signature(&wide_label))
            .collect::<Result<Vec<_>, _>>()
            .expect("adaptor sigs should be valid");

        let control_block = spend_info
            .control_block(&(script.clone(), LeafVersion::TapScript))
            .unwrap()
            .serialize();

        assert!(signatures.len() == num_sigs);
        tx.input[0].witness = [
            signatures
                .iter()
                .cloned()
                .map(|x| x.to_vec())
                .rev()
                .collect::<Vec<_>>(),
            vec![script.to_bytes(), control_block.clone()],
        ]
        .concat()
        .into();

        let ret = bitvm::dry_run_taproot_input(&tx, 0, &prevouts[..]);
        info!("Evaluator: dry run taproot input: {ret:?}");
        assert!(ret.success);
    }

    pub fn test_wide2() {
        let num_sigs = 2;

        let mut rng = rand::thread_rng();

        let secp = garbled_snark_verifier::cac::vsss::Secp256k1::new();

        let num_vals = 256*num_sigs;
        let wide_labels = (0..num_vals).map(|_|  Fr::rand(&mut rng)).collect_vec();
        let label_commits = secp.generator_batch_mul(&wide_labels);
    

        let evaluator_secret = rand_schnorr_sk(&mut rng);
        let script = taproot_tx::script_for(evaluator_secret, num_sigs);
        let mut tx = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn::default()],
            output: vec![TxOut {
                value: Amount::from_sat(2000),
                script_pubkey: bitcoin::ScriptBuf::new_p2a(),
            }],
        };
        let spend_info = spend_info_from_script(script.clone());
        let address = address_from_spend_info(&spend_info, Network::Bitcoin);
        let prevouts = vec![TxOut {
            value: Amount::from_sat(2000),
            script_pubkey: address.script_pubkey(),
        }];
        let sighashes = taproot_tx::sighashes(&tx, &prevouts, &script, num_sigs);

        // let evaluator_secret = Fr::rand(&mut rng);
        let wide_adaptor_infos = label_commits.chunks(256).zip_eq(sighashes).map(|(commits, sighash)| 
            WideAdaptorInfo::new(&evaluator_secret, &commits, &sighash, &mut rng))
            .collect_vec();
        

        
        let signatures = wide_labels.chunks(256).zip_eq(wide_adaptor_infos.iter()).map(|(wide_labels, info)|
         info.garbler_signature(&wide_labels[0]).unwrap()).collect_vec();

        let control_block = spend_info
            .control_block(&(script.clone(), LeafVersion::TapScript))
            .unwrap()
            .serialize();

        assert!(signatures.len() == num_sigs);
        tx.input[0].witness = [
            signatures
                .iter()
                .cloned()
                .map(|x| x.to_vec())
                .rev()
                .collect::<Vec<_>>(),
            vec![script.to_bytes(), control_block.clone()],
        ]
        .concat()
        .into();

        let ret = bitvm::dry_run_taproot_input(&tx, 0, &prevouts[..]);
        info!("Evaluator: dry run taproot input: {ret:?}");
        assert!(ret.success);
    }

    pub fn test_narrow() {
        let num_sigs = 3;

        let mut rng = rand::thread_rng();

        let secp = garbled_snark_verifier::cac::vsss::Secp256k1::new();

        let num_vals = num_sigs;
        let garbler_secrets = (0..num_vals).map(|_|  Fr::rand(&mut rng)).collect_vec();
        let garbler_commits = secp.generator_batch_mul(&garbler_secrets);
    
        fn rand_schnorr(rng: &mut impl Rng) -> Fr {
            let ret = loop {
                let ret = Fr::rand(rng);
                if !ret.into_bigint().is_zero() {
                    break ret;
                }
            };
            let is_odd = (Projective::generator() * ret)
            .into_affine()
                .y
                .into_bigint()
                .is_odd();

            if is_odd {
                -ret
            } else {
                ret
            }
        }
        // let evaluator_secret = Fr::from_be_bytes_mod_order(&SigningKey::random(&mut rand::thread_rng()).to_bytes());
        // let evaluator_secret = Fr::rand(&mut rng);
        // let evaluator_secret = Fr::from_be_bytes_mod_order(&evaluator_secret.into_bigint().to_bytes_be());
        let evaluator_secret = rand_schnorr(&mut rng);

        SigningKey::from_bytes(&evaluator_secret.into_bigint().to_bytes_be()).unwrap();
        let script = taproot_tx::script_for(evaluator_secret, num_sigs);
        let mut tx = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn::default()],
            output: vec![TxOut {
                value: Amount::from_sat(2000),
                script_pubkey: bitcoin::ScriptBuf::new_p2a(),
            }],
        };
        let spend_info = spend_info_from_script(script.clone());
        let address = address_from_spend_info(&spend_info, Network::Bitcoin);
        let prevouts = vec![TxOut {
            value: Amount::from_sat(2000),
            script_pubkey: address.script_pubkey(),
        }];
        let sighashes = taproot_tx::sighashes(&tx, &prevouts, &script, num_sigs);
        let adaptor_infos = garbler_commits.iter().zip_eq(sighashes).map(|(commit, sighash)| 
            AdaptorInfo::new(&evaluator_secret, commit.clone(), &sighash, &mut rng))
            .collect_vec();
        

        
        let signatures = garbler_secrets.iter().zip_eq(adaptor_infos.iter()).map(|(garbler_secret, info)|
         info.garbler_signature(garbler_secret)).collect_vec();

        let control_block = spend_info
            .control_block(&(script.clone(), LeafVersion::TapScript))
            .unwrap()
            .serialize();

        assert!(signatures.len() == num_sigs);
        tx.input[0].witness = [
            signatures
                .iter()
                .cloned()
                .map(|x| x.to_vec())
                .rev()
                .collect::<Vec<_>>(),
            vec![script.to_bytes(), control_block.clone()],
        ]
        .concat()
        .into();

        let ret = bitvm::dry_run_taproot_input(&tx, 0, &prevouts[..]);
        info!("Evaluator: dry run taproot input: {ret:?}");
        assert!(ret.success);
    }


    #[test]
    fn test_tx() {
        let evaluator_privkey = SigningKey::random(&mut rand::thread_rng());
        let evaluator_pubkey = evaluator_privkey.verifying_key().as_affine().x().to_vec();
        let mut rng = rand::thread_rng();
        let evaluator_secret_fr = {
            let b = evaluator_privkey.to_bytes();
            fr_from_be_bytes_mod_order(b.as_slice())
        };
        let garbler_secret_fr = Fr::rand(&mut rng);
        let garbler_commit = Projective::generator() * garbler_secret_fr;

        let script = script! {
            { evaluator_pubkey }
            OP_CHECKSIG
        }
        .compile();

        let spend_info = spend_info_from_script(script.clone());
        let address = address_from_spend_info(&spend_info, Network::Bitcoin);
        let mut tx = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn::default()],
            output: vec![TxOut {
                value: Amount::from_sat(2000),
                script_pubkey: bitcoin::address.script_pubkey(),
            }],
        };

        // Provide a concrete prevout matching the spend script to compute taproot sighash
        let prevouts = vec![TxOut {
            value: Amount::from_sat(2000),
            script_pubkey: address.script_pubkey(),
        }];
        let mut sighash_cache = SighashCache::new(&tx);

        let sighash = sighash_cache
            .taproot_script_spend_signature_hash(
                0,
                &Prevouts::All(&prevouts),
                ScriptPath::with_defaults(script.as_script()),
                TapSighashType::Default,
            )
            .unwrap()
            .to_byte_array()
            .to_vec();

        let adaptor = AdaptorInfo::new(
            &evaluator_secret_fr,
            garbler_commit,
            sighash.as_slice(),
            &mut rng,
        );

        let garbler_sig_bytes = adaptor.garbler_signature(&garbler_secret_fr);
        // Verify using k256 in test only
        let verifying_key: VerifyingKey = *evaluator_privkey.verifying_key();
        let ksig = KSig::try_from(garbler_sig_bytes.as_slice()).expect("valid sig");
        verifying_key
            .verify_raw(sighash.as_slice(), &ksig)
            .expect("signature should be valid");

        let secret = adaptor
            .extract_secret(&garbler_sig_bytes)
            .expect("secret should be extracted");
        assert_eq!(secret, garbler_secret_fr);

        let control_block = spend_info
            .control_block(&(script.clone(), LeafVersion::TapScript))
            .unwrap()
            .serialize();

        let witness: Witness =
            vec![garbler_sig_bytes.to_vec(), script.to_bytes(), control_block].into();

        tx.input[0].witness = witness;

        let res = bitvm::dry_run_taproot_input(&tx, 0, &prevouts[..]);
        assert!(res.success);
    }

    pub fn script_for(secret: Fr, num_sigs: usize) -> ScriptBuf {
        let pubkey = Projective::generator() * secret;
        let pubkey_bytes = pubkey
            .into_affine()
            .x()
            .unwrap()
            .into_bigint()
            .to_bytes_be();

        script! {
            { pubkey_bytes }

            for _ in 0..num_sigs - 1 {
                OP_TUCK
                OP_CHECKSIGVERIFY
                OP_CODESEPARATOR
            }

            OP_CHECKSIG
        }
        .compile()
    }

    pub fn sighashes(
        tx: &Transaction,
        prevouts: &[TxOut],
        script: &ScriptBuf,
        num_sigs: usize,
    ) -> Vec<Vec<u8>> {
        let mut sighash_cache = SighashCache::new(tx);

        (0..num_sigs as u32)
            .map(|i| {
                let mut enc = TapSighash::engine();

                sighash_cache
                    .taproot_encode_signing_data_to(
                        &mut enc,
                        0,
                        &Prevouts::All(&prevouts),
                        None,
                        Some((
                            ScriptPath::with_defaults(script.as_script()).into(),
                            if i == 0 { 0xFFFFFFFF } else { 3 * i },
                        )),
                        TapSighashType::Default,
                    )
                    .unwrap();
                TapSighash::from_engine(enc).to_byte_array().to_vec()
            })
            .collect_vec()
    }

    // #[test]
    fn test_tx_multiple_sigs() {
        let evaluator_privkey = SigningKey::random(&mut rand::thread_rng());
        let evaluator_pubkey = evaluator_privkey.verifying_key().as_affine().x().to_vec();
        let mut rng = rand::thread_rng();

        let num_sigs = 3;

        // assumes num_sigs >= 2
        let script = script! {
            { evaluator_pubkey.clone() }

            for _ in 0..num_sigs - 1 {
                OP_TUCK
                OP_CHECKSIGVERIFY
                OP_CODESEPARATOR
            }

            OP_CHECKSIG
        }
        .compile();

        let spend_info = spend_info_from_script(script.clone());
        let address = address_from_spend_info(&spend_info, Network::Bitcoin);
        let mut tx = Transaction {
            version: Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn::default()],
            output: vec![TxOut {
                value: Amount::from_sat(2000),
                script_pubkey: address.script_pubkey(),
            }],
        };

        // Provide a concrete prevout matching the spend script to compute taproot sighash
        let prevouts = vec![TxOut {
            value: Amount::from_sat(2000),
            script_pubkey: address.script_pubkey(),
        }];
        let mut sighash_cache = SighashCache::new(&tx);

        let sigs = (0..num_sigs)
            .map(|i| {
                let evaluator_secret_fr = Fr::rand(&mut rng);

                let garbler_secret_fr = Fr::rand(&mut rng);
                let garbler_commit = Projective::generator() * garbler_secret_fr;

                let mut enc = TapSighash::engine();
                sighash_cache
                    .taproot_encode_signing_data_to(
                        &mut enc,
                        0,
                        &Prevouts::All(&prevouts),
                        None,
                        Some((
                            ScriptPath::with_defaults(script.as_script()).into(),
                            if i == 0 { 0xFFFFFFFF } else { 3 * i + 32 },
                        )),
                        TapSighashType::Default,
                    )
                    .unwrap();
                let sighash = TapSighash::from_engine(enc).to_byte_array().to_vec();

                let adaptor = AdaptorInfo::new(
                    &evaluator_secret_fr,
                    garbler_commit,
                    sighash.as_slice(),
                    &mut rng,
                );

                let garbler_sig_bytes = adaptor.garbler_signature(&garbler_secret_fr);
                // Verify using k256 in test only
                let verifying_key: VerifyingKey = *evaluator_privkey.verifying_key();
                let ksig = KSig::try_from(garbler_sig_bytes.as_slice()).expect("valid sig");
                verifying_key
                    .verify_raw(sighash.as_slice(), &ksig)
                    .expect("signature should be valid");

                let secret = adaptor
                    .extract_secret(&garbler_sig_bytes)
                    .expect("secret should be extracted");
                assert_eq!(secret, garbler_secret_fr);
                garbler_sig_bytes.to_vec()
            })
            .collect::<Vec<_>>();

        let control_block = spend_info
            .control_block(&(script.clone(), LeafVersion::TapScript))
            .unwrap()
            .serialize();

        tx.input[0].witness = [
            sigs.iter().cloned().rev().collect::<Vec<_>>(),
            vec![script.to_bytes(), control_block.clone()],
        ]
        .concat()
        .into();
        assert!(bitvm::dry_run_taproot_input(&tx, 0, &prevouts[..]).success);

        // Test with different order of sigs: should fail
        tx.input[0].witness = [
            sigs.to_vec(),
            vec![script.to_bytes(), control_block.clone()],
        ]
        .concat()
        .into();

        // println

        assert!(!bitvm::dry_run_taproot_input(&tx, 0, &prevouts[..]).success);
    }
}
