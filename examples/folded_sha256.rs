//! Demonstrates folding SHA-256 compression steps with NeutronNova.
//!
//! Run with: `RUST_LOG=info cargo run --release --example folded_sha256`

use bellpepper::gadgets::{
  boolean::{AllocatedBit, Boolean},
  sha256::sha256_compression_function,
  uint32::UInt32,
};
use bellpepper_core::{
  ConstraintSystem, SynthesisError,
  num::{AllocatedNum, Num},
};
use ff::PrimeField;
use sha2::{Digest, Sha256};
use spartan2::{
  neutronnova_zk::NeutronNovaZkSNARK,
  provider::T256HyraxEngine,
  traits::{Engine, circuit::SpartanCircuit},
};
use std::{convert::TryInto, fmt::Write as _};
use tracing_subscriber::EnvFilter;

const BLOCK_SIZE: usize = 64;

fn rotr(x: u32, n: u32) -> u32 {
  x.rotate_right(n)
}

pub fn sha256_compress(state: [u32; 8], block: &[u8; BLOCK_SIZE]) -> [u32; 8] {
  const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
  ];

  let mut w = [0u32; 64];

  for i in 0..16 {
    w[i] = u32::from_be_bytes(block[i * 4..i * 4 + 4].try_into().unwrap());
  }

  for i in 16..64 {
    let s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
    let s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
    w[i] = w[i - 16]
      .wrapping_add(s0)
      .wrapping_add(w[i - 7])
      .wrapping_add(s1);
  }

  let mut a = state[0];
  let mut b = state[1];
  let mut c = state[2];
  let mut d = state[3];
  let mut e = state[4];
  let mut f = state[5];
  let mut g = state[6];
  let mut h = state[7];

  for i in 0..64 {
    let s1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
    let ch = (e & f) ^ ((!e) & g);
    let temp1 = h
      .wrapping_add(s1)
      .wrapping_add(ch)
      .wrapping_add(K[i])
      .wrapping_add(w[i]);

    let s0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
    let maj = (a & b) ^ (a & c) ^ (b & c);
    let temp2 = s0.wrapping_add(maj);

    h = g;
    g = f;
    f = e;
    e = d.wrapping_add(temp1);
    d = c;
    c = b;
    b = a;
    a = temp1.wrapping_add(temp2);
  }

  [
    state[0].wrapping_add(a),
    state[1].wrapping_add(b),
    state[2].wrapping_add(c),
    state[3].wrapping_add(d),
    state[4].wrapping_add(e),
    state[5].wrapping_add(f),
    state[6].wrapping_add(g),
    state[7].wrapping_add(h),
  ]
}

type E = T256HyraxEngine;

const SHA256_IV: [u32; 8] = [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

fn scalar_from_u32<F: PrimeField>(value: u32) -> F {
  F::from(value as u64)
}
fn scalar_to_u32<F: PrimeField>(scalar: &F) -> u32 {
  let bytes = scalar.to_repr();
  u32::from_le_bytes(bytes.as_ref()[..4].try_into().unwrap())
}

fn pack_uint32_equals_public<Scalar, CS>(
  cs: &mut CS,
  word: &UInt32,
  public: &AllocatedNum<Scalar>,
  label: &str,
) -> Result<(), SynthesisError>
where
  Scalar: PrimeField,
  CS: ConstraintSystem<Scalar>,
{
  let mut packed = Num::<Scalar>::zero();
  let mut coeff = Scalar::ONE;
  for bit in word.clone().into_bits() {
    packed = packed.add_bool_with_coeff(CS::one(), &bit, coeff);
    coeff = coeff + coeff;
  }

  cs.enforce(
    || format!("{label}_packing"),
    |_| packed.lc(Scalar::ONE),
    |lc| lc + CS::one(),
    |lc| lc + public.get_variable(),
  );

  Ok(())
}

#[derive(Clone, Debug)]
struct Sha256StepCircuit {
  previous_state: [u32; 8],
  block: [u8; 64],
  next_state: [u32; 8],
}

impl Sha256StepCircuit {
  fn new(previous_state: [u32; 8], block: [u8; 64], next_state: [u32; 8]) -> Self {
    Self {
      previous_state,
      block,
      next_state,
    }
  }
}

impl SpartanCircuit<E> for Sha256StepCircuit {
  fn public_values(&self) -> Result<Vec<<E as Engine>::Scalar>, SynthesisError> {
    Ok(
      self
        .previous_state
        .iter()
        .chain(self.next_state.iter())
        .map(|&word| scalar_from_u32::<<E as Engine>::Scalar>(word))
        .collect(),
    )
  }

  fn shared<CS: ConstraintSystem<<E as Engine>::Scalar>>(
    &self,
    _cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<<E as Engine>::Scalar>>, SynthesisError> {
    Ok(vec![])
  }

  fn precommitted<CS: ConstraintSystem<<E as Engine>::Scalar>>(
    &self,
    _cs: &mut CS,
    _shared: &[AllocatedNum<<E as Engine>::Scalar>],
  ) -> Result<Vec<AllocatedNum<<E as Engine>::Scalar>>, SynthesisError> {
    Ok(vec![])
  }

  fn num_challenges(&self) -> usize {
    0
  }

  fn synthesize<CS: ConstraintSystem<<E as Engine>::Scalar>>(
    &self,
    cs: &mut CS,
    _shared: &[AllocatedNum<<E as Engine>::Scalar>],
    _precommitted: &[AllocatedNum<<E as Engine>::Scalar>],
    _challenges: Option<&[<E as Engine>::Scalar]>,
  ) -> Result<(), SynthesisError> {
    let mut prev_words = Vec::with_capacity(8);
    for (i, value) in self.previous_state.iter().copied().enumerate() {
      let word = UInt32::alloc(cs.namespace(|| format!("prev_state_{i}")), Some(value))?;
      let public = AllocatedNum::alloc_input(cs.namespace(|| format!("prev_public_{i}")), || {
        Ok(scalar_from_u32::<<E as Engine>::Scalar>(value))
      })?;
      pack_uint32_equals_public(cs, &word, &public, &format!("prev_state_{i}"))?;
      prev_words.push(word);
    }

    let mut block_bits = Vec::with_capacity(512);
    for (byte_index, byte) in self.block.iter().copied().enumerate() {
      for bit_index in 0..8 {
        let idx = byte_index * 8 + bit_index;
        let shift = 7 - bit_index;
        let value = ((byte >> shift) & 1) == 1;
        let allocated =
          AllocatedBit::alloc(cs.namespace(|| format!("block_bit_{idx}")), Some(value))?;
        block_bits.push(Boolean::from(allocated));
      }
    }

    let computed_next = sha256_compression_function(
      cs.namespace(|| "sha256_compression"),
      &block_bits,
      &prev_words,
    )?;

    for (i, (word, value)) in computed_next
      .into_iter()
      .zip(self.next_state.iter().copied())
      .enumerate()
    {
      let public = AllocatedNum::alloc_input(cs.namespace(|| format!("next_public_{i}")), || {
        Ok(scalar_from_u32::<<E as Engine>::Scalar>(value))
      })?;
      pack_uint32_equals_public(cs, &word, &public, &format!("next_state_{i}"))?;
    }

    Ok(())
  }
}

#[derive(Clone, Debug)]
struct Sha256CoreCircuit {
  final_state: [u32; 8],
  expected_digest: [u32; 8],
}

impl Sha256CoreCircuit {
  fn new(final_state: [u32; 8], expected_digest: [u32; 8]) -> Self {
    Self {
      final_state,
      expected_digest,
    }
  }
}

impl SpartanCircuit<E> for Sha256CoreCircuit {
  fn public_values(&self) -> Result<Vec<<E as Engine>::Scalar>, SynthesisError> {
    Ok(
      self
        .final_state
        .into_iter()
        .map(|word| scalar_from_u32::<<E as Engine>::Scalar>(word))
        .collect(),
    )
  }

  fn shared<CS: ConstraintSystem<<E as Engine>::Scalar>>(
    &self,
    _cs: &mut CS,
  ) -> Result<Vec<AllocatedNum<<E as Engine>::Scalar>>, SynthesisError> {
    Ok(vec![])
  }

  fn precommitted<CS: ConstraintSystem<<E as Engine>::Scalar>>(
    &self,
    _cs: &mut CS,
    _shared: &[AllocatedNum<<E as Engine>::Scalar>],
  ) -> Result<Vec<AllocatedNum<<E as Engine>::Scalar>>, SynthesisError> {
    Ok(vec![])
  }

  fn num_challenges(&self) -> usize {
    0
  }

  fn synthesize<CS: ConstraintSystem<<E as Engine>::Scalar>>(
    &self,
    cs: &mut CS,
    _shared: &[AllocatedNum<<E as Engine>::Scalar>],
    _precommitted: &[AllocatedNum<<E as Engine>::Scalar>],
    _challenges: Option<&[<E as Engine>::Scalar]>,
  ) -> Result<(), SynthesisError> {
    for (i, (&final_word, &expected_word)) in self
      .final_state
      .iter()
      .zip(&self.expected_digest)
      .enumerate()
    {
      let final_alloc =
        AllocatedNum::alloc_input(cs.namespace(|| format!("final_word_{i}")), || {
          Ok(scalar_from_u32::<<E as Engine>::Scalar>(final_word))
        })?;
      cs.enforce(
        || format!("digest_matches_{i}"),
        |lc| lc + final_alloc.get_variable(),
        |lc| lc + CS::one(),
        |lc| {
          lc + (
            scalar_from_u32::<<E as Engine>::Scalar>(expected_word),
            CS::one(),
          )
        },
      );
    }

    Ok(())
  }
}

fn format_state(state: &[u32; 8]) -> String {
  let mut output = String::with_capacity(64); // 8 words * 8 hex chars = 64 bytes
  for word in state {
    write!(&mut output, "{:08x}", word).unwrap();
  }
  output
}

fn sha256_blocks(message: &[u8]) -> Vec<[u8; 64]> {
  let mut data = message.to_vec();
  data.push(0x80);
  while data.len() % 64 != 56 {
    data.push(0x00);
  }
  let bit_len = (message.len() as u64) * 8;
  data.extend_from_slice(&bit_len.to_be_bytes());
  assert_eq!(data.len() % 64, 0);
  data
    .chunks(64)
    .map(|chunk| {
      let mut block = [0u8; 64];
      block.copy_from_slice(chunk);
      block
    })
    .collect()
}

fn prepare_inputs(message: &[u8]) -> (Vec<Sha256StepCircuit>, Sha256CoreCircuit, [u32; 8]) {
  let blocks = sha256_blocks(&message);
  let mut state = SHA256_IV;
  let mut step_circuits = Vec::with_capacity(blocks.len());

  for block in blocks.iter() {
    let prev_state = state;
    let next_state = sha256_compress(prev_state, block);
    step_circuits.push(Sha256StepCircuit::new(prev_state, *block, next_state));
    state = next_state;
  }

  // Compute expected digest from SHA2 library
  let expected_digest_bytes = Sha256::digest(&message);
  let mut expected_digest_words = [0u32; 8];
  for (i, chunk) in expected_digest_bytes.chunks(4).enumerate() {
    expected_digest_words[i] = u32::from_be_bytes(chunk.try_into().unwrap());
  }

  // Verify state matches expected (early validation)
  assert_eq!(state, expected_digest_words);

  let core_circuit = Sha256CoreCircuit::new(state, expected_digest_words);

  (step_circuits, core_circuit, expected_digest_words)
}

fn main() {
  tracing_subscriber::fmt()
    .with_target(false)
    .with_ansi(true)
    .with_env_filter(EnvFilter::from_default_env())
    .init();

  let message = vec![0u8; 1024];

  let (step_circuits, core_circuit, expected_digest_words) = prepare_inputs(&message);

  let (pk, vk) =
    NeutronNovaZkSNARK::<E>::setup(&step_circuits[0], &core_circuit, step_circuits.len())
      .expect("setup failed");

  let prep_state = NeutronNovaZkSNARK::<E>::prep_prove(&pk, &step_circuits, &core_circuit, true)
    .expect("prep_prove failed");

  let proof = NeutronNovaZkSNARK::<E>::prove(&pk, &step_circuits, &core_circuit, &prep_state, true)
    .expect("prove failed");

  let (_, core_public_values) = proof
    .verify(&vk, step_circuits.len())
    .expect("verify failed");

  let digest_words: [u32; 8] = core_public_values
    .iter()
    .map(scalar_to_u32)
    .collect::<Vec<_>>()
    .try_into()
    .expect("Should have exactly 8 values");

  let circuit_output = format_state(&digest_words);
  let expected_output = format_state(&expected_digest_words);

  assert_eq!(
    circuit_output, expected_output,
    "Circuit output does not match expected SHA-256 digest"
  );
}
