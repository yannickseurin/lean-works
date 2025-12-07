/-
Copyright (c) 2025 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import LeanWorks.Probability

/-!
# Public-Key Encryption Schemes

This file gives definitions for PKE schemes.
-/

/--
A public key encryption (PKE) scheme.
We model randomized algorithm as PMFs over their return type.
-/
structure PKE where
  /-- public parameters -/
  {P : Type}
  /-- secret keys -/
  {SK : Type}
  /-- public keys -/
  {PK : Type}
  /-- messages -/
  {M : Type}
  [dem : DecidableEq M]
  /-- ciphertexts -/
  {C : Type}
  /-- `setup` takes no input and returns
  public parameters `par` (randomized) -/
  setup : PMF P
  /-- `keygen` takes public parameters `par` and generates a
  secret public key pair `(sk, pk)` (randomized) -/
  keygen : P → PMF (SK × PK)
  /-- `encrypt` takes public parameters `par`, a public key `pk`,
  and a message `m` and returns a ciphertext `c` (randomized) -/
  encrypt : P → PK → M → PMF C
  /-- `decrypt` takes public parameters `par`, a secret key `sk`,
  and a ciphertext `c`, and returns a message `m` or `⊥` indicating
  decryption failure -/
  decrypt : P → SK → C → Option M

attribute [instance] PKE.dem

namespace PKE

/-- The correctness experiment.
Executes the public-key scheme by encrypting and decrypting some message `m`
and returns 1 if the ciphertexts decrypts to `m` and 0 otherwise.
-/
noncomputable def correctness (pke : PKE) (m : pke.M) : PMF (ZMod 2) := do
  let par ← pke.setup
  let (sk, pk) ← pke.keygen par
  let c ← pke.encrypt par pk m
  PMF.pure (if pke.decrypt par sk c = some m then 1 else 0)

/--
A public-key encryption scheme is (perfectly) correct if for every
message `m`, decryption undoes encryption with probability 1.
-/
def PerfectlyCorrect (pke : PKE) : Prop := ∀ (m : pke.M), pke.correctness m = PMF.pure 1

/--
An IND-CPA adversary against a PKE.
-/
structure Adversary (pke : PKE) where
  /-- state passed from `A₁` to `A₂` -/
  A_state : Type
  /-- First stage: takes public parameters `par`, a public key `pk`,
  and outputs two messages `m₀` and `m₁` and a state. -/
  A₁ : pke.P → pke.PK → PMF (pke.M × pke.M × A_state)
  /-- Second stage: takes a ciphertext `c` (of either `m₀` or `m₁`)
  and a state passed from `A₁` and returns a bit. -/
  A₂ : pke.C → A_state → PMF (ZMod 2)

/--
The IND-CPA (semantic security) game.
Returns 1 if the attacker A₂ guesses the correct bit.
-/
noncomputable def IND_CPA {pke : PKE} (adversary : Adversary pke) : PMF (ZMod 2) := do
  let par ← pke.setup
  let (_, pk) ← pke.keygen par
  let (m₀, m₁, state) ← adversary.A₁ par pk
  let b ← PMF.uniform_2
  let c ← pke.encrypt par pk (if b = 0 then m₀ else m₁)
  let b' ← adversary.A₂ c state
  pure (if b = b' then 1 else 0)

/--
The advantage of an IND-CPA adversary against a PKE scheme.
-/
noncomputable def advantage {pke : PKE} (adversary : Adversary pke) : ℝ :=
  |(IND_CPA adversary 1).toReal - 1 / 2|

end PKE
