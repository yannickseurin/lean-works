/-
Some results about negligible functions (https://en.wikipedia.org/wiki/Negligible_function)
Inspired from https://github.com/JoeyLupo/cryptolib/blob/main/src/negligible.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def negligible (f : ℕ → ℝ) :=
  ∀ c > 0, ∃ n₀, ∀ n,
  n₀ ≤ n → |f n| <  1 / (n ^ c)

lemma zero_negl : negligible (fun _ => 0) := by
  unfold negligible
  intro c _
  use 1
  intro n hn
  norm_num
  apply pow_pos
  exact Nat.cast_pos'.mpr hn

lemma negl_add_aux {f : ℕ → ℝ} (hf : negligible f):
    ∀ c > 0, ∃ n₀, ∀ n, n₀ ≤ n → |f n| <  (1 / (n ^ c)) / 2 := by
  intro c hc
  have hc' : 0 < c + 1 := by linarith
  rcases hf (c + 1) hc' with ⟨n₀, hn₀⟩
  use max n₀ 2
  intro n hn
  have twolen : 2 ≤ (n : ℝ) := by
    apply Nat.ofNat_le_cast.mpr
    exact le_of_max_le_right hn
  have npowpos : 0 < (n : ℝ) ^ c := by
    apply pow_pos
    linarith
  have npowpos' : 0 < (n : ℝ) ^ (c + 1) := by
    apply pow_pos
    linarith
  apply lt_of_lt_of_le (hn₀ n (le_of_max_le_left hn))
  have : 1 / (n : ℝ) ^ c / 2 = 1 / (n ^ c * 2) := by
    exact div_div 1 ((n : ℝ) ^ c) 2
  rw [this]
  apply (div_le_div_left _ _ _).mpr
  · have : (n : ℝ) ^ (c + 1) = n ^ c * n := rfl
    rw [this]
    apply (mul_le_mul_left npowpos).mpr twolen
  · norm_num
  · linarith
  apply mul_pos
  · apply pow_pos
    exact lt_of_lt_of_le two_pos twolen
  norm_num

lemma negl_add {f g : ℕ → ℝ} :
    negligible f → negligible g → negligible (f + g) := by
  intro hf hg
  unfold negligible
  intro c hc
  rcases negl_add_aux hf c hc with ⟨nf, hnf⟩
  rcases negl_add_aux hg c hc with ⟨ng, hng⟩
  use max nf ng
  intro n hn
  dsimp
  calc |f n + g n|
    _ ≤ |f n| + |g n| := abs_add (f n) (g n)
    _ < 1 / n ^ c / 2 + 1 / n ^ c / 2 := by
      apply add_lt_add
      · apply hnf n
        exact le_of_max_le_left hn
      apply hng n
      exact le_of_max_le_right hn
    _ ≤ 1 / n ^ c := by linarith

lemma negl_of_bounded_negl {f g : ℕ → ℝ} (hg : negligible g) :
    (∀ n, |f n| ≤ |g n|) → negligible f := by
  intro h
  unfold negligible
  intro c hc
  rcases hg c hc with ⟨n₀, hn₀⟩
  use n₀
  intro n hn
  exact lt_of_le_of_lt (h n) (hn₀ n hn)

lemma pow_mul_negl {f : ℕ → ℝ} {k : ℕ} (hf : negligible f) :
    negligible fun n ↦ n ^ k * (f n) := by
  induction' k with k ih
  · have : (fun n ↦ n ^ 0 * (f n)) = f := by
      ext
      rw [pow_zero, one_mul]
    rw [this]
    exact hf
  unfold negligible
  dsimp
  intro c hc
  have hc' : 0 < c + 1 := by linarith
  rcases ih (c + 1) hc' with ⟨n₀, hn₀⟩
  dsimp at hn₀
  use max n₀ 1
  intro n hn
  have npos : 0 < n := by
    exact lt_of_lt_of_le (one_pos) (le_of_max_le_right hn)
  let nn := (n : ℝ)
  calc |nn ^ (k + 1) * f n|
    _ = |nn * nn ^ k * f n| := by
      congr
      exact pow_succ' nn k
    _ = |nn * (nn ^ k * f n)| := by rw [mul_assoc]
    _ = |nn| * |nn ^ k * f n| := abs_mul nn (nn ^ k * f n)
    _ = nn * |nn ^ k * f n| := by
      apply mul_eq_mul_right_iff.mpr
      left
      exact Nat.abs_cast n
    _ < nn * (1 / nn ^ (c + 1)) := by
      apply (mul_lt_mul_left _).mpr
      · exact hn₀ n (le_of_max_le_left hn)
      exact Nat.cast_pos'.mpr npos
    _ = 1 / nn ^ c := by
      rw [mul_div, mul_one]
      apply (div_eq_div_iff _ _).mpr
      · rw [one_mul]
        exact (pow_succ' nn c).symm
      · apply ne_of_gt
        apply pow_pos
        exact Nat.cast_pos'.mpr npos
      apply ne_of_gt
      apply pow_pos
      exact Nat.cast_pos'.mpr npos


-- Useful for proving `pow_lt_exp`
lemma sq_lt_two_pow : ∀ n ≥ 5, n ^ 2 < 2 ^ n := by
  apply Nat.le_induction
  · norm_num
  intro n hn ih
  calc (n + 1) ^ 2
    _ = n ^ 2 + 2 * n + 1 := by ring
    _ < n ^ 2 + 3 * n := by linarith
    _ < n ^ 2 + n * n := by
      apply Nat.add_lt_add_left
      apply Nat.mul_lt_mul_of_pos_right <;> linarith
    _ = 2 * n ^ 2 := by ring
    _ < 2 * 2 ^ n := by linarith
    _ = 2 ^ (n + 1) := by exact Eq.symm Nat.pow_succ'

/-
Proof that exponential grows faster than polynomial.
Inspired from https://eventuallyalmosteverywhere.wordpress.com/2013/04/05/exponentials-kill-polynomials/
-/
lemma pow_lt_exp (c : ℕ) :
    ∃ n₀, ∀ n, n₀ ≤ n → n ^ c < 2 ^ n := by
  induction' c with c ih
  · use 1
    intro n hn
    rw [pow_zero]
    apply Nat.one_lt_two_pow
    linarith
  rcases ih with ⟨n₀, hn₀⟩
  use max (8 * c + 4) (max (4 * n₀) 5)
  intro n hn
  have nge : 5 ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  have nge' : 4 * n₀ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have nge'' : 8 * c + 4 ≤ n := le_of_max_le_left hn
  have hn' : n₀ ≤ n / 4 + 1 := by
    apply (mul_le_mul_iff_of_pos_left four_pos).mp
    trans n
    · exact nge'
    nth_rw 1 [← Nat.div_add_mod n 4, mul_add, mul_one]
    simp
    apply le_of_lt
    apply Nat.mod_lt
    linarith
  show n ^ (c + 1) < 2 ^ n
  apply lt_of_pow_lt_pow_left 2
  · positivity
  calc (n ^ (c + 1)) ^ 2
    _ = n ^ 2 * (n ^ c) ^ 2 := by ring
    _ ≤ n ^ 2 * ((4 * (n / 4 + 1)) ^ c) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply (Nat.pow_le_pow_left _) 2
        apply (Nat.pow_le_pow_left _) c
        calc n
          _ = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
          _ ≤ 4 * (n / 4) + 4 := by
            apply le_of_lt
            apply Nat.add_lt_add_left _ (4 * (n / 4))
            apply Nat.mod_lt
            linarith
          _ = 4 * (n / 4 + 1) := by ring
      positivity
    _ = n ^ 2 * (4 ^ c * (n / 4 + 1) ^ c) ^ 2 := by rw [mul_pow]
    _ = n ^ 2 * (4 ^ c) ^ 2 * ((n / 4 + 1) ^ c) ^ 2 := by ring
    _ = n ^ 2 * 2 ^ (4 * c) * ((n / 4 + 1) ^ c) ^ 2 := by
      have : (4 ^ c) ^ 2 = 2 ^ (4 * c) := by
        have : 4 = 2 ^ 2 := by norm_num
        nth_rw 1 [this]
        rw [← Nat.pow_mul, ← Nat.pow_mul]
        ring
      rw [this]
    _ = n ^ 2 * (2 ^ (4 * c) * ((n / 4 + 1) ^ c) ^ 2) := by ring
    _ < 2 ^ n * (2 ^ (4 * c) * ((n / 4 + 1) ^ c) ^ 2) := by
      apply Nat.mul_lt_mul_of_pos_right
      · exact sq_lt_two_pow n nge
      positivity
    _ < 2 ^ n * (2 ^ (4 * c) * (2 ^ (n / 4 + 1)) ^ 2) := by
      apply Nat.mul_lt_mul_of_pos_left
      · apply Nat.mul_lt_mul_of_pos_left
        · apply Nat.pow_lt_pow_left
          · exact hn₀ (n / 4 + 1) hn'
          norm_num
        positivity
      positivity
    _ ≤ 2 ^ n * (2 ^ (4 * c) * 2 ^ (n / 2 + 2)) := by
      rw [← Nat.pow_mul]
      simp
      apply Nat.pow_le_pow_of_le_right
      · norm_num
      rw [add_mul, one_mul, add_le_add_iff_right, mul_comm]
      nth_rw 2 [← Nat.div_add_mod n 4]
      apply (Nat.le_div_iff_mul_le _).mpr
      · rw [mul_assoc, mul_comm (n / 4) 2, ← mul_assoc]
        simp
      norm_num
    _ = 2 ^ n * 2 ^ (4 * c + n / 2 + 2) := by ring
    _ ≤ 2 ^ n * 2 ^ n := by
      simp
      apply Nat.pow_le_pow_of_le_right
      · norm_num
      apply (mul_le_mul_iff_of_pos_left two_pos).mp
      rw [mul_add, mul_add]
      linarith [Nat.mul_div_le n 2]
    _ = (2 ^ n) ^ 2 := by ring

lemma inv_exp_negl : negligible fun n ↦ (1 : ℝ) / 2 ^ n := by
  unfold negligible
  dsimp
  intro c _
  rcases (pow_lt_exp c) with ⟨n₀, hn₀⟩
  use max n₀ 1
  intro n hn
  have : |(1 : ℝ) / 2 ^ n| = 1 / 2 ^ n := by
    apply abs_eq_self.mpr
    positivity
  rw [this]
  repeat
    rw [one_div]
  apply inv_lt_inv_of_lt
  · apply pow_pos
    have : 1 ≤ n := by exact le_of_max_le_right hn
    positivity
  norm_cast
  exact hn₀ n (le_of_max_le_left hn)
