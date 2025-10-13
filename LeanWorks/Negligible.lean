/-
Some results about negligible functions (https://en.wikipedia.org/wiki/Negligible_function)
Inspired from https://github.com/JoeyLupo/cryptolib/blob/main/src/negligible.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- A function is negligible if it approaches zero
-- faster than the inverse of any polynomial
def negligible (f : ℕ → ℝ) :=
  ∀ c : ℕ, ∃ n₀, ∀ n, n₀ ≤ n → |f n| ≤ 1 / (n ^ c)

-- The zero function is negligible
lemma zero_negl : negligible (fun _ => 0) := by
  unfold negligible
  intro c
  use 1
  intro n
  norm_num

-- An auxiliary lemma
lemma negl_add_aux {f : ℕ → ℝ} (hf : negligible f):
    ∀ c : ℕ, ∃ n₀, ∀ n, n₀ ≤ n → |f n| ≤ (1 / (n ^ c)) / 2 := by
  intro c
  rcases hf (c + 1) with ⟨n₀, hn₀⟩
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
  apply le_trans (hn₀ n (le_of_max_le_left hn))
  have : 1 / (n : ℝ) ^ c / 2 = 1 / (n ^ c * 2) := by
    exact div_div 1 ((n : ℝ) ^ c) 2
  rw [this]
  apply (div_le_div_left _ _ _).mpr
  · have : (n : ℝ) ^ (c + 1) = n ^ c * n := rfl
    rw [this]
    apply (mul_le_mul_left npowpos).mpr twolen
  · norm_num
  · exact npowpos'
  apply mul_pos
  · apply pow_pos
    exact lt_of_lt_of_le two_pos twolen
  norm_num

-- The sum of two negligible functions is negligible
lemma negl_add {f g : ℕ → ℝ} :
    negligible f → negligible g → negligible (f + g) := by
  intro hf hg
  unfold negligible
  intro c
  rcases negl_add_aux hf c with ⟨n₀, hnf⟩
  rcases negl_add_aux hg c with ⟨n₁, hng⟩
  use max n₀ n₁
  intro n hn
  simp only [Pi.add_apply]
  calc |f n + g n|
    _ ≤ |f n| + |g n| := abs_add (f n) (g n)
    _ ≤ 1 / n ^ c / 2 + 1 / n ^ c / 2 := by
      apply add_le_add
      · apply hnf n
        exact le_of_max_le_left hn
      apply hng n
      exact le_of_max_le_right hn
    _ ≤ 1 / n ^ c := by linarith

-- If a function f is asymptotically upper bounded by
-- a negligible function g then it is negligible
lemma negl_of_bounded_negl {f g : ℕ → ℝ} (hg : negligible g) :
    (∃ n₀, ∀ n, n₀ ≤ n → |f n| ≤ |g n|) → negligible f := by
  rintro ⟨n₀, hn₀⟩
  unfold negligible
  intro c
  rcases hg c with ⟨n₁, hn₁⟩
  use max n₀ n₁
  intro n hn
  exact le_trans (hn₀ n (le_of_max_le_left hn)) (hn₁ n (le_of_max_le_right hn))

-- Multiplying a negligible function by a monomial yields a negligible function
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
  intro c
  rcases ih (c + 1) with ⟨n₀, hn₀⟩
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
    _ ≤ nn * (1 / nn ^ (c + 1)) := by
      apply (mul_le_mul_left _).mpr
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

-- A useful lemma for proving `pow_le_exp`
lemma sq_le_two_pow : ∀ n ≥ 4, n ^ 2 ≤ 2 ^ n := by
  apply Nat.le_induction
  · norm_num
  intro n hn ih
  calc (n + 1) ^ 2
    _ = n ^ 2 + 2 * n + 1 := by ring
    _ ≤ n ^ 2 + 3 * n := by linarith
    _ ≤ n ^ 2 + n * n := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_right
      linarith
    _ = 2 * n ^ 2 := by ring
    _ ≤ 2 * 2 ^ n := by linarith
    _ = 2 ^ (n + 1) := by exact Eq.symm Nat.pow_succ'

/-
Proof that exponential grows faster than polynomial.
Inspired from https://eventuallyalmosteverywhere.wordpress.com/2013/04/05/exponentials-kill-polynomials/
-/
lemma pow_le_exp (c : ℕ) :
    ∃ n₀, ∀ n, n₀ ≤ n → n ^ c ≤ 2 ^ n := by
  induction' c with c ih
  · use 1
    intro n _
    rw [pow_zero]
    exact Nat.one_le_two_pow
  rcases ih with ⟨n₀, hn₀⟩
  use max (8 * c + 4) (max (4 * n₀) 4)
  intro n hn
  have nge : 4 ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  have nge' : 4 * n₀ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have nge'' : 8 * c + 4 ≤ n := le_of_max_le_left hn
  have hn' : n₀ ≤ n / 4 + 1 := by
    apply (mul_le_mul_iff_of_pos_left four_pos).mp
    trans n
    · exact nge'
    nth_rw 1 [← Nat.div_add_mod n 4, mul_add, mul_one]
    simp only [add_le_add_iff_left]
    apply le_of_lt
    apply Nat.mod_lt
    linarith
  show n ^ (c + 1) ≤ 2 ^ n
  have : 2 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one 1)
  apply le_of_pow_le_pow_left this
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
    _ ≤ 2 ^ n * (2 ^ (4 * c) * ((n / 4 + 1) ^ c) ^ 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact sq_le_two_pow n nge
      positivity
    _ ≤ 2 ^ n * (2 ^ (4 * c) * (2 ^ (n / 4 + 1)) ^ 2) := by
      repeat apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      exact hn₀ (n / 4 + 1) hn'
    _ ≤ 2 ^ n * (2 ^ (4 * c) * 2 ^ (n / 2 + 2)) := by
      rw [← Nat.pow_mul]
      simp only [Nat.ofNat_pos, pow_pos, mul_le_mul_left]
      apply Nat.pow_le_pow_of_le_right
      · norm_num
      rw [add_mul, one_mul, add_le_add_iff_right, mul_comm]
      nth_rw 2 [← Nat.div_add_mod n 4]
      apply (Nat.le_div_iff_mul_le _).mpr
      · rw [mul_assoc, mul_comm (n / 4) 2, ← mul_assoc]
        simp only [Nat.reduceMul, le_add_iff_nonneg_right, zero_le]
      norm_num
    _ = 2 ^ n * 2 ^ (4 * c + n / 2 + 2) := by ring
    _ ≤ 2 ^ n * 2 ^ n := by
      simp only [Nat.ofNat_pos, pow_pos, mul_le_mul_left]
      apply Nat.pow_le_pow_of_le_right
      · norm_num
      apply (mul_le_mul_iff_of_pos_left two_pos).mp
      rw [mul_add, mul_add]
      linarith [Nat.mul_div_le n 2]
    _ = (2 ^ n) ^ 2 := by ring

lemma inv_exp_negl : negligible fun n ↦ (1 : ℝ) / 2 ^ n := by
  unfold negligible
  dsimp
  intro c
  rcases (pow_le_exp c) with ⟨n₀, hn₀⟩
  use max n₀ 1
  intro n hn
  have : |(1 : ℝ) / 2 ^ n| = 1 / 2 ^ n := by
    apply abs_eq_self.mpr
    positivity
  rw [this]
  repeat
    rw [one_div]
  apply inv_le_inv_of_le
  · apply pow_pos
    have : 1 ≤ n := by exact le_of_max_le_right hn
    positivity
  norm_cast
  exact hn₀ n (le_of_max_le_left hn)

/-
A formalization of a theorem by Bellare about defining
"negligible" for families of functions.
See https://eprint.iacr.org/1997/004.pdf
Theorem 3.2 in the paper corresponds to `fun_fam_negligible_iff`
-/

variable (I : Type*)

-- A family of functions indexed by `I`
def fun_fam := I → ℕ → ℝ

-- `F` is pointwise negligible if `F i` is negligible for every `i : I`
def pw_negligible (F : fun_fam I) :=
  ∀ i, negligible (F i)

-- `F` is uniformly negligible is there exists a negligible function `δ`
-- such that for all `i`, `F i` is eventually less than `δ`
def unif_negligible (F : fun_fam I) :=
  ∃ δ : ℕ → ℝ, negligible δ ∧ ∀ i, ∃ n₀, ∀ n, n₀ ≤ n → |F i n| ≤ |δ n|

-- Uniform negligibility implies pointwise negligibility
theorem pw_negl_of_unif_negl (F : fun_fam I) :
    unif_negligible I F → pw_negligible I F := by
  rintro ⟨f, ⟨hf, h⟩⟩
  intro i
  apply negl_of_bounded_negl hf
  exact h i

open Classical

variable [Countable I] [Nonempty I]

-- The converse and more complicated direction:
-- pointwise negligibility implies uniform negligibility
theorem unif_negl_of_pw_negl (F : fun_fam I) :
    pw_negligible I F → unif_negligible I F := by
  intro hF
  simp [pw_negligible, negligible] at hF
  -- we follow Bellare's proof very closely
  -- We define function `N i c` such that
  -- `F i c ≤ 1 / n ^ c` for all `n ≥ N i c`
  let N (i : I) (c : ℕ) : ℕ :=
    Classical.choose (hF i c)
-- a direct consequence of the definition of `N`
  have hN (i : I) (c : ℕ) : ∀ n, N i c ≤ n → |F i n| ≤ ((n : ℝ) ^ c)⁻¹ := by
    dsimp [N]
    exact Classical.choose_spec (hF i c)
  -- Let `s` be an injection from `I` to `ℕ`
  rcases Countable.exists_injective_nat I with ⟨s, s_inj⟩
  -- define function `N' j c` as `N i c` if there is
  -- some `i : I` such that `s i = j` and `0` otherwise
  let N' (j : ℕ) (c : ℕ) : ℕ :=
    if j ∈ Set.range s then N (Function.invFun s j) c else 0
  have hNN' (i : I) (c : ℕ) : N i c = N' (s i) c := by
    simp [N']
    rw [Function.leftInverse_invFun s_inj i]
  -- define Finset `S c = { N' 0 c, N' 1 c, ..., N' c c }`
  let S (c : ℕ) : Finset ℕ := (Finset.range (c + 1)).image (fun j => N' j c)
  have S_ne (c : ℕ) : (S c).Nonempty := by
    simp [S]
  -- define function `φ` as `φ 0 = N' 0 0` and
  -- `φ (c + 1) = max { N' 0 (c+1), N' 1 (c+1), ..., N' (c+1) (c+1), φ(c) + 1 }`
  -- this is function `h` in Bellare's paper
  -- for why we can't define it with `let rec`, see https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/working.20with.20.60let.20rec.60.20in.20proofs
  let φ (c : ℕ) : ℕ :=
    Nat.recOn c
      (N' 0 0)
      (fun c ih => max ((S (c + 1)).max' (S_ne (c + 1))) (ih + 1))
  -- The two claims `hφ` and `hφ'` below are
  -- direct consequences of the definition of `φ`
  have hφ (c j : ℕ) : j ≤ c → N' j c ≤ φ c := by
    intro j_le_c
    cases c with
    | zero =>
      have : j = 0 := by exact Nat.eq_zero_of_le_zero j_le_c
      rw [this]
      exact Nat.le_refl (N' 0 0)
    | succ c =>
      trans (S (c + 1)).max' (S_ne (c + 1))
      · have : N' j (c + 1) ∈ S (c + 1) := by
          simp [S]
          use j
          simp
          linarith
        exact Finset.le_max' (S (c + 1)) (N' j (c + 1)) this
      simp [φ]
  have hφ' (i : I) (c : ℕ) : s i ≤ c → N i c ≤ φ c := by
    intro si_le_c
    trans N' (s i) c
    · simp [hNN' i]
    exact hφ c (s i) si_le_c
  -- All the claims below follow the numeration used in Bellare
  have claim₁ (i : I) (c n : ℕ) : s i ≤ c → φ c ≤ n → |F i n| ≤ ((n : ℝ) ^ c)⁻¹ := by
    intro hi hn
    have : N i c ≤ n := by
      trans φ c
      · exact hφ' i c hi
      assumption
    exact hN i c n this
  have claim₂ (c : ℕ) : φ c < φ (c + 1) := by
    cases c <;> simp [φ]
  -- two direct consequences of `claim₂`
  -- that will be useful later on
  have claim₂' (c : ℕ) : c ≤ φ c := by
    induction' c with c hc
    · simp [φ]
    trans φ c + 1
    · linarith
    exact Nat.le_max_right ((S (c + 1)).max' (S_ne (c + 1))) (φ c + 1)
  have claim₂'' (c d : ℕ) : c < d → φ c < φ d := by
    apply Nat.le_induction
    · exact claim₂ c
    intro d _ ih
    trans φ d
    · assumption
    exact claim₂ d
  let T (n : ℕ) : Set ℕ := { c | φ c ≤ n}
  -- `T n` is finite (needed to define its max)
  have T_fin (n : ℕ) : (T n).Finite := by
    have hsubset : T n ⊆ {c | c ≤ n} := by
      intro c hc
      simp only [T, Set.mem_setOf_eq] at hc ⊢
      exact Nat.le_trans (claim₂' c) hc
    exact (Set.finite_le_nat n).subset hsubset
  -- cast `T n` into a Finset `T' n` to define its max
  -- we include `0` so that `T' n` is always non-empty
  let T' (n : ℕ) : Finset ℕ := (T_fin n).toFinset ∪ {0}
  -- `T' n` is non-empty
  have T'_ne (n : ℕ) : (T' n).Nonempty := by
    have : 0 ∈ T' n := by simp [T']
    exact Set.nonempty_of_mem this
  -- also, `T' n` is a subset of `T' (n + 1)`
  have T'_subset (n : ℕ) : T' n ⊆ T' (n + 1) := by
    simp [T']
    apply Finset.union_subset_union_left
    apply Set.Finite.toFinset_subset_toFinset.mpr
    simp [T]
    tauto
  have T'_le (c : ℕ) : ∀ a ∈ T' (φ c), a ≤ c := by
    intro a a_mem
    simp [T, T'] at a_mem
    rcases a_mem with h | h
    · contrapose! h
      exact claim₂'' c a h
    linarith
  -- define function `γ` as `γ n = max {c : ℕ | φ(c) ≤ n } ∪ { 0 }`
  -- this is function `g` in Bellare's paper
  let γ (n : ℕ) : ℕ := (T' n).max' (T'_ne n)
  -- `γ` is non-decreasing
  have claim₃ (n : ℕ) : γ n ≤ γ (n + 1) :=
    Finset.max'_subset (T'_ne n) (T'_subset n)
  have claim₃' (n m : ℕ) : n ≤ m → γ n ≤ γ m := by
    apply Nat.le_induction
    · rfl
    intro m _ ih
    trans γ m
    · assumption
    exact claim₃ m
  have claim₄ (n : ℕ) : N' 0 0 ≤ n → φ (γ n) ≤ n := by
    intro hn
    have : γ n ∈ T' n := by
      exact Finset.max'_mem (T' n) (T'_ne n)
    simp [T, T'] at this
    rcases this with h | h
    · assumption
    rw [h]
    simpa [φ]
  have claim₅ (c : ℕ) : γ (φ c) = c := by
    simp [γ]
    apply Nat.le_antisymm
    · exact Finset.max'_le (T' (φ c)) (T'_ne (φ c)) c (T'_le c)
    have : c ∈ T' (φ c) := by
      simp [T, T']
    exact Finset.le_max' (T' (φ c)) c this
  -- define `U n` as the set of values `F i n`
  -- for `i : I` such that `0 ≤ s i ≤ γ n`
  -- again, we include `0` so that `U n` is non-empty
  let U (n : ℕ) : Finset ℝ := {0} ∪ (Finset.range (γ n + 1)).image
      fun j => if j ∈ Set.range s then |F (Function.invFun s j) n| else 0
  have U_ne (n : ℕ) : (U n).Nonempty := by
    have : 0 ∈ U n := by simp [U]
    exact Set.nonempty_of_mem this
  -- finally, we can define `δ`
  let δ (n : ℕ) : ℝ := (U n).max' (U_ne n)
  have δ_nonneg (n : ℕ) : 0 ≤ δ n := by
    simp [δ]
    have : 0 ∈ U n := by simp [U]
    exact Finset.le_max' (U n) 0 this
  have hδ (i : I)  (n: ℕ) : s i ≤ γ n → |F i n| ≤ δ n := by
    intro hsi
    have : |F i n| ∈ U n := by
      simp [U]
      right
      use s i
      constructor
      · linarith
      simp
      rw [Function.leftInverse_invFun s_inj i]
    simp [δ]
    exact Finset.le_max' (U n) |F i n| this
  -- every function `F i` is eventually less than `δ`
  have claim₆ : ∀ i, ∃ n₀, ∀ n, n₀ ≤ n → |F i n| ≤ |δ n| := by
    intro i
    use φ (s i)
    intro n hn
    have : s i ≤ γ n := by
      apply claim₃' at hn
      rwa [← claim₅ (s i)]
    trans δ n
    exact hδ i n this
    exact le_abs_self (δ n)
  -- `δ` is negligible
  have claim₇ : negligible δ := by
    intro c
    use max (max (φ c) (N' 0 0)) 1
    intro n hn
    have ncast_ge_one : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr (le_of_max_le_right hn)
    rw [abs_of_nonneg (δ_nonneg n)]
    simp
    trans ((n : ℝ) ^ (γ n))⁻¹
    · simp [δ]
      have n_ge : φ (γ n) ≤ n := claim₄ n (le_of_max_le_right (le_of_max_le_left hn))
      intro x hx
      simp [U] at hx
      rcases hx with h | h
      · rw [h]
        positivity
      rcases h with ⟨j, j_le, hj⟩
      rw [← hj]
      by_cases h' : ∃ i, s i = j
      · rw [if_pos h']
        -- now use claim₁ to conclude
        rcases h' with ⟨i, hij⟩
        rw [← hij,Function.leftInverse_invFun s_inj i]
        have : s i ≤ γ n := by
          linarith
        exact claim₁ i (γ n) n this n_ge
      rw [if_neg h']
      positivity
    show ((n : ℝ) ^ γ n)⁻¹ ≤ ((n : ℝ) ^ c)⁻¹
    have c_le : c ≤ γ n := by
      trans γ (φ c)
      · exact le_of_eq (claim₅ c).symm
      exact claim₃' (φ c) n (le_of_max_le_left (le_of_max_le_left hn))
    have : (n : ℝ) ^ c ≤ (n : ℝ) ^ (γ n) := by
      apply pow_le_pow_right
      · exact ncast_ge_one
      assumption
    apply inv_le_inv_of_le
    · have : 0 < (n : ℝ) := by
        linarith
      exact pow_pos this c
    assumption
  -- finally, we have all we need to conclude
  exact ⟨δ, claim₇, claim₆⟩

theorem fun_fam_negligible_iff (F : fun_fam I) :
    pw_negligible I F ↔ unif_negligible I F := by
  constructor
  · exact unif_negl_of_pw_negl I F
  · exact pw_negl_of_unif_negl I F
