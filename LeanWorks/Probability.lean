/-
Copyright (c) 2025 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import Mathlib.Probability.Distributions.Uniform
import LeanWorks.ToMathlib

open ENNReal

namespace PMF

section PMFBind

universe u

variable {α β : Type u}
         (p : PMF α) (f : α → PMF β)

-- variant of `PMF.pure_bind`
@[simp]
theorem pure_bind' (a : α) : ((pure a) >>= f) = f a := pure_bind a f

-- variant of `PMF.bind_apply`
@[simp]
theorem bind_apply' (b : β) :
    (p >>= f) b = ∑' (a : α), p a * (f a) b := bind_apply p f b

lemma bind_skip (p : PMF α) (f g : α → PMF β) :
    (∀ a : α, f a = g a) → p.bind f = p.bind g := by
  intro h
  ext x
  simp
  apply tsum_congr
  intro b
  rw [h b]

lemma bind_skip' (p : PMF α) (f g : α → PMF β) :
    (∀ a : α, f a = g a) → (p >>= f) = (p >>= g) := bind_skip p f g

@[simp]
lemma bind_skip_const (pa : PMF α) (pb : PMF β) (f : α → PMF β) :
    (∀ a : α, f a = pb) → pa.bind f = pb := by
  intro h
  ext x
  simp [h]
  rw [ENNReal.tsum_mul_right]
  rw [tsum_coe pa]
  simp only [one_mul]

@[simp]
lemma bind_skip_const' (pa : PMF α) (pb : PMF β) (f : α → PMF β) :
    (∀ a : α, f a = pb) → (pa >>= f) = pb := bind_skip_const pa pb f

end PMFBind

noncomputable section Uniform

def uniform_zmod (n : ℕ) [NeZero n] : PMF (ZMod n) :=
  uniformOfFintype (ZMod n)

@[simp]
lemma uniform_zmod_prob {n : ℕ} [NeZero n] (a : ZMod n) :
    (uniform_zmod n) a = (n : ℝ≥0∞)⁻¹ := by
  simp [uniform_zmod]

@[simp]
lemma uniform_zmod_prob' {n : ℕ} [NeZero n] (a : ZMod n) :
    (uniformOfFintype (ZMod n)) a = (n : ℝ≥0∞)⁻¹ := by
  simp

@[simp]
lemma uniform_threewise_prob {G : Type*} [Fintype G] [Nonempty G] (a : G × G × G) :
    (uniformOfFintype (G × G × G)) a =
      (Nat.card G : ℝ≥0∞)⁻¹ * (Nat.card G : ℝ≥0∞)⁻¹ * (Nat.card G : ℝ≥0∞)⁻¹ := by
  simp only [uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul, Nat.card_eq_fintype_card]
  rw [← Nat.cast_mul, ENNReal.mul_inv_natCast, Nat.cast_mul, ENNReal.mul_inv_natCast, ← mul_assoc]

def uniform_coin : PMF (Bool) := uniformOfFintype Bool

end Uniform

noncomputable section UniformProd

universe u

variable {α β : Type u} [Fintype α] [Nonempty α] [DecidableEq α]
                        [Fintype β] [Nonempty β] [DecidableEq β]

/--
Drawing `a` from `α` and `b` from `β` and forming the pair `(a, b)`
yields the uniform distribution on `α × β`.
The process can also be written
`PMF.uniformOfFintype α >>= fun x ↦ PMF.uniformOfFintype β >>= fun y ↦ PMF.pure (x, y)`
-/
lemma uniform_prod :
    (do
       let a ← uniformOfFintype α
       let b ← uniformOfFintype β
       pure (a, b)) = uniformOfFintype (α × β) := by
  ext p
  let (a, b) := p
  simp only [bind_apply', uniformOfFintype_apply, pure_apply,
    mul_ite, mul_one, mul_zero, Fintype.card_prod, Nat.cast_mul,
    ENNReal.tsum_mul_left, ← ENNReal.tsum_prod, ENNReal.mul_inv_natCast,
    eq_comm, Prod.mk.eta, tsum_ite_eq]

end UniformProd

noncomputable section UniformBij

universe u v

variable {α : Type u} [Fintype α] [Nonempty α] [DecidableEq α]
         {β : Type v} [Fintype β] [Nonempty β] [DecidableEq β]

/--
If `f : α → β` is bijective, then drawing `a` uniformly from `α`
and applying `f` yields the uniform distribution on `β`.
Using the monadic structure of PMFs, the process of sampling `a` from
`α` and applying `f` is expressed as `PMF.map f (PMF.uniformOfFintype α)`.
By definition, this is `(PMF.uniformOfFintype α).bind (PMF.pure ∘ f)`
or, using `>>=` notation, `(PMF.uniformOfFintype α) >>= (PMF.pure ∘ f)`.
One can also define it with the `do` notation:
```lean4
def foo : PMF β := do
  let x ← PMF.uniformOfFintype α
  PMF.pure (f x)
```
-/
lemma map_eq_uniform_of_bijective (f : α → β) (hf : Function.Bijective f) :
    map f (uniformOfFintype α) = uniformOfFintype β := by
  ext b
  simp only [map_apply, uniformOfFintype_apply]
  rw [Fintype.card_of_bijective hf]
  rcases Function.bijective_iff_has_inverse'.mp hf with ⟨g, hg⟩
  simp_rw [hg]
  simp [tsum_ite_eq]

end UniformBij

section UniformGroup

/--
Applying exponentiation to `x` drawn uniformly at raandom from `ZMod #G`
yields the uniform distribution on `G`.
-/
theorem exp_eq_uniform_group {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (g : G) (hg : Group.IsGenerator G g) :
    PMF.map (fun x ↦ g ^ x.val) (uniform_zmod (Nat.card G)) = PMF.uniformOfFintype G := by
  rw [uniform_zmod]
  apply map_eq_uniform_of_bijective
  exact Group.exp_bijective g hg

end UniformGroup

end PMF
