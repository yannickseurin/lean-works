/-
Copyright (c) 2025 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import Mathlib.Probability.Distributions.Uniform
import LeanWorks.ToMathlib

namespace PMF

section PMFBind

variable {α β : Type}
         (p : PMF α) (f : α → PMF β)

-- variant of `PMF.pure_bind`
@[simp]
theorem pure_bind' (a : α) : ((PMF.pure a) >>= f) = f a := pure_bind a f

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

lemma bind_skip_const (pa : PMF α) (pb : PMF β) (f : α → PMF β) :
    (∀ a : α, f a = pb) → pa.bind f = pb := by
  intro h
  ext x
  simp [h]
  rw [ENNReal.tsum_mul_right]
  rw [PMF.tsum_coe pa]
  simp only [one_mul]

lemma bind_skip_const' (pa : PMF α) (pb : PMF β) (f : α → PMF β) :
    (∀ a : α, f a = pb) → (pa >>= f) = pb := bind_skip_const pa pb f

end PMFBind

noncomputable section Uniform

variable {α β : Type} [Fintype α] [Nonempty α] [DecidableEq α]
                      [Fintype β] [Nonempty β] [DecidableEq β]

def uniform_then_prod : PMF (α × β) := do
  let a ← PMF.uniformOfFintype α
  let b ← PMF.uniformOfFintype β
  PMF.pure (a, b)

def uniform_then_prod' : PMF (α × β) :=
    (PMF.uniformOfFintype α) >>= fun x ↦ (PMF.uniformOfFintype β) >>= fun y ↦ PMF.pure (x, y)

/--
Drawing `a` from `α` and `b` from `β` and forming the pair `(a, b)`
yields the uniform distribution on `α × β`.
The process can also be written
`PMF.uniformOfFintype α >>= fun x ↦ PMF.uniformOfFintype β >>= fun y ↦ PMF.pure (x, y)`
-/
lemma uniform_prod :
    (
    do
      let a ← PMF.uniformOfFintype α
      let b ← PMF.uniformOfFintype β
      PMF.pure (a, b)
    ) = PMF.uniformOfFintype (α × β) := by
  ext p
  let (a, b) := p
  simp_rw
    [PMF.bind_apply', PMF.uniformOfFintype_apply, PMF.pure_apply, mul_ite,
    mul_one, mul_zero, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.tsum_mul_left, ← ENNReal.tsum_prod]
  rw [ENNReal.mul_inv_natCast]
  simp [eq_comm]

/--
If `f : α → β` is bijective, then drawing `a` uniformly from `α`
and applying `f` yields the uniform distribution on `β`.
Using the monadic stucture of PMFs, the process of sampling `a` from
`α` and applyng `f` is expressed as `PMF.map f (PMF.uniformOfFintype α)`.
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
    PMF.map f (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
  let B := (Fintype.card β : ENNReal)
  ext b
  simp only [map_apply, uniformOfFintype_apply]
  rw [Fintype.card_of_bijective hf]
  rcases Function.bijective_iff_has_inverse.mp hf with ⟨f', invli, invri⟩
  let a := f' b
  let Sa : Finset α := {x | x = a}
  let Sna : Finset α := {x | x ≠ a}
  have hu : Finset.univ = Sa ∪ Sna := by
    ext x
    simp
    simp [Sa, Sna]
    apply Classical.em
  have hd : Disjoint Sa Sna := by
    apply Finset.disjoint_left.mpr
    simp [Sa, Sna]
  rw [tsum_fintype fun y ↦ if b = f y then B⁻¹ else 0]
  rw [hu, Finset.sum_union hd]
  have snazero: ∀ x ∈ Sna, (fun y ↦ if b = f y then B⁻¹ else 0) x = 0 := by
    intro x xsna
    dsimp
    rw [if_neg]
    apply Finset.mem_filter.mp at xsna
    intro bfx
    have : x = a :=
      calc
        x = f' (f x) := by exact (invli x).symm
        _ = f' b := by rw [← bfx]
        _ = a := rfl
    tauto
  have sacardb : ∀ x ∈ Sa, (fun y ↦ if b = f y then B⁻¹ else 0) x = B⁻¹ := by
    intro x xsa
    dsimp
    rw [if_pos]
    apply Finset.mem_filter.mp at xsa
    calc
      b = f (f' b) := by exact (invri b).symm
      _ = f a := by rfl
      _ = f x := by rw [xsa.2]
  rw [Finset.sum_eq_zero snazero, add_zero, Finset.sum_congr rfl sacardb, Finset.sum_const]
  have cardsa : Finset.card Sa = 1 := by
    apply (Fintype.existsUnique_iff_card_one _).mp
    exact existsUnique_eq
  rw [cardsa]
  exact one_nsmul B⁻¹

end Uniform

end PMF
