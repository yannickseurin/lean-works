/-
Copyright (c) 2025 Yannick Seurin. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Yannick Seurin
-/
import Mathlib.Tactic

/-!
General lemmas that could be ported to Mathlib, maybe...
-/

/-
This instance allows to infer `NeZero (Nat.card G)` when working with a Fintype group
See https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/instance.20synthesis.20failed
-/
instance {α : Type u} [Finite α] [Nonempty α] : NeZero (Nat.card α) where
  out := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

-- theorem add_zmod_two (b b' : ZMod 2) : 1 + b + b' = if b = b' then 1 else 0 := by
--   by_cases h : b = b'
--   · rw [if_pos h, h]
--     exact CharTwo.add_cancel_right 1 b'
--   rw [if_neg h]
--   sorry

section Bijection

universe u v

/--
The n-fold product of a type.
-/
def nfoldProd (α : Type u) : ℕ → Type u
  | 0     => PUnit
  | 1     => α
  | n + 2 => α × nfoldProd α (n + 1)

/--
The application of a function `f` coordinate-wise on an n-tuple.
-/
def nfoldMap {α : Type u} {β : Type v} (f : α → β) : (n : ℕ) → nfoldProd α n → nfoldProd β n
  | 0, _       => PUnit.unit
  | 1, x       => f x
  | n + 2, (x, xs) => (f x, nfoldMap f (n + 1) xs)

variable {α : Type u} {β : Type v} {f : α → β}

theorem Function.bijective_iff_has_inverse' :
    Bijective f ↔ ∃ g : β → α, (∀ x : α, ∀ y : β, y = f x ↔ x = g y) := by
  constructor
  · intro f_bij
    rcases Function.bijective_iff_has_inverse.mp f_bij with ⟨g, gli, gri⟩
    use g
    intro x y
    constructor
    · intro h
      rw [eq_comm, h, gli]
    intro h
    rw [eq_comm, h, gri]
  rintro ⟨g, hg⟩
  apply Function.bijective_iff_has_inverse.mpr
  use g
  constructor
  · intro x
    have : f x = f x ↔ x = g (f x) := hg x (f x)
    tauto
  intro y
  have : g y = g y ↔ y = f (g y) := iff_comm.mp (hg (g y) y)
  tauto

theorem Function.bijective_nfold (n : ℕ) (hf : Function.Bijective f) :
    Function.Bijective (nfoldMap f n) := by
  apply (Function.bijective_iff_existsUnique (nfoldMap f n)).mpr
  cases n with
    | zero =>
      simp [nfoldProd, nfoldMap]
    | succ n =>
      induction n with
      | zero =>
        exact fun b ↦ Bijective.existsUnique hf b
      | succ n ih =>
        simp only [nfoldProd, nfoldMap, Prod.forall, Prod.mk.injEq] at *
        intro b bs
        specialize ih bs
        have hb : ∃! a, f a = b := by exact Function.Bijective.existsUnique hf b
        simp [ExistsUnique] at *
        rcases hb with ⟨a, ha, ha'⟩
        rcases ih with ⟨as, has, has'⟩
        use a, as
        tauto

end Bijection

section ENNReal

theorem ENNReal.mul_natCast {a b : ℕ} : (a : ENNReal) * (b : ENNReal) = (↑(a * b) : ENNReal) := by
  exact Eq.symm (Nat.cast_mul a b)

theorem ENNReal.mul_inv_natCast {a b : ℕ} :
    ((a : ENNReal) * (b : ENNReal))⁻¹ = (a : ENNReal)⁻¹ * (b : ENNReal)⁻¹ := by
  apply ENNReal.mul_inv
  · right
    exact ENNReal.natCast_ne_top b
  left
  exact ENNReal.natCast_ne_top a

theorem ENNReal.inv_mul_cancel_natCast {a : ℕ} (ha : a ≠ 0) :
     (a : ENNReal)⁻¹ * (a : ENNReal) = 1 := by
  apply ENNReal.inv_mul_cancel
  · exact Nat.cast_ne_zero.mpr ha
  exact natCast_ne_top a

theorem ENNReal.mul_inv_cancel_natCast {a : ℕ} (ha : a ≠ 0) :
     (a : ENNReal) * (a : ENNReal)⁻¹  = 1 := by
  apply ENNReal.mul_inv_cancel
  · exact Nat.cast_ne_zero.mpr ha
  exact natCast_ne_top a

end ENNReal

section Group

instance {G : Type*} [Group G] [IsCyclic G] : CommGroup G := IsCyclic.commGroup

namespace Group

def IsGenerator (G : Type*) [Group G] (g : G) :=
  ∀ x : G, x ∈ Subgroup.zpowers g

open Classical in
noncomputable def generators (G : Type*) [Group G] [Fintype G] : Finset G :=
  { g : G | IsGenerator G g }

open Classical in
theorem generators_nonempty_of_cyclic (G : Type*) [Group G] [IsCyclic G] [Fintype G] :
    (generators G).Nonempty := by
  simp only [Finset.Nonempty, generators, IsGenerator, Finset.mem_filter, Finset.mem_univ, true_and]
  exact IsCyclic.exists_zpow_surjective

theorem g_order {G : Type*} [Group G] (g : G) (hg : IsGenerator G g) :
    orderOf g = Nat.card G :=
  orderOf_eq_card_of_forall_mem_zpowers hg

theorem zpow_val_add {G : Type*} [Group G] [Fintype G]
    (g : G) (hg : IsGenerator G g)
    (a b : ZMod (Nat.card G)) :
    g ^ (a + b).val = g ^ (a.val + b.val) := by
  apply pow_eq_pow_iff_modEq.mpr
  rw [g_order g hg]
  unfold Nat.ModEq
  have : (a + b).val % (Nat.card G) = (a + b).val :=
    Nat.mod_eq_of_lt (ZMod.val_lt (a + b))
  rw [this]
  exact ZMod.val_add a b

theorem zpow_val_mul {G : Type*} [Group G] [Fintype G]
    (g : G) (hg : IsGenerator G g)
    (a b : ZMod (Nat.card G)) :
    g ^ (a * b).val = g ^ (a.val * b.val) := by
  apply pow_eq_pow_iff_modEq.mpr
  rw [g_order g hg]
  unfold Nat.ModEq
  have : (a * b).val % (Nat.card G) = (a * b).val :=
    Nat.mod_eq_of_lt (ZMod.val_lt (a * b))
  rw [this]
  exact ZMod.val_mul a b

/--
Exponentiation in a cyclic group is bijective
-/
theorem exp_bijective {G : Type*} [Group G] [Fintype G]
    (g : G) (hg : IsGenerator G g) :
    Function.Bijective fun (x : ZMod (Nat.card G))↦ g ^ x.val := by
  constructor
  · simp [Function.Injective]
    intro a₁ a₂ h
    rw [← ZMod.natCast_zmod_val a₁, ← ZMod.natCast_zmod_val a₂, ZMod.natCast_eq_natCast_iff]
    have : a₁.val ≡ a₂.val [MOD orderOf g] := pow_eq_pow_iff_modEq.mp h
    rw [g_order g hg] at this
    exact this
  simp [Function.Surjective]
  intro b
  rcases hg b with ⟨z, rfl⟩
  dsimp
  use (z : ZMod (Nat.card G))
  rw [← zpow_natCast g (z : ZMod (Nat.card G)).val, ZMod.val_intCast z]
  rw [← zpow_mod_orderOf g z, g_order g hg]

end Group

end Group
