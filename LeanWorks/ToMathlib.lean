import Mathlib.Tactic

/-!
General lemmas that could be ported to Mathlib, maybe...
-/

section Bijection

-- the n-fold product of a type
def nfoldProd.{u} (α : Type u) : ℕ → Type u
  | 0     => PUnit
  | 1     => α
  | n + 2 => α × nfoldProd α (n + 1)

-- applying a function `f` coordinate-wise on an n-tuple
def nfoldMap.{u,v} {α : Type u} {β : Type v} (f : α → β) : (n : ℕ) → nfoldProd α n → nfoldProd β n
  | 0, _       => PUnit.unit
  | 1, x       => f x
  | n + 2, (x, xs) => (f x, nfoldMap f (n + 1) xs)

variable {α β : Type} {f : α → β}

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
  have : g y = g y ↔ y = f (g y) := by exact iff_comm.mp (hg (g y) y)
  tauto

theorem Function.bijective_nfold (n : ℕ) (hf : Function.Bijective f) :
    Function.Bijective (nfoldMap f n) := by
  apply (Function.bijective_iff_existsUnique (nfoldMap f n)).mpr
  cases n with
    | zero =>
      exact fun b ↦ existsUnique_eq
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

section ENNRealCast

theorem ENNReal.mul_natCast {a b : ℕ} : (a : ENNReal) * (b : ENNReal) = (↑(a * b) : ENNReal) := by
  exact Eq.symm (Nat.cast_mul a b)

theorem ENNReal.mul_inv_natCast {a b : ℕ} :
    ((a : ENNReal) * (b : ENNReal))⁻¹ = (a : ENNReal)⁻¹ * (b : ENNReal)⁻¹ := by
  apply ENNReal.mul_inv
  · right
    exact ENNReal.natCast_ne_top b
  left
  exact ENNReal.natCast_ne_top a

end ENNRealCast
