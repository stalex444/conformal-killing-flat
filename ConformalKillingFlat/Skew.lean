module
public import ConformalKillingFlat.Defs

@[expose] public section
/-!
# The space of antisymmetric `n × n` real matrices has dimension `n (n - 1) / 2`

`skew n` is the underlying submodule of Mathlib's `LieAlgebra.Orthogonal.so (Fin n) ℝ`
(`skew_eq_so`).
-/

namespace ConformalKillingFlat

noncomputable section

variable {n : ℕ}

/-- The antisymmetric `n × n` real matrices. -/
def skew (n : ℕ) : Submodule ℝ (Tens n) where
  carrier := {A | A.transpose = -A}
  add_mem' := by
    intro A B hA hB
    have hA' : A.transpose = -A := hA
    have hB' : B.transpose = -B := hB
    show (A + B).transpose = -(A + B)
    rw [Matrix.transpose_add, hA', hB', neg_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c A hA
    have hA' : A.transpose = -A := hA
    show (c • A).transpose = -(c • A)
    rw [Matrix.transpose_smul, hA', smul_neg]

theorem mem_skew {A : Tens n} : A ∈ skew n ↔ A.transpose = -A := Iff.rfl

section Bridge

attribute [local instance 100] LieRing.ofAssociativeRing

/-- `skew n` is the underlying submodule of Mathlib's Lie algebra `so(n, ℝ)`
(`LieAlgebra.Orthogonal.so (Fin n) ℝ`). Only the underlying real vector space is used in this
development; no bracket enters. -/
theorem skew_eq_so (n : ℕ) : skew n = (LieAlgebra.Orthogonal.so (Fin n) ℝ).toSubmodule := by
  ext A
  exact (LieAlgebra.Orthogonal.mem_so (Fin n) ℝ A).symm

end Bridge

/-- The index pairs strictly above the diagonal. -/
abbrev UpperPairs (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The antisymmetric matrix with prescribed entries above the diagonal. -/
def skewOf (c : UpperPairs n → ℝ) : Tens n :=
  fun i j => if h : i < j then c ⟨(i, j), h⟩ else if h' : j < i then -c ⟨(j, i), h'⟩ else 0

theorem skewOf_of_lt (c : UpperPairs n → ℝ) {i j : Fin n} (h : i < j) :
    skewOf c i j = c ⟨(i, j), h⟩ := by
  simp [skewOf, h]

theorem skewOf_of_gt (c : UpperPairs n → ℝ) {i j : Fin n} (h : j < i) :
    skewOf c i j = -c ⟨(j, i), h⟩ := by
  simp [skewOf, h, not_lt_of_gt h]

theorem skewOf_self (c : UpperPairs n → ℝ) (i : Fin n) : skewOf c i i = 0 := by
  simp [skewOf]

theorem skewOf_transpose (c : UpperPairs n → ℝ) : (skewOf c).transpose = -skewOf c := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [skewOf_of_gt c h, skewOf_of_lt c h]
  · subst h
    rw [skewOf_self, neg_zero]
  · rw [skewOf_of_lt c h, skewOf_of_gt c h, neg_neg]

/-- Antisymmetric matrices are determined by their entries above the diagonal. -/
def skewEquiv (n : ℕ) : skew n ≃ₗ[ℝ] (UpperPairs n → ℝ) where
  toFun A := fun p => (A : Tens n) p.1.1 p.1.2
  map_add' A B := rfl
  map_smul' c A := rfl
  invFun c := ⟨skewOf c, skewOf_transpose c⟩
  left_inv := by
    rintro ⟨A, hA⟩
    have hA' : ∀ i j, A j i = -A i j := fun i j => congrFun (congrFun hA i) j
    apply Subtype.ext
    ext i j
    show skewOf (fun p : UpperPairs n => A p.1.1 p.1.2) i j = A i j
    rcases lt_trichotomy i j with h | h | h
    · rw [skewOf_of_lt _ h]
    · subst h
      rw [skewOf_self]
      linarith [hA' i i]
    · rw [skewOf_of_gt _ h]
      linarith [hA' j i]
  right_inv := by
    intro c
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    exact skewOf_of_lt c h

theorem card_upperPairs (n : ℕ) : Fintype.card (UpperPairs n) = n * (n - 1) / 2 := by
  rw [Fintype.card_subtype, ← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) n,
    Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.card_filter]
  have e : (Finset.univ.filter fun i : Fin n => i < j) = Finset.Iio j := by
    ext i
    simp
  rw [e, Fin.card_Iio]

/-- The antisymmetric `n × n` real matrices form a space of dimension `n (n - 1) / 2`. -/
theorem finrank_skew (n : ℕ) : Module.finrank ℝ (skew n) = n * (n - 1) / 2 := by
  rw [LinearEquiv.finrank_eq (skewEquiv n), Module.finrank_fintype_fun_eq_card, card_upperPairs]

end

end ConformalKillingFlat
