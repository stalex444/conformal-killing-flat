module
public import Mathlib

@[expose] public section
/-!
# Conformal Killing fields of flat pseudo-Euclidean space: shared definitions

Covector fields `ω : ℝⁿ → ℝⁿ` on `ℝⁿ` with a diagonal metric `η` whose entries are `±1`
(every signature). `Challenge.lean` carries its own copy of these definitions (in the namespace
`FlatConformalKilling`), since it imports Mathlib only; `Solution.lean` identifies the two copies.
-/

namespace ConformalKillingFlat

noncomputable section

/-- Points (and covectors) of `ℝⁿ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- `n × n` real matrices: tensors at a point. -/
abbrev Tens (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

/-- A diagonal metric of arbitrary signature: every entry is `1` or `-1`. -/
def IsSignature (η : Vec n) : Prop := ∀ i, η i = 1 ∨ η i = -1

/-- `∂_i ω_j` at `x`. -/
def partialD (ω : Vec n → Vec n) (x : Vec n) (i j : Fin n) : ℝ :=
  fderiv ℝ ω x (Pi.single i 1) j

/-- The conformal Killing equation `∂_i ω_j + ∂_j ω_i = 2 φ η_ij` for a `C³` covector field. -/
def IsConformalKilling (η : Vec n) (ω : Vec n → Vec n) : Prop :=
  ContDiff ℝ 3 ω ∧ ∃ φ : Vec n → ℝ, ∀ x i j,
    partialD ω x i j + partialD ω x j i = 2 * φ x * (if i = j then η i else 0)

/-- The Killing equation `∂_i ω_j + ∂_j ω_i = 0` for a `C³` covector field. -/
def IsKilling (ω : Vec n → Vec n) : Prop :=
  ContDiff ℝ 3 ω ∧ ∀ x i j, partialD ω x i j + partialD ω x j i = 0

/-- The explicit family: translations `a`, rotations `A` (antisymmetric in the classification; the definition
allows any real matrix), the dilation
`lam`, and special conformal fields `b`. -/
def family (η : Vec n) (a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n) : Vec n → Vec n :=
  fun x j => a j + ∑ i, A i j * x i + lam * η j * x j
    + (2 * (∑ i, b i * x i) * η j * x j - b j * ∑ i, η i * x i ^ 2)

end

end ConformalKillingFlat
