module
public import Mathlib

@[expose] public section
/-!
# Conformal Killing fields of flat space: classification, dimension, conserved currents

On `ℝⁿ` with a diagonal metric `η` whose entries are `±1`, a covector field `ω` is *conformal
Killing* when it is `C³` and `∂_i ω_j + ∂_j ω_i = 2 φ η_ij` for some function `φ`, and *Killing*
when it is `C³` and `∂_i ω_j + ∂_j ω_i = 0`. For `n ≥ 3` and every signature the conformal
Killing fields are exactly the sums of a translation, a rotation, a multiple of the dilation and
a special conformal field, and they form a real vector space of dimension `(n + 1)(n + 2)/2`; in
every dimension the Killing fields are exactly the sums of a translation and a rotation, a space
of dimension `n (n + 1)/2`. For a conformal Killing field `ω` with factor `φ`, the current `T·ω`
of a differentiable symmetric tensor field `T` satisfies
`div (T·ω) = (div T)·ω + φ · tr_η T`, and conservation of these currents characterizes the two
classes of fields.
This entry compares exactly these nine statements.
Statements 1–4 are classical. Statements 1 and 3 are the classification of the conformal Killing
fields of `ℝ^{p,q}` for `p + q ≥ 3` and the count of their parameters (M. Schottenloher, *A
Mathematical Introduction to Conformal Field Theory*, 2nd ed., 2008, Theorem 1.7; P. Ginsparg,
*Applied Conformal Field Theory* (Les Houches 1988), arXiv:hep-th/9108028, §1.1); they are the
infinitesimal counterpart of Liouville's theorem on conformal maps. Statements 2 and 4 are the
Killing fields of flat space and their number (Schottenloher, §1.4.1; M. Blau, *Lecture Notes on
General Relativity*, (9.81)–(9.82) and (14.4)). Statement 6 is the standard identity behind the
conserved currents of a trace-free stress tensor (Blau, §10.2, (10.14)–(10.16), the computation
displayed in (10.16) on a general metric, for a conserved trace-free `T`; Ginsparg, §2.2, the trace
term printed in two dimensions, for a conserved `T`; D. Simmons-Duffin, *TASI Lectures on the
Conformal Bootstrap*, arXiv:1602.07982 (published as *The Conformal Bootstrap*), (18)–(23), the
product rule for a conserved `T`, without the trace term). Statements 5 and 9 are standard examples:
in the Euclidean plane the conformal Killing fields are the holomorphic functions (Schottenloher,
§1.4.2), and the dilation has a constant nonzero conformal factor. In statements 7 and 8 the
direction from the equation to conserved currents is statement 6. The direction from conserved
currents to the equation was not found stated in the sources read for this entry; it is elementary,
it is proved here by testing on constant tensor fields, and it is not claimed as new. No statement
here is claimed as a new theorem.

Conventions. Points of `ℝⁿ` and covectors are functions `Fin n → ℝ` (`Vec n`); a field is a
function `ω : Vec n → Vec n`, read as the covector field with components `ω_j`. The partial
derivative `∂_i ω_j` at `x` is `partialD ω x i j = fderiv ℝ ω x (Pi.single i 1) j`: the
derivative in the `i`-th coordinate direction of the `j`-th component. The metric is a function
`η : Vec n`, read as the diagonal matrix with entries `η i`, so `η_ij` is `η i` if `i = j` and `0`
otherwise; `IsSignature η` says every entry is `1` or `-1`. Both `IsConformalKilling η ω` and
`IsKilling ω` include the hypothesis that `ω` is `C³`. A tensor at a point is an `n × n` real
matrix (`Tens n`), a tensor field is a function `T : Vec n → Tens n`, and differentiability of a
tensor field is differentiability of each entry. For a tensor field `T` and a field `ω`:
`divT T x j = Σ_i ∂_i T^{ij}`, `current T ω x i = Σ_j T^{ij} ω_j`, `divJ J x = Σ_i ∂_i J^i`, and
`traceEta η M = Σ_i η_i M^{ii}`.

Classification (statements 1–5):

1. `conformalKilling_iff_family` — for `n ≥ 3` and every signature, `ω` is conformal Killing if
   and only if `ω = family η a A lam b` for some `a`, `b` in `ℝⁿ`, a real number `lam` and an
   antisymmetric matrix `A`, where
   `family η a A lam b x j = a_j + Σ_i A_ij x_i + lam η_j x_j + 2 (b·x) η_j x_j − b_j Σ_i η_i x_i²`
   (translations `a`, rotations `A`, the dilation `lam`, special conformal fields `b`).
2. `killing_iff_affine` — in every dimension, `ω` is Killing if and only if
   `ω x j = a_j + Σ_i A_ij x_i` for some `a` in `ℝⁿ` and an antisymmetric matrix `A`. No metric
   enters.
3. `finrank_conformalKilling` — for `n ≥ 3` and every signature, the conformal Killing fields
   form a finite-dimensional real vector space of dimension `(n + 1)(n + 2)/2`.
4. `finrank_killing` — in every dimension, the Killing fields form a finite-dimensional real
   vector space of dimension `n (n + 1)/2`.
5. `plane_conformalKilling_not_family` — a control for the hypothesis `n ≥ 3` of statement 1: in
   the Euclidean plane, `η = (1, 1)`, there is a conformal Killing field that is not
   `family η a A lam b` for any `a`, `A`, `lam`, `b`; here `A` is any real matrix, antisymmetric
   or not. The witness in the proof is the real and imaginary parts of `z³`.

Conserved currents: which fields give them (statements 6–9):

6. `div_current_of_conformal` — if `T` and `ω` are differentiable at `x`, `T x` is symmetric and
   `∂_i ω_j + ∂_j ω_i = 2 φ η_ij` at `x`, then
   `div (T·ω) = Σ_j (div T)^j ω_j + φ · tr_η T` at `x`. No hypothesis on `η`.
7. `currents_conserved_iff_conformalKilling` — a `C³` field `ω` is conformal Killing if and only
   if the current `T·ω` is divergence-free for every differentiable, symmetric, divergence-free,
   `η`-trace-free tensor field `T`. No hypothesis on `η`.
8. `currents_conserved_iff_killing` — a `C³` field `ω` is Killing if and only if the current
   `T·ω` is divergence-free for every differentiable, symmetric, divergence-free tensor field `T`.
9. `dilation_conformalKilling_not_killing` — for `n ≥ 1` and every signature, the dilation field
   `ω_j = η_j x_j` is conformal Killing and is not Killing.

Scope.
* The metric is diagonal with entries `±1`. A general nondegenerate constant metric is reached by
  a linear change of coordinates, which is not formalized.
* The solutions are `C³`, as part of the definitions; `conformalKilling η` and `killing` are the
  spaces of `C³` solutions. Nothing is claimed about solutions of lower regularity.
* The fields are covector fields `ω_j`. The vector field is `ξ^i = η_i ω_i`; the statements are
  not restated for it.
* The numbers in statements 3 and 4 are dimensions of real vector spaces (`Module.finrank`, with
  finite-dimensionality stated alongside). No Lie bracket is defined and no isomorphism with an
  orthogonal Lie algebra is stated.
* In statements 7 and 8 the tensor fields range over all differentiable fields with the stated
  properties (symmetric and divergence-free, and `η`-trace-free in statement 7); constant tensor
  fields are admitted and already suffice for the directions from conserved currents to the
  equation, which are therefore pointwise facts of linear algebra. Nothing is said about compactly
  supported tensor fields. None of statements 6–9 depends on statements 1–5; statements 6–8 hold
  in every dimension and statement 9 for `n ≥ 1`.
* Statement 7 has content from `n = 2` on: for `n ≤ 1` and a metric with entries `±1`, both sides
  hold for every `C³` field. Statement 8 has content from `n = 1` on.
* Statement 5 is a single example in the Euclidean plane. It excludes `family η a A lam b` for
  every real matrix `A`, which is stronger than a control restricted to the antisymmetric `A` of
  statement 1. No compared statement tests the hypothesis `n ≥ 3` of statement 3.

Prior formalization (search of 2026-11-11). The identity of statement 6 is formalized for `n = 4`
and signature `(1,3)` in `github.com/openai/math`; special cases of the currents, and Killing
fields on Riemannian manifolds, are in three other Lean developments. No formalization of
statements 1–5, or of the direction of statements 7 and 8 from conserved currents to the
equation, was found. This is a dated search, not a claim of priority; `README.md`, section "Prior
formalization", names the files and commits, where the search looked and what it could not search.

Not formalized. The list is in `README.md`, section "Not formalized"; beyond the scope above it
names fields on proper open subsets, the passage from conformal flows to the equation, the
Liouville theorem on finite conformal maps, and dimension two beyond the examples.

Sources and proof. The proofs were written from a plan of the classical integrability argument,
not from the text of one source; `README.md`, sections "The proofs" and "Relation to the
literature", compares them with the sources, and `formalization.yaml` records how each was read.

Application (cited; no compared statement asserts it). For `n = 4` and a Lorentzian signature,
the space of statement 3 has dimension 15 and is the space of infinitesimal conformal symmetries
of Minkowski space, and the space of statement 4 has dimension 10 and is the space of its
infinitesimal isometries, the Poincaré generators (Blau, §10.3). Statement 6 is the conservation
law used for them in field theory: the current of a conserved, symmetric stress tensor against a
Killing field is conserved, and against a conformal Killing field it is conserved when the
stress tensor is also trace-free (Blau, §§10.1–10.2), as the Maxwell stress tensor is for `n = 4`
(Blau, (7.122)).

Every statement here is left unproved as a placeholder; `Solution.lean` proves each, with the
identical statement and the identical definitions.
-/

namespace FlatConformalKilling

noncomputable section

/-! ### Definitions -/

/-- Points of `ℝⁿ`, and covectors at a point: functions `Fin n → ℝ`. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- Tensors at a point: `n × n` real matrices. A tensor field is a function `Vec n → Tens n`. -/
abbrev Tens (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A diagonal metric of arbitrary signature: `η` is read as the diagonal matrix with entries
`η i`, and every entry is `1` or `-1`. -/
def IsSignature {n : ℕ} (η : Vec n) : Prop := ∀ i, η i = 1 ∨ η i = -1

/-- `∂_i ω_j` at `x`: the derivative in the `i`-th coordinate direction of the `j`-th component
of the covector field `ω`. -/
def partialD {n : ℕ} (ω : Vec n → Vec n) (x : Vec n) (i j : Fin n) : ℝ :=
  fderiv ℝ ω x (Pi.single i 1) j

/-- The covector field `ω` is conformal Killing for the diagonal metric `η`: it is `C³` and
`∂_i ω_j + ∂_j ω_i = 2 φ η_ij` everywhere, for some function `φ` (the conformal factor). -/
def IsConformalKilling {n : ℕ} (η : Vec n) (ω : Vec n → Vec n) : Prop :=
  ContDiff ℝ 3 ω ∧ ∃ φ : Vec n → ℝ, ∀ x i j,
    partialD ω x i j + partialD ω x j i = 2 * φ x * (if i = j then η i else 0)

/-- The covector field `ω` is Killing: it is `C³` and `∂_i ω_j + ∂_j ω_i = 0` everywhere. In this
lowered-index form the equation does not involve the metric. -/
def IsKilling {n : ℕ} (ω : Vec n → Vec n) : Prop :=
  ContDiff ℝ 3 ω ∧ ∀ x i j, partialD ω x i j + partialD ω x j i = 0

/-- The explicit family, as covector fields:
`ω_j(x) = a_j + Σ_i A_ij x_i + lam η_j x_j + 2 (b·x) η_j x_j − b_j Σ_i η_i x_i²`.
Translations `a`, rotations `A` (antisymmetric in statement 1; statement 5 allows any real
matrix), the dilation `lam`, special conformal fields `b`. -/
def family {n : ℕ} (η : Vec n) (a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n) : Vec n → Vec n :=
  fun x j => a j + ∑ i, A i j * x i + lam * η j * x j
    + (2 * (∑ i, b i * x i) * η j * x j - b j * ∑ i, η i * x i ^ 2)

/-- The real vector space of conformal Killing fields of the metric `η`: the set of all `ω` with
`IsConformalKilling η ω`, with pointwise addition and scalar multiplication. The three proofs
show that the set is closed under addition, contains zero and is closed under scalar
multiplication. -/
def conformalKilling {n : ℕ} (η : Vec n) : Submodule ℝ (Vec n → Vec n) where
  carrier := {ω | IsConformalKilling η ω}
  add_mem' := by
    rintro ω₁ ω₂ ⟨h₁, φ₁, e₁⟩ ⟨h₂, φ₂, e₂⟩
    refine ⟨h₁.add h₂, fun x => φ₁ x + φ₂ x, fun x i j => ?_⟩
    have d₁ : DifferentiableAt ℝ ω₁ x := (h₁.differentiable (by norm_num)) x
    have d₂ : DifferentiableAt ℝ ω₂ x := (h₂.differentiable (by norm_num)) x
    have e : ∀ i j, partialD (ω₁ + ω₂) x i j = partialD ω₁ x i j + partialD ω₂ x i j := by
      intro i j
      unfold partialD
      rw [fderiv_add d₁ d₂]
      rfl
    rw [e, e]
    linear_combination e₁ x i j + e₂ x i j
  zero_mem' := by
    refine ⟨contDiff_const, fun _ => 0, fun x i j => ?_⟩
    simp [partialD]
  smul_mem' := by
    rintro c ω ⟨h, φ, e⟩
    refine ⟨h.const_smul c, fun x => c * φ x, fun x i j => ?_⟩
    have d : DifferentiableAt ℝ ω x := (h.differentiable (by norm_num)) x
    have e' : ∀ i j, partialD (c • ω) x i j = c * partialD ω x i j := by
      intro i j
      unfold partialD
      rw [fderiv_const_smul d c]
      rfl
    rw [e', e']
    linear_combination c * e x i j

/-- The real vector space of Killing fields on `ℝⁿ`: the set of all `ω` with `IsKilling ω`, with
pointwise addition and scalar multiplication. The three proofs show that the set is closed under
addition, contains zero and is closed under scalar multiplication. -/
def killing {n : ℕ} : Submodule ℝ (Vec n → Vec n) where
  carrier := {ω | IsKilling ω}
  add_mem' := by
    rintro ω₁ ω₂ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    refine ⟨h₁.add h₂, fun x i j => ?_⟩
    have d₁ : DifferentiableAt ℝ ω₁ x := (h₁.differentiable (by norm_num)) x
    have d₂ : DifferentiableAt ℝ ω₂ x := (h₂.differentiable (by norm_num)) x
    have e : ∀ i j, partialD (ω₁ + ω₂) x i j = partialD ω₁ x i j + partialD ω₂ x i j := by
      intro i j
      unfold partialD
      rw [fderiv_add d₁ d₂]
      rfl
    rw [e, e]
    linear_combination e₁ x i j + e₂ x i j
  zero_mem' := by
    refine ⟨contDiff_const, fun x i j => ?_⟩
    simp [partialD]
  smul_mem' := by
    rintro c ω ⟨h, e⟩
    refine ⟨h.const_smul c, fun x i j => ?_⟩
    have d : DifferentiableAt ℝ ω x := (h.differentiable (by norm_num)) x
    have e' : ∀ i j, partialD (c • ω) x i j = c * partialD ω x i j := by
      intro i j
      unfold partialD
      rw [fderiv_const_smul d c]
      rfl
    rw [e', e']
    linear_combination c * e x i j

/-- The divergence of a tensor field on its first index: `(div T)^j = Σ_i ∂_i T^{ij}` at `x`. -/
def divT {n : ℕ} (T : Vec n → Tens n) (x : Vec n) (j : Fin n) : ℝ :=
  ∑ i, fderiv ℝ (fun y => T y i j) x (Pi.single i 1)

/-- The current of a tensor field against a covector field: `J^i = Σ_j T^{ij} ω_j`. -/
def current {n : ℕ} (T : Vec n → Tens n) (ω : Vec n → Vec n) : Vec n → Vec n :=
  fun x i => ∑ j, T x i j * ω x j

/-- The divergence of a current: `div J = Σ_i ∂_i J^i` at `x`. -/
def divJ {n : ℕ} (J : Vec n → Vec n) (x : Vec n) : ℝ :=
  ∑ i, fderiv ℝ (fun y => J y i) x (Pi.single i 1)

/-- The metric trace of a tensor: `tr_η M = Σ_i η_i M^{ii}`. -/
def traceEta {n : ℕ} (η : Vec n) (M : Tens n) : ℝ := ∑ i, η i * M i i

/-! ### Classification -/

/-- **1. Classification of the conformal Killing fields, `n ≥ 3`.** For `n ≥ 3` and a diagonal
metric with entries `±1`, a covector field is conformal Killing (`C³`, with
`∂_i ω_j + ∂_j ω_i = 2 φ η_ij` for some function `φ`) if and only if it is a member of the
explicit family with an antisymmetric matrix `A`: translations, rotations, the dilation and
special conformal fields. -/
theorem conformalKilling_iff_family {n : ℕ} (η : Vec n) (hη : IsSignature η) (hn : 3 ≤ n)
    (ω : Vec n → Vec n) :
    IsConformalKilling η ω ↔ ∃ (a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n),
      A.transpose = -A ∧ ω = family η a A lam b := by
  sorry

/-- **2. Classification of the Killing fields, every dimension.** A covector field on `ℝⁿ` is
Killing (`C³`, with `∂_i ω_j + ∂_j ω_i = 0`) if and only if it is affine,
`ω_j(x) = a_j + Σ_i A_ij x_i`, with `A` antisymmetric. -/
theorem killing_iff_affine {n : ℕ} (ω : Vec n → Vec n) :
    IsKilling ω ↔ ∃ (a : Vec n) (A : Tens n), A.transpose = -A ∧
      ∀ x j, ω x j = a j + ∑ i, A i j * x i := by
  sorry

/-- **3. Dimension of the space of conformal Killing fields, `n ≥ 3`.** For `n ≥ 3` and a
diagonal metric with entries `±1`, the conformal Killing fields form a finite-dimensional real
vector space, of dimension `(n + 1)(n + 2)/2`. (The product `(n + 1)(n + 2)` is even, so the
division of natural numbers is exact.) -/
theorem finrank_conformalKilling {n : ℕ} (η : Vec n) (hη : IsSignature η) (hn : 3 ≤ n) :
    Module.Finite ℝ (conformalKilling η) ∧
      Module.finrank ℝ (conformalKilling η) = (n + 1) * (n + 2) / 2 := by
  sorry

/-- **4. Dimension of the space of Killing fields, every dimension.** The Killing fields on `ℝⁿ`
form a finite-dimensional real vector space, of dimension `n (n + 1)/2`. (The product
`n (n + 1)` is even, so the division of natural numbers is exact.) -/
theorem finrank_killing (n : ℕ) :
    Module.Finite ℝ (killing (n := n)) ∧
      Module.finrank ℝ (killing (n := n)) = n * (n + 1) / 2 := by
  sorry

/-- **5. Control: the Euclidean plane.** In dimension two with the Euclidean metric `η = (1, 1)`
there is a conformal Killing field that is not `family η a A lam b` for any `a`, `A`, `lam`, `b`,
where `A` is any real matrix, antisymmetric or not. So the hypothesis `3 ≤ n` of statement 1
cannot be replaced by `2 ≤ n`. -/
theorem plane_conformalKilling_not_family :
    ∃ ω : Vec 2 → Vec 2, IsConformalKilling (fun _ => (1 : ℝ)) ω ∧
      ¬ ∃ (a : Vec 2) (A : Tens 2) (lam : ℝ) (b : Vec 2),
        ω = family (fun _ => (1 : ℝ)) a A lam b := by
  sorry

/-! ### Conserved currents of the classified fields -/

/-- **6. Divergence of the current of a symmetric tensor field.** If the tensor field `T` and
the covector field `ω` are differentiable at `x`, `T x` is symmetric, and
`∂_i ω_j + ∂_j ω_i = 2 φ η_ij` at `x`, then at `x`
`div (T·ω) = Σ_j (div T)^j ω_j + φ · tr_η T`. -/
theorem div_current_of_conformal {n : ℕ} (η : Vec n) (T : Vec n → Tens n) (ω : Vec n → Vec n)
    (x : Vec n) (φ : ℝ)
    (hT : DifferentiableAt ℝ T x) (hω : DifferentiableAt ℝ ω x)
    (hsym : (T x).transpose = T x)
    (hck : ∀ i j, partialD ω x i j + partialD ω x j i
      = 2 * φ * (if i = j then η i else 0)) :
    divJ (current T ω) x = ∑ j, divT T x j * ω x j + φ * traceEta η (T x) := by
  sorry

/-- **7. Conserved currents characterize conformal Killing fields.** Among `C³` covector fields,
`ω` is conformal Killing for `η` if and only if the current `T·ω` is divergence-free for every
differentiable tensor field `T` that is symmetric, divergence-free and `η`-trace-free. Constant
tensor fields are admitted. -/
theorem currents_conserved_iff_conformalKilling {n : ℕ} (η : Vec n)
    (ω : Vec n → Vec n) (hω : ContDiff ℝ 3 ω) :
    (∀ T : Vec n → Tens n, Differentiable ℝ T → (∀ x, (T x).transpose = T x) →
        (∀ x j, divT T x j = 0) → (∀ x, traceEta η (T x) = 0) →
        ∀ x, divJ (current T ω) x = 0) ↔ IsConformalKilling η ω := by
  sorry

/-- **8. Conserved currents characterize Killing fields.** Among `C³` covector fields, `ω` is
Killing if and only if the current `T·ω` is divergence-free for every differentiable tensor
field `T` that is symmetric and divergence-free. Constant tensor fields are admitted. -/
theorem currents_conserved_iff_killing {n : ℕ} (ω : Vec n → Vec n) (hω : ContDiff ℝ 3 ω) :
    (∀ T : Vec n → Tens n, Differentiable ℝ T → (∀ x, (T x).transpose = T x) →
        (∀ x j, divT T x j = 0) → ∀ x, divJ (current T ω) x = 0) ↔ IsKilling ω := by
  sorry

/-- **9. The dilation is conformal Killing and not Killing.** For `n ≥ 1` and a diagonal metric
with entries `±1`, the field `ω_j(x) = η_j x_j` is conformal Killing and is not Killing. -/
theorem dilation_conformalKilling_not_killing {n : ℕ} (η : Vec n) (hη : IsSignature η)
    (hn : 1 ≤ n) :
    IsConformalKilling η (fun x j => η j * x j) ∧ ¬ IsKilling (fun x j => η j * x j) := by
  sorry

end

end FlatConformalKilling
