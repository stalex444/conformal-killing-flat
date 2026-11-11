module
public import Mathlib
public import ConformalKillingFlat

@[expose] public section
/-!
# Conformal Killing fields of flat space: proofs of the compared statements

Each of the nine statements of `Challenge.lean` is proved here, with the identical statement and
the identical definitions, by transfer from the proof library (`ConformalKillingFlat.lean` and
the modules under `ConformalKillingFlat/`, namespace `ConformalKillingFlat`).

The definitions carried by `Challenge.lean` (namespace `FlatConformalKilling`) are repeated here
verbatim. Each has the same body as the library's definition of the same name, so the two unfold
to the same term: the section "The carried definitions are the library's" records this by `rfl`,
and each compared statement is closed by the library theorem directly.

* Statement 1: `ConformalKillingFlat.isConformalKilling_iff` (`Rigidity`). The members of the
  family are conformal Killing by a direct computation of their derivatives
  (`isConformalKilling_family`). Conversely, for a `C³` solution the second derivatives of `ω`
  are determined by the first derivatives of the conformal factor `φ` (`second_deriv`); the
  symmetry of third derivatives then gives an algebraic identity on the Hessian of `φ`, which
  forces the Hessian to vanish when `n ≥ 3` (`hessian_eq_zero_of_identity`, `hessian_phi_eq_zero`).
  So `φ` is affine, and `ω` agrees with the member of the family having the same value, first
  derivative and conformal-factor gradient at the origin (`IsConformalKilling.eq_family`).
* Statement 2: `ConformalKillingFlat.isKilling_iff` (`Killing`). With `φ = 0` the same
  second-derivative formula shows that the first derivatives of `ω` are constant
  (`IsKilling.partialD_eq`), in every dimension.
* Statement 3: `ConformalKillingFlat.finite_conformalKilling` and
  `ConformalKillingFlat.finrank_conformalKilling` (`Dimension`). The parametrization of the
  family by `ℝⁿ × skew n × ℝ × ℝⁿ` is linear and injective, and by statement 1 its range is the
  space of conformal Killing fields (`paramEquiv`); the antisymmetric matrices have dimension
  `n (n − 1)/2` (`finrank_skew`).
* Statement 4: `ConformalKillingFlat.finite_killing` and `ConformalKillingFlat.finrank_killing`
  (`Dimension`), in the same way from statement 2 (`paramEquivK`).
* Statement 5: `ConformalKillingFlat.exists_conformalKilling_two_not_family` (`Control`). The
  witness is `(Re z³, Im z³)`; it is cubic along the first axis, where `family η a A lam b` is a
  polynomial of degree at most two for every real matrix `A`, antisymmetric or not
  (`cubicField_ne_family`).
* Statement 6: `ConformalKillingFlat.div_current_of_conformal` (`Current`): the product rule
  (`div_current`), and the fact that a symmetric matrix pairs only with the symmetric part of
  `∂ω` (`sum_sym_mul_of_conformal`).
* Statement 7: `ConformalKillingFlat.currents_conserved_iff_conformalKilling` (`Current`). From
  the equation to conserved currents: statement 6. Conversely, the constant tensor fields
  `E_ij + E_ji` (`i ≠ j`) and `η_j E_ii − η_i E_jj` are symmetric, divergence-free and
  `η`-trace-free, and their currents have divergence `∂_i ω_j + ∂_j ω_i` and
  `η_j ∂_i ω_i − η_i ∂_j ω_j`.
* Statement 8: `ConformalKillingFlat.currents_conserved_iff_killing` (`Current`), with the
  constant tensor fields `E_ij + E_ji` for all `i`, `j`.
* Statement 9: `ConformalKillingFlat.dilation_isConformalKilling_not_isKilling` (`Current`): the
  derivative of the dilation is `∂_i ω_j = η_ij`, so the conformal factor is `1`.
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

/-! ### The carried definitions are the library's -/

theorem isSignature_iff {n : ℕ} (η : Vec n) :
    IsSignature η ↔ ConformalKillingFlat.IsSignature η := Iff.rfl

theorem partialD_eq {n : ℕ} (ω : Vec n → Vec n) (x : Vec n) (i j : Fin n) :
    partialD ω x i j = ConformalKillingFlat.partialD ω x i j := rfl

theorem isConformalKilling_iff {n : ℕ} (η : Vec n) (ω : Vec n → Vec n) :
    IsConformalKilling η ω ↔ ConformalKillingFlat.IsConformalKilling η ω := Iff.rfl

theorem isKilling_iff {n : ℕ} (ω : Vec n → Vec n) :
    IsKilling ω ↔ ConformalKillingFlat.IsKilling ω := Iff.rfl

theorem family_eq {n : ℕ} (η a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n) :
    family η a A lam b = ConformalKillingFlat.family η a A lam b := rfl

theorem conformalKilling_eq {n : ℕ} (η : Vec n) :
    conformalKilling η = ConformalKillingFlat.conformalKilling η := rfl

theorem killing_eq {n : ℕ} : killing (n := n) = ConformalKillingFlat.killing := rfl

theorem divT_eq {n : ℕ} (T : Vec n → Tens n) (x : Vec n) (j : Fin n) :
    divT T x j = ConformalKillingFlat.divT T x j := rfl

theorem current_eq {n : ℕ} (T : Vec n → Tens n) (ω : Vec n → Vec n) :
    current T ω = ConformalKillingFlat.current T ω := rfl

theorem divJ_eq {n : ℕ} (J : Vec n → Vec n) (x : Vec n) :
    divJ J x = ConformalKillingFlat.divJ J x := rfl

theorem traceEta_eq {n : ℕ} (η : Vec n) (M : Tens n) :
    traceEta η M = ConformalKillingFlat.traceEta η M := rfl

/-! ### Classification -/

/-- **1. Classification of the conformal Killing fields, `n ≥ 3`.** For `n ≥ 3` and a diagonal
metric with entries `±1`, a covector field is conformal Killing (`C³`, with
`∂_i ω_j + ∂_j ω_i = 2 φ η_ij` for some function `φ`) if and only if it is a member of the
explicit family with an antisymmetric matrix `A`: translations, rotations, the dilation and
special conformal fields. -/
theorem conformalKilling_iff_family {n : ℕ} (η : Vec n) (hη : IsSignature η) (hn : 3 ≤ n)
    (ω : Vec n → Vec n) :
    IsConformalKilling η ω ↔ ∃ (a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n),
      A.transpose = -A ∧ ω = family η a A lam b :=
  ConformalKillingFlat.isConformalKilling_iff η hη hn ω

/-- **2. Classification of the Killing fields, every dimension.** A covector field on `ℝⁿ` is
Killing (`C³`, with `∂_i ω_j + ∂_j ω_i = 0`) if and only if it is affine,
`ω_j(x) = a_j + Σ_i A_ij x_i`, with `A` antisymmetric. -/
theorem killing_iff_affine {n : ℕ} (ω : Vec n → Vec n) :
    IsKilling ω ↔ ∃ (a : Vec n) (A : Tens n), A.transpose = -A ∧
      ∀ x j, ω x j = a j + ∑ i, A i j * x i :=
  ConformalKillingFlat.isKilling_iff ω

/-- **3. Dimension of the space of conformal Killing fields, `n ≥ 3`.** For `n ≥ 3` and a
diagonal metric with entries `±1`, the conformal Killing fields form a finite-dimensional real
vector space, of dimension `(n + 1)(n + 2)/2`. (The product `(n + 1)(n + 2)` is even, so the
division of natural numbers is exact.) -/
theorem finrank_conformalKilling {n : ℕ} (η : Vec n) (hη : IsSignature η) (hn : 3 ≤ n) :
    Module.Finite ℝ (conformalKilling η) ∧
      Module.finrank ℝ (conformalKilling η) = (n + 1) * (n + 2) / 2 :=
  ⟨ConformalKillingFlat.finite_conformalKilling η hη hn,
    ConformalKillingFlat.finrank_conformalKilling η hη hn⟩

/-- **4. Dimension of the space of Killing fields, every dimension.** The Killing fields on `ℝⁿ`
form a finite-dimensional real vector space, of dimension `n (n + 1)/2`. (The product
`n (n + 1)` is even, so the division of natural numbers is exact.) -/
theorem finrank_killing (n : ℕ) :
    Module.Finite ℝ (killing (n := n)) ∧
      Module.finrank ℝ (killing (n := n)) = n * (n + 1) / 2 :=
  ⟨ConformalKillingFlat.finite_killing, ConformalKillingFlat.finrank_killing⟩

/-- **5. Control: the Euclidean plane.** In dimension two with the Euclidean metric `η = (1, 1)`
there is a conformal Killing field that is not `family η a A lam b` for any `a`, `A`, `lam`, `b`,
where `A` is any real matrix, antisymmetric or not. So the hypothesis `3 ≤ n` of statement 1
cannot be replaced by `2 ≤ n`. -/
theorem plane_conformalKilling_not_family :
    ∃ ω : Vec 2 → Vec 2, IsConformalKilling (fun _ => (1 : ℝ)) ω ∧
      ¬ ∃ (a : Vec 2) (A : Tens 2) (lam : ℝ) (b : Vec 2),
        ω = family (fun _ => (1 : ℝ)) a A lam b :=
  ConformalKillingFlat.exists_conformalKilling_two_not_family

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
    divJ (current T ω) x = ∑ j, divT T x j * ω x j + φ * traceEta η (T x) :=
  ConformalKillingFlat.div_current_of_conformal η T ω x φ hT hω hsym hck

/-- **7. Conserved currents characterize conformal Killing fields.** Among `C³` covector fields,
`ω` is conformal Killing for `η` if and only if the current `T·ω` is divergence-free for every
differentiable tensor field `T` that is symmetric, divergence-free and `η`-trace-free. Constant
tensor fields are admitted. -/
theorem currents_conserved_iff_conformalKilling {n : ℕ} (η : Vec n)
    (ω : Vec n → Vec n) (hω : ContDiff ℝ 3 ω) :
    (∀ T : Vec n → Tens n, Differentiable ℝ T → (∀ x, (T x).transpose = T x) →
        (∀ x j, divT T x j = 0) → (∀ x, traceEta η (T x) = 0) →
        ∀ x, divJ (current T ω) x = 0) ↔ IsConformalKilling η ω :=
  ConformalKillingFlat.currents_conserved_iff_conformalKilling η ω hω

/-- **8. Conserved currents characterize Killing fields.** Among `C³` covector fields, `ω` is
Killing if and only if the current `T·ω` is divergence-free for every differentiable tensor
field `T` that is symmetric and divergence-free. Constant tensor fields are admitted. -/
theorem currents_conserved_iff_killing {n : ℕ} (ω : Vec n → Vec n) (hω : ContDiff ℝ 3 ω) :
    (∀ T : Vec n → Tens n, Differentiable ℝ T → (∀ x, (T x).transpose = T x) →
        (∀ x j, divT T x j = 0) → ∀ x, divJ (current T ω) x = 0) ↔ IsKilling ω :=
  ConformalKillingFlat.currents_conserved_iff_killing ω hω

/-- **9. The dilation is conformal Killing and not Killing.** For `n ≥ 1` and a diagonal metric
with entries `±1`, the field `ω_j(x) = η_j x_j` is conformal Killing and is not Killing. -/
theorem dilation_conformalKilling_not_killing {n : ℕ} (η : Vec n) (hη : IsSignature η)
    (hn : 1 ≤ n) :
    IsConformalKilling η (fun x j => η j * x j) ∧ ¬ IsKilling (fun x j => η j * x j) :=
  ConformalKillingFlat.dilation_isConformalKilling_not_isKilling η hη hn

end

end FlatConformalKilling
