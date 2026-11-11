module
public import ConformalKillingFlat.Defs

@[expose] public section
/-!
# Currents of symmetric tensor fields on flat pseudo-Euclidean space

For a tensor field `T` and a covector field `ω` on `ℝⁿ` the current is `J^i = Σ_j T^{ij} ω_j`.

* `div_current`: `div J = Σ_j (div T)^j ω_j + Σ_{ij} T^{ij} ∂_i ω_j`.
* `div_current_of_conformal`: for symmetric `T` and `∂_i ω_j + ∂_j ω_i = 2 φ η_ij`,
  `div J = Σ_j (div T)^j ω_j + φ · tr_η T`.
* `currents_conserved_iff_conformalKilling`: among `C³` covector fields, a field is conformal
  Killing iff the current of every differentiable, symmetric, divergence-free, `η`-trace-free
  tensor field against it is conserved. No hypothesis on `η`.
* `currents_conserved_iff_killing`: among `C³` covector fields, a field is Killing iff the current
  of every differentiable, symmetric, divergence-free tensor field against it is conserved.
* `dilation_isConformalKilling_not_isKilling`: the dilation field separates the two classes in
  every dimension `n ≥ 1`.

The tensor fields in the two characterizations are all differentiable fields `T : ℝⁿ → Matrix`;
constant tensor fields are admitted and already suffice for the forward directions (conserved
currents imply the equation), which are therefore pointwise facts of linear algebra. Nothing is
said about compactly supported or decaying tensor fields. The conformal statement has content from
`n = 2` on (for `n ≤ 1` and a metric with entries `±1`, both sides hold for every `C³` field); the
Killing statement has content from `n = 1` on.
-/

namespace ConformalKillingFlat

noncomputable section

open Finset

variable {n : ℕ}

/-- `(div T)^j = Σ_i ∂_i T^{ij}`. -/
def divT (T : Vec n → Tens n) (x : Vec n) (j : Fin n) : ℝ :=
  ∑ i, fderiv ℝ (fun y => T y i j) x (Pi.single i 1)

/-- The current `J^i = Σ_j T^{ij} ω_j`. -/
def current (T : Vec n → Tens n) (ω : Vec n → Vec n) : Vec n → Vec n :=
  fun x i => ∑ j, T x i j * ω x j

/-- `div J = Σ_i ∂_i J^i`. -/
def divJ (J : Vec n → Vec n) (x : Vec n) : ℝ :=
  ∑ i, fderiv ℝ (fun y => J y i) x (Pi.single i 1)

/-- The metric trace `Σ_i η_i T^{ii}`. -/
def traceEta (η : Vec n) (M : Tens n) : ℝ := ∑ i, η i * M i i

/-! ### Differentiability of components -/

/-- The entries of a differentiable matrix-valued map are differentiable. -/
theorem differentiableAt_entry {T : Vec n → Tens n} {x : Vec n} (hT : DifferentiableAt ℝ T x)
    (i j : Fin n) : DifferentiableAt ℝ (fun y => T y i j) x := by
  have hT' : DifferentiableAt ℝ (fun y => (T y : Fin n → Fin n → ℝ)) x := hT
  exact differentiableAt_pi.1 (differentiableAt_pi.1 hT' i) j

/-- `∂_i ω_j` is the `i`-th partial derivative of the `j`-th component. -/
theorem partialD_eq {ω : Vec n → Vec n} {x : Vec n} (hω : DifferentiableAt ℝ ω x)
    (i j : Fin n) : partialD ω x i j = fderiv ℝ (fun y => ω y j) x (Pi.single i 1) := by
  rw [(hasFDerivAt_pi'.1 hω.hasFDerivAt j).fderiv]
  rfl

/-! ### The divergence of a current -/

/-- **Divergence of a current.** `div J = Σ_j (div T)^j ω_j + Σ_{ij} T^{ij} ∂_i ω_j`. -/
theorem div_current (T : Vec n → Tens n) (ω : Vec n → Vec n) (x : Vec n)
    (hT : DifferentiableAt ℝ T x) (hω : DifferentiableAt ℝ ω x) :
    divJ (current T ω) x
      = ∑ j, divT T x j * ω x j + ∑ i, ∑ j, T x i j * partialD ω x i j := by
  have key : ∀ i, fderiv ℝ (fun y => current T ω y i) x (Pi.single i 1)
      = ∑ j, (fderiv ℝ (fun y => T y i j) x (Pi.single i 1) * ω x j
          + T x i j * partialD ω x i j) := by
    intro i
    have hsum : HasFDerivAt (fun y => ∑ j, T y i j * ω y j)
        (∑ j, (T x i j • fderiv ℝ (fun y => ω y j) x
          + ω x j • fderiv ℝ (fun y => T y i j) x)) x :=
      HasFDerivAt.fun_sum fun j _ =>
        ((differentiableAt_entry hT i j).hasFDerivAt).mul
          ((differentiableAt_pi.1 hω j).hasFDerivAt)
    have h := hsum.fderiv
    unfold current
    rw [h, _root_.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [partialD_eq hω i j]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  unfold divJ
  rw [Finset.sum_congr rfl fun i _ => key i]
  simp only [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold divT
  rw [Finset.sum_mul]

/-- For a symmetric matrix `M`, only the symmetric part of `P` pairs with it. -/
theorem sum_sym_mul (M P : Tens n) (hM : M.transpose = M) :
    ∑ i, ∑ j, M i j * P i j = (1 / 2) * ∑ i, ∑ j, M i j * (P i j + P j i) := by
  have hM' : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.transpose_apply] using this
  have hswap : ∑ i, ∑ j, M i j * P j i = ∑ i, ∑ j, M i j * P i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM' i j]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hswap]
  ring

/-- A symmetric tensor paired with `φ` times the metric is `φ` times its metric trace. -/
theorem sum_sym_mul_of_conformal (η : Vec n) (M P : Tens n) (φ : ℝ) (hM : M.transpose = M)
    (hck : ∀ i j, P i j + P j i = 2 * φ * (if i = j then η i else 0)) :
    ∑ i, ∑ j, M i j * P i j = φ * traceEta η M := by
  rw [sum_sym_mul M P hM]
  have h : ∀ i, ∑ j, M i j * (P i j + P j i) = 2 * φ * (η i * M i i) := by
    intro i
    rw [Finset.sum_congr rfl fun j _ => by rw [hck i j]]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.mul_sum]
  unfold traceEta
  ring

/-- **Divergence of the current of a symmetric tensor against a conformal Killing covector.**
For symmetric `T` and `∂_i ω_j + ∂_j ω_i = 2 φ η_ij` at `x`,
`div J = Σ_j (div T)^j ω_j + φ · tr_η T`. -/
theorem div_current_of_conformal (η : Vec n) (T : Vec n → Tens n) (ω : Vec n → Vec n)
    (x : Vec n) (φ : ℝ)
    (hT : DifferentiableAt ℝ T x) (hω : DifferentiableAt ℝ ω x)
    (hsym : (T x).transpose = T x)
    (hck : ∀ i j, partialD ω x i j + partialD ω x j i
      = 2 * φ * (if i = j then η i else 0)) :
    divJ (current T ω) x = ∑ j, divT T x j * ω x j + φ * traceEta η (T x) := by
  rw [div_current T ω x hT hω]
  congr 1
  exact sum_sym_mul_of_conformal η (T x) (Matrix.of fun i j => partialD ω x i j) φ hsym hck

/-- If moreover `T` is divergence-free at `x`, then `div J = φ · tr_η T`. -/
theorem div_current_of_conformal_of_divT_eq_zero (η : Vec n) (T : Vec n → Tens n)
    (ω : Vec n → Vec n) (x : Vec n) (φ : ℝ)
    (hT : DifferentiableAt ℝ T x) (hω : DifferentiableAt ℝ ω x)
    (hsym : (T x).transpose = T x)
    (hck : ∀ i j, partialD ω x i j + partialD ω x j i
      = 2 * φ * (if i = j then η i else 0))
    (hdiv : ∀ j, divT T x j = 0) :
    divJ (current T ω) x = φ * traceEta η (T x) := by
  rw [div_current_of_conformal η T ω x φ hT hω hsym hck]
  simp [hdiv]

/-- If moreover `T` is divergence-free and `η`-trace-free at `x`, the current is conserved
there. -/
theorem div_current_eq_zero_of_conformal (η : Vec n) (T : Vec n → Tens n)
    (ω : Vec n → Vec n) (x : Vec n) (φ : ℝ)
    (hT : DifferentiableAt ℝ T x) (hω : DifferentiableAt ℝ ω x)
    (hsym : (T x).transpose = T x)
    (hck : ∀ i j, partialD ω x i j + partialD ω x j i
      = 2 * φ * (if i = j then η i else 0))
    (hdiv : ∀ j, divT T x j = 0) (htr : traceEta η (T x) = 0) :
    divJ (current T ω) x = 0 := by
  rw [div_current_of_conformal_of_divT_eq_zero η T ω x φ hT hω hsym hck hdiv, htr, mul_zero]

/-- For a Killing covector (`∂_i ω_j + ∂_j ω_i = 0` at `x`) and symmetric `T`,
`div J = Σ_j (div T)^j ω_j`, with no trace hypothesis. -/
theorem div_current_of_killing (T : Vec n → Tens n) (ω : Vec n → Vec n) (x : Vec n)
    (hT : DifferentiableAt ℝ T x) (hω : DifferentiableAt ℝ ω x)
    (hsym : (T x).transpose = T x)
    (hk : ∀ i j, partialD ω x i j + partialD ω x j i = 0) :
    divJ (current T ω) x = ∑ j, divT T x j * ω x j := by
  have h := div_current_of_conformal (fun _ => 0) T ω x 0 hT hω hsym
    (fun i j => by rw [hk i j]; simp)
  simpa using h

/-- For a Killing covector and symmetric divergence-free `T` the current is conserved. -/
theorem div_current_eq_zero_of_killing (T : Vec n → Tens n) (ω : Vec n → Vec n) (x : Vec n)
    (hT : DifferentiableAt ℝ T x) (hω : DifferentiableAt ℝ ω x)
    (hsym : (T x).transpose = T x)
    (hk : ∀ i j, partialD ω x i j + partialD ω x j i = 0)
    (hdiv : ∀ j, divT T x j = 0) :
    divJ (current T ω) x = 0 := by
  rw [div_current_of_killing T ω x hT hω hsym hk]
  simp [hdiv]

/-! ### Constant test tensors -/

/-- A constant tensor field is divergence-free. -/
theorem divT_const (M : Tens n) (x : Vec n) (j : Fin n) : divT (fun _ => M) x j = 0 := by
  unfold divT
  simp

/-- The divergence of the current of a constant tensor `M` is `Σ_{ij} M^{ij} ∂_i ω_j`. -/
theorem div_current_const (M : Tens n) (ω : Vec n → Vec n) (x : Vec n)
    (hω : DifferentiableAt ℝ ω x) :
    divJ (current (fun _ => M) ω) x = ∑ i, ∑ j, M i j * partialD ω x i j := by
  rw [div_current (fun _ => M) ω x (differentiableAt_const M) hω]
  simp [divT_const]

/-- A double sum against a matrix unit picks out one entry. -/
theorem sum_unit_mul (i j : Fin n) (c : ℝ) (P : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, (if a = i ∧ b = j then c else 0) * P a b = c * P i j := by
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp),
    Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The symmetric test tensor `E_ij + E_ji`. -/
def symUnit (i j : Fin n) : Tens n :=
  Matrix.of fun a b =>
    (if a = i ∧ b = j then (1 : ℝ) else 0) + (if a = j ∧ b = i then (1 : ℝ) else 0)

theorem symUnit_transpose (i j : Fin n) : (symUnit i j).transpose = symUnit i j := by
  ext a b
  simp only [symUnit, Matrix.transpose_apply, Matrix.of_apply]
  rw [add_comm]
  simp only [and_comm]

theorem sum_symUnit_mul (i j : Fin n) (P : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, symUnit i j a b * P a b = P i j + P j i := by
  simp only [symUnit, Matrix.of_apply, add_mul, Finset.sum_add_distrib, sum_unit_mul, one_mul]

theorem traceEta_symUnit_of_ne (η : Vec n) {i j : Fin n} (hij : i ≠ j) :
    traceEta η (symUnit i j) = 0 := by
  unfold traceEta
  refine Finset.sum_eq_zero fun a _ => ?_
  have h1 : ¬ (a = i ∧ a = j) := fun h => hij (h.1.symm.trans h.2)
  have h2 : ¬ (a = j ∧ a = i) := fun h => hij (h.2.symm.trans h.1)
  simp only [symUnit, Matrix.of_apply, h1, h2, reduceIte, add_zero, mul_zero]

theorem traceEta_symUnit_self (η : Vec n) (i : Fin n) :
    traceEta η (symUnit i i) = 2 * η i := by
  unfold traceEta
  simp only [symUnit, Matrix.of_apply, and_self, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The diagonal test tensor `η_j E_ii − η_i E_jj`, which is `η`-trace-free for every `η`. -/
def diagDiff (η : Vec n) (i j : Fin n) : Tens n :=
  Matrix.of fun a b =>
    (if a = i ∧ b = i then η j else 0) - (if a = j ∧ b = j then η i else 0)

theorem diagDiff_transpose (η : Vec n) (i j : Fin n) :
    (diagDiff η i j).transpose = diagDiff η i j := by
  ext a b
  simp only [diagDiff, Matrix.transpose_apply, Matrix.of_apply]
  simp only [and_comm]

theorem sum_diagDiff_mul (η : Vec n) (i j : Fin n) (P : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, diagDiff η i j a b * P a b = η j * P i i - η i * P j j := by
  simp only [diagDiff, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, sum_unit_mul]

theorem traceEta_diagDiff (η : Vec n) (i j : Fin n) :
    traceEta η (diagDiff η i j) = 0 := by
  unfold traceEta
  simp only [diagDiff, Matrix.of_apply, and_self, mul_sub, mul_ite, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-! ### The main theorems -/

open Classical in
/-- **Among `C³` covector fields, the conformal Killing fields are exactly those against which
every differentiable, symmetric, divergence-free, `η`-trace-free tensor field has a conserved
current.** No hypothesis on `η` is needed. Constant tensor fields are admitted and already suffice
for the forward direction. The statement has content from `n = 2` on: for `n ≤ 1` and a metric
with entries `±1`, both sides hold for every `C³` field. -/
theorem currents_conserved_iff_conformalKilling (η : Vec n)
    (ω : Vec n → Vec n) (hω : ContDiff ℝ 3 ω) :
    (∀ T : Vec n → Tens n, Differentiable ℝ T → (∀ x, (T x).transpose = T x) →
        (∀ x j, divT T x j = 0) → (∀ x, traceEta η (T x) = 0) →
        ∀ x, divJ (current T ω) x = 0) ↔ IsConformalKilling η ω := by
  have hd : Differentiable ℝ ω := hω.differentiable (by norm_num)
  constructor
  · intro H
    -- every constant symmetric `η`-trace-free tensor annihilates `∂ω` at every point
    have key : ∀ (M : Tens n), M.transpose = M → traceEta η M = 0 →
        ∀ x, ∑ i, ∑ j, M i j * partialD ω x i j = 0 := by
      intro M hM htr x
      rw [← div_current_const M ω x (hd x)]
      exact H (fun _ => M) (differentiable_const M) (fun _ => hM) (fun y j => divT_const M y j)
        (fun _ => htr) x
    have hdiag : ∀ x i j, η j * partialD ω x i i = η i * partialD ω x j j := by
      intro x i j
      have h := key (diagDiff η i j) (diagDiff_transpose η i j) (traceEta_diagDiff η i j) x
      rw [sum_diagDiff_mul] at h
      linarith
    have hzero : ∀ x i, η i = 0 → partialD ω x i i = 0 := by
      intro x i hi
      have h := key (symUnit i i) (symUnit_transpose i i)
        (by rw [traceEta_symUnit_self, hi, mul_zero]) x
      rw [sum_symUnit_mul] at h
      linarith
    refine ⟨hω, fun x => if h : ∃ k, η k ≠ 0 then partialD ω x h.choose h.choose / η h.choose
      else 0, ?_⟩
    intro x i j
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      by_cases hk : ∃ k, η k ≠ 0
      · simp only [hk, reduceDIte]
        have hne := hk.choose_spec
        have := hdiag x i hk.choose
        field_simp
        linarith
      · simp only [hk, reduceDIte]
        have hi : η i = 0 := by
          by_contra h; exact hk ⟨i, h⟩
        rw [hzero x i hi]; simp
    · have h := key (symUnit i j) (symUnit_transpose i j) (traceEta_symUnit_of_ne η hij) x
      rw [sum_symUnit_mul i j (partialD ω x)] at h
      simp only [h, hij, reduceIte, mul_zero]
  · rintro ⟨-, φ, hφ⟩ T hT hsym hdiv htr x
    exact div_current_eq_zero_of_conformal η T ω x (φ x) (hT x) (hd x) (hsym x) (hφ x)
      (hdiv x) (htr x)

/-- **Among `C³` covector fields, the Killing fields are exactly those against which every
differentiable, symmetric, divergence-free tensor field has a conserved current.** Constant tensor
fields are admitted and already suffice for the forward direction. The statement has content from
`n = 1` on. -/
theorem currents_conserved_iff_killing (ω : Vec n → Vec n) (hω : ContDiff ℝ 3 ω) :
    (∀ T : Vec n → Tens n, Differentiable ℝ T → (∀ x, (T x).transpose = T x) →
        (∀ x j, divT T x j = 0) → ∀ x, divJ (current T ω) x = 0) ↔ IsKilling ω := by
  have hd : Differentiable ℝ ω := hω.differentiable (by norm_num)
  constructor
  · intro H
    refine ⟨hω, fun x i j => ?_⟩
    have h := H (fun _ => symUnit i j) (differentiable_const _)
      (fun _ => symUnit_transpose i j) (fun y k => divT_const _ y k) x
    rw [div_current_const _ ω x (hd x), sum_symUnit_mul i j (partialD ω x)] at h
    exact h
  · rintro ⟨-, hk⟩ T hT hsym hdiv x
    exact div_current_eq_zero_of_killing T ω x (hT x) (hd x) (hsym x) (hk x) (hdiv x)

/-! ### The dilation separates the two classes -/

theorem partialD_dilation (η : Vec n) (x : Vec n) (i j : Fin n) :
    partialD (fun y k => η k * y k) x i j = if i = j then η i else 0 := by
  have hd : DifferentiableAt ℝ (fun (y : Vec n) k => η k * y k) x :=
    differentiableAt_pi.2 fun k => (differentiableAt_apply k x).const_mul (η k)
  rw [partialD_eq hd i j]
  have h : HasFDerivAt (fun y : Vec n => η j * y j)
      (η j • (ContinuousLinearMap.proj j : Vec n →L[ℝ] ℝ)) x :=
    (hasFDerivAt_apply j x).const_mul (η j)
  rw [h.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.single_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

/-- **The dilation field is conformal Killing and not Killing**, in every dimension `n ≥ 1` and
every signature. -/
theorem dilation_isConformalKilling_not_isKilling (η : Vec n) (hη : IsSignature η)
    (hn : 1 ≤ n) :
    IsConformalKilling η (fun x j => η j * x j) ∧ ¬ IsKilling (fun x j => η j * x j) := by
  have hc : ContDiff ℝ 3 (fun (x : Vec n) j => η j * x j) :=
    contDiff_pi.2 fun j => contDiff_const.mul (contDiff_apply ℝ ℝ j)
  refine ⟨⟨hc, fun _ => 1, fun x i j => ?_⟩, ?_⟩
  · rw [partialD_dilation, partialD_dilation]
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp [hij, Ne.symm hij]
  · rintro ⟨-, hk⟩
    have h := hk 0 ⟨0, hn⟩ ⟨0, hn⟩
    rw [partialD_dilation] at h
    simp only [ite_true] at h
    rcases hη ⟨0, hn⟩ with h1 | h1 <;> rw [h1] at h <;> norm_num at h

end

end ConformalKillingFlat
