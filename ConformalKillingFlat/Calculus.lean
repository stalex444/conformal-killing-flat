module
public import ConformalKillingFlat.Defs

@[expose] public section
/-!
# A small calculus library for scalar partial derivatives on `ℝⁿ`

Scalar partial derivatives `pd i f`, their symmetry for `C²` functions, the constancy of a function
with vanishing partial derivatives, reading a partial derivative off a coordinate line, and the
compatibility of `partialD` with sums, differences and multiples of fields.
-/

namespace ConformalKillingFlat

noncomputable section

variable {n : ℕ}

/-- The metric as a function of two indices. -/
def etaM (η : Vec n) (i j : Fin n) : ℝ := if i = j then η i else 0

theorem etaM_self (η : Vec n) (i : Fin n) : etaM η i i = η i := by simp [etaM]

theorem etaM_of_ne (η : Vec n) {i j : Fin n} (h : i ≠ j) : etaM η i j = 0 := by simp [etaM, h]

theorem etaM_comm (η : Vec n) (i j : Fin n) : etaM η i j = etaM η j i := by
  by_cases h : i = j
  · subst h; rfl
  · rw [etaM_of_ne η h, etaM_of_ne η (fun e => h e.symm)]

theorem IsSignature.mul_self {η : Vec n} (hη : IsSignature η) (i : Fin n) : η i * η i = 1 := by
  rcases hη i with h | h <;> rw [h] <;> norm_num

theorem IsSignature.ne_zero {η : Vec n} (hη : IsSignature η) (i : Fin n) : η i ≠ 0 := by
  rcases hη i with h | h <;> rw [h] <;> norm_num

/-! ### Scalar partial derivatives -/

/-- `∂_i f` at `x`, for a scalar function `f`. -/
def pd (i : Fin n) (f : Vec n → ℝ) (x : Vec n) : ℝ := fderiv ℝ f x (Pi.single i 1)

theorem partialD_eq_pd {ω : Vec n → Vec n} {x : Vec n} (h : DifferentiableAt ℝ ω x)
    (i j : Fin n) : partialD ω x i j = pd i (fun y => ω y j) x := by
  have h1 : HasFDerivAt (fun y => ω y j)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).comp (fderiv ℝ ω x)) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.comp x
      h.hasFDerivAt
  unfold pd partialD
  rw [h1.fderiv]
  rfl

theorem contDiff_pd {m k : WithTop ℕ∞} {f : Vec n → ℝ} (hf : ContDiff ℝ k f) (hmk : m + 1 ≤ k)
    (i : Fin n) : ContDiff ℝ m (pd i f) := by
  show ContDiff ℝ m (fun x => fderiv ℝ f x (Pi.single i 1))
  exact (hf.fderiv_right hmk).clm_apply contDiff_const

theorem contDiff_partialD {m k : WithTop ℕ∞} {ω : Vec n → Vec n} (hf : ContDiff ℝ k ω)
    (hmk : m + 1 ≤ k) (i j : Fin n) : ContDiff ℝ m (fun x => partialD ω x i j) := by
  have h : ContDiff ℝ m (fun x => fderiv ℝ ω x (Pi.single i 1)) :=
    (hf.fderiv_right hmk).clm_apply contDiff_const
  exact contDiff_pi.1 h j

theorem one_add_one_le_two : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num

theorem two_add_one_le_three : (2 : WithTop ℕ∞) + 1 ≤ 3 := by norm_num

theorem three_ne_zero' : (3 : WithTop ℕ∞) ≠ 0 := by norm_num

/-- Symmetry of mixed partial derivatives of a `C²` function. -/
theorem pd_comm {f : Vec n → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin n) (x : Vec n) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right one_add_one_le_two).differentiable (by norm_num)) x
  have key : ∀ v w : Vec n,
      fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
    intro v w
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  have hs : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)
    = fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1)
  rw [key, key, hs]

/-- A differentiable function all of whose partial derivatives vanish is constant. -/
theorem eq_of_pd_eq_zero {f : Vec n → ℝ} (hf : Differentiable ℝ f) (h : ∀ x i, pd i f x = 0)
    (x y : Vec n) : f x = f y := by
  apply is_const_of_fderiv_eq_zero hf
  intro z
  apply ContinuousLinearMap.coe_injective
  apply LinearMap.pi_ext
  intro i c
  have hs : (Pi.single i c : Vec n) = c • Pi.single i 1 := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  have hz := h z i
  unfold pd at hz
  simp [hs, hz]

/-- Reading off a partial derivative from the restriction to a coordinate line, when that
restriction is a cubic polynomial. -/
theorem pd_eq_of_line_cubic {f : Vec n → ℝ} {x : Vec n} {i : Fin n} (hf : DifferentiableAt ℝ f x)
    {c D E F : ℝ} (h : ∀ t : ℝ, f (x + t • Pi.single i 1) = c + t * D + t ^ 2 * E + t ^ 3 * F) :
    pd i f x = D := by
  have h1 : HasDerivAt (fun t : ℝ => f (x + t • Pi.single i 1))
      (fderiv ℝ f x (Pi.single i 1)) 0 := hf.hasFDerivAt.hasLineDerivAt _
  have h2 : HasDerivAt (fun t : ℝ => c + t * D + t ^ 2 * E + t ^ 3 * F) D 0 := by
    have h3 : HasDerivAt (fun t : ℝ => c + t * D + t ^ 2 * E + t ^ 3 * F)
        (1 * D + (2 * (0 : ℝ) ^ (2 - 1)) * E + (3 * (0 : ℝ) ^ (3 - 1)) * F) 0 :=
      ((((hasDerivAt_id (0 : ℝ)).mul_const D).const_add c).add
        ((hasDerivAt_pow 2 (0 : ℝ)).mul_const E)).add ((hasDerivAt_pow 3 (0 : ℝ)).mul_const F)
    simpa using h3
  rw [funext h] at h1
  exact h1.unique h2

/-- Reading off a partial derivative from the restriction to a coordinate line, when that
restriction is a quadratic polynomial. -/
theorem pd_eq_of_line {f : Vec n → ℝ} {x : Vec n} {i : Fin n} (hf : DifferentiableAt ℝ f x)
    {c D E : ℝ} (h : ∀ t : ℝ, f (x + t • Pi.single i 1) = c + t * D + t ^ 2 * E) :
    pd i f x = D := by
  refine pd_eq_of_line_cubic (c := c) (E := E) (F := 0) hf fun t => ?_
  rw [h t]
  ring

theorem pd_const (i : Fin n) (c : ℝ) (x : Vec n) : pd i (fun _ => c) x = 0 := by
  simp [pd]

theorem pd_add {f g : Vec n → ℝ} {x : Vec n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  unfold pd
  rw [fderiv_fun_add hf hg]
  rfl

theorem pd_sub {f g : Vec n → ℝ} {x : Vec n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  unfold pd
  rw [fderiv_fun_sub hf hg]
  rfl

theorem pd_mul_const {f : Vec n → ℝ} {x : Vec n} (hf : DifferentiableAt ℝ f x) (c : ℝ)
    (i : Fin n) : pd i (fun y => f y * c) x = pd i f x * c := by
  unfold pd
  rw [fderiv_mul_const hf c]
  simp [mul_comm]

theorem pd_const_mul {f : Vec n → ℝ} {x : Vec n} (hf : DifferentiableAt ℝ f x) (c : ℝ)
    (i : Fin n) : pd i (fun y => c * f y) x = c * pd i f x := by
  unfold pd
  rw [fderiv_const_mul hf c]
  simp

theorem pd_lin3 {f g h : Vec n → ℝ} {x : Vec n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (p q r : ℝ) (i : Fin n) :
    pd i (fun y => f y * p + g y * q - h y * r) x = pd i f x * p + pd i g x * q - pd i h x * r := by
  have h1 : DifferentiableAt ℝ (fun y => f y * p) x := hf.mul_const p
  have h2 : DifferentiableAt ℝ (fun y => g y * q) x := hg.mul_const q
  have h3 : DifferentiableAt ℝ (fun y => h y * r) x := hh.mul_const r
  have h12 : DifferentiableAt ℝ (fun y => f y * p + g y * q) x := h1.add h2
  rw [pd_sub h12 h3, pd_add h1 h2, pd_mul_const hf, pd_mul_const hg, pd_mul_const hh]

/-! ### Partial derivatives of sums, differences and multiples of fields -/

theorem partialD_add {ω₁ ω₂ : Vec n → Vec n} {x : Vec n} (h₁ : DifferentiableAt ℝ ω₁ x)
    (h₂ : DifferentiableAt ℝ ω₂ x) (i j : Fin n) :
    partialD (ω₁ + ω₂) x i j = partialD ω₁ x i j + partialD ω₂ x i j := by
  unfold partialD
  rw [fderiv_add h₁ h₂]
  rfl

theorem partialD_sub {ω₁ ω₂ : Vec n → Vec n} {x : Vec n} (h₁ : DifferentiableAt ℝ ω₁ x)
    (h₂ : DifferentiableAt ℝ ω₂ x) (i j : Fin n) :
    partialD (ω₁ - ω₂) x i j = partialD ω₁ x i j - partialD ω₂ x i j := by
  unfold partialD
  rw [fderiv_sub h₁ h₂]
  rfl

theorem partialD_smul {ω : Vec n → Vec n} {x : Vec n} (h : DifferentiableAt ℝ ω x) (c : ℝ)
    (i j : Fin n) : partialD (c • ω) x i j = c * partialD ω x i j := by
  unfold partialD
  rw [fderiv_const_smul h c]
  rfl

theorem partialD_zero (x : Vec n) (i j : Fin n) : partialD (0 : Vec n → Vec n) x i j = 0 := by
  simp [partialD]

/-- A differentiable field all of whose partial derivatives vanish is constant. -/
theorem eq_of_partialD_eq_zero {ω : Vec n → Vec n} (hω : Differentiable ℝ ω)
    (h : ∀ x i j, partialD ω x i j = 0) (x y : Vec n) : ω x = ω y := by
  funext j
  have hj : Differentiable ℝ (fun z => ω z j) := differentiable_pi.1 hω j
  refine eq_of_pd_eq_zero hj (fun z i => ?_) x y
  rw [← partialD_eq_pd (hω z)]
  exact h z i j

/-! ### Coordinate lines -/

theorem line_apply (x : Vec n) (i k : Fin n) (t : ℝ) :
    (x + t • Pi.single i 1 : Vec n) k = x k + t * (if k = i then 1 else 0) := by
  simp [Pi.single_apply]

theorem sum_line (c x : Vec n) (i : Fin n) (t : ℝ) :
    ∑ k, c k * (x + t • Pi.single i 1 : Vec n) k = ∑ k, c k * x k + t * c i := by
  have e : ∀ k, c k * (x + t • Pi.single i 1 : Vec n) k
      = c k * x k + (if k = i then t * c k else 0) := by
    intro k
    rw [line_apply x i k t]
    by_cases h : k = i
    · simp only [h, ↓reduceIte]; ring
    · simp only [h, ↓reduceIte]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem sum_line_sq (c x : Vec n) (i : Fin n) (t : ℝ) :
    ∑ k, c k * (x + t • Pi.single i 1 : Vec n) k ^ 2
      = ∑ k, c k * x k ^ 2 + t * (2 * c i * x i) + t ^ 2 * c i := by
  have e : ∀ k, c k * (x + t • Pi.single i 1 : Vec n) k ^ 2
      = c k * x k ^ 2 + (if k = i then t * (2 * c k * x k) + t ^ 2 * c k else 0) := by
    intro k
    rw [line_apply x i k t]
    by_cases h : k = i
    · simp only [h, ↓reduceIte]; ring
    · simp only [h, ↓reduceIte]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- The partial derivatives of a linear form. -/
theorem pd_linear (c : Vec n) (i : Fin n) (x : Vec n) :
    pd i (fun y => ∑ k, c k * y k) x = c i := by
  have hd : Differentiable ℝ (fun y : Vec n => ∑ k, c k * y k) := by fun_prop
  refine pd_eq_of_line (c := ∑ k, c k * x k) (E := 0) (hd x) fun t => ?_
  rw [sum_line c x i t]
  ring

end

end ConformalKillingFlat
