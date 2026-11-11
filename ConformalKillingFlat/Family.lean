module
public import ConformalKillingFlat.Calculus

@[expose] public section
/-!
# The explicit family and its derivatives

Translations `a`, rotations `A` (antisymmetric), the dilation `lam`, and the special conformal
fields `b`, for a diagonal metric `η` in any dimension.
-/

namespace ConformalKillingFlat

noncomputable section

variable {n : ℕ}

/-- The first partial derivatives `∂_i (family)_j` of the explicit family. -/
def familyD (η : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n) (x : Vec n) (i j : Fin n) : ℝ :=
  A i j + lam * etaM η i j + 2 * b i * η j * x j + 2 * (∑ k, b k * x k) * etaM η i j
    - 2 * b j * η i * x i

theorem contDiff_family {m : WithTop ℕ∞} (η a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n) :
    ContDiff ℝ m (family η a A lam b) := by
  rw [contDiff_pi]
  intro j
  unfold family
  fun_prop

theorem differentiable_family (η a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n) :
    Differentiable ℝ (family η a A lam b) :=
  (contDiff_family (m := 3) η a A lam b).differentiable three_ne_zero'

theorem family_zero (η a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n) :
    family η a A lam b 0 = a := by
  ext j
  simp [family]

theorem family_line (η a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n) (x : Vec n)
    (i j : Fin n) (t : ℝ) :
    family η a A lam b (x + t • Pi.single i 1) j
      = family η a A lam b x j + t * familyD η A lam b x i j
        + t ^ 2 * (2 * b i * etaM η i j - b j * η i) := by
  have e1 : ∑ k, A k j * (x + t • Pi.single i 1 : Vec n) k = ∑ k, A k j * x k + t * A i j :=
    sum_line (fun k => A k j) x i t
  have e2 : ∑ k, b k * (x + t • Pi.single i 1 : Vec n) k = ∑ k, b k * x k + t * b i :=
    sum_line b x i t
  have e3 : ∑ k, η k * (x + t • Pi.single i 1 : Vec n) k ^ 2
      = ∑ k, η k * x k ^ 2 + t * (2 * η i * x i) + t ^ 2 * η i := sum_line_sq η x i t
  unfold family familyD
  rw [e1, e2, e3, line_apply x i j t]
  by_cases h : j = i
  · subst h
    rw [etaM_self]
    simp only [↓reduceIte]
    ring
  · rw [etaM_of_ne η (fun e => h e.symm)]
    simp only [h, ↓reduceIte]
    ring

theorem partialD_family (η a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n) (x : Vec n)
    (i j : Fin n) : partialD (family η a A lam b) x i j = familyD η A lam b x i j := by
  have hd' : Differentiable ℝ (fun y => family η a A lam b y j) :=
    (contDiff_pi.1 (contDiff_family (m := 3) η a A lam b) j).differentiable three_ne_zero'
  rw [partialD_eq_pd (differentiable_family η a A lam b x)]
  exact pd_eq_of_line (hd' x) (family_line η a A lam b x i j)

theorem familyD_symm (η : Vec n) {A : Tens n} (hA : A.transpose = -A) (lam : ℝ) (b : Vec n)
    (x : Vec n) (i j : Fin n) :
    familyD η A lam b x i j + familyD η A lam b x j i
      = 2 * (lam + 2 * ∑ k, b k * x k) * etaM η i j := by
  have h : A j i = -A i j := congrFun (congrFun hA i) j
  unfold familyD
  rw [etaM_comm η j i, h]
  ring

/-- (1) Every member of the explicit family with `A` antisymmetric is conformal Killing, with
conformal factor `lam + 2 b·x`. No hypothesis on `η` is needed. -/
theorem isConformalKilling_family (η : Vec n) (a : Vec n) (A : Tens n)
    (hA : A.transpose = -A) (lam : ℝ) (b : Vec n) : IsConformalKilling η (family η a A lam b) := by
  refine ⟨contDiff_family η a A lam b, fun x => lam + 2 * ∑ k, b k * x k, fun x i j => ?_⟩
  rw [partialD_family, partialD_family]
  exact familyD_symm η hA lam b x i j

/-- The members with `lam = 0`, `b = 0` are the affine fields `a + A x`. -/
theorem family_affine (η a : Vec n) (A : Tens n) (x : Vec n) (j : Fin n) :
    family η a A 0 0 x j = a j + ∑ i, A i j * x i := by
  simp [family]

/-- The members with `lam = 0`, `b = 0` and `A` antisymmetric are Killing. -/
theorem isKilling_family (η a : Vec n) {A : Tens n} (hA : A.transpose = -A) :
    IsKilling (family η a A 0 0) := by
  refine ⟨contDiff_family η a A 0 0, fun x i j => ?_⟩
  rw [partialD_family, partialD_family, familyD_symm η hA]
  simp

/-! ### The conformal factor read off a diagonal entry -/

/-- The conformal factor of a field, read off the diagonal entry `i₀` of its derivative. -/
def cf (η : Vec n) (ω : Vec n → Vec n) (i₀ : Fin n) (x : Vec n) : ℝ :=
  η i₀ * partialD ω x i₀ i₀

theorem cf_family {η : Vec n} (hη : IsSignature η) (a : Vec n) {A : Tens n}
    (hA : A.transpose = -A) (lam : ℝ) (b : Vec n) (i₀ : Fin n) (x : Vec n) :
    cf η (family η a A lam b) i₀ x = lam + 2 * ∑ k, b k * x k := by
  have h : A i₀ i₀ = -A i₀ i₀ := congrFun (congrFun hA i₀) i₀
  have h0 : A i₀ i₀ = 0 := by linarith
  unfold cf
  rw [partialD_family]
  unfold familyD
  rw [etaM_self, h0]
  linear_combination (lam + 2 * ∑ k, b k * x k) * hη.mul_self i₀

theorem pd_cf_family {η : Vec n} (hη : IsSignature η) (a : Vec n) {A : Tens n}
    (hA : A.transpose = -A) (lam : ℝ) (b : Vec n) (i₀ k : Fin n) (x : Vec n) :
    pd k (cf η (family η a A lam b) i₀) x = 2 * b k := by
  have e : cf η (family η a A lam b) i₀ = fun y => lam + 2 * ∑ k, b k * y k :=
    funext fun y => cf_family hη a hA lam b i₀ y
  have hd : Differentiable ℝ (fun y : Vec n => lam + 2 * ∑ k, b k * y k) := by fun_prop
  rw [e]
  refine pd_eq_of_line (c := lam + 2 * ∑ k, b k * x k) (E := 0) (hd x) fun t => ?_
  rw [sum_line b x k t]
  ring

end

end ConformalKillingFlat
