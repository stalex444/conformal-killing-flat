module
public import ConformalKillingFlat.Family

@[expose] public section
/-!
# Control: in dimension two the classification fails

The real and imaginary parts of `z³` satisfy the Cauchy–Riemann equations, hence the conformal
Killing equation of the Euclidean plane, but form a cubic field, which is not in the (quadratic)
explicit family. So the hypothesis `3 ≤ n` in `isConformalKilling_iff` cannot be dropped.

A second control covers the Lorentzian plane (`η = (1, −1)`): the field
`((x₀ + x₁)³, −(x₀ + x₁)³)`, a cubic function of one null coordinate, is conformal Killing and is
not in the explicit family (`exists_conformalKilling_lorentzian_two_not_family`).

Both controls exclude `family η a A lam b` for every real matrix `A`, antisymmetric or not
(`cubicField_ne_family`, `nullCubicField_ne_family`); this is stronger than excluding the members
with `A` antisymmetric, which are the fields of the classification.
-/

namespace ConformalKillingFlat

noncomputable section

/-- The real and imaginary parts of `z³`, `z = x₀ + i x₁`. -/
def cubicField : Vec 2 → Vec 2 :=
  fun x => ![x 0 ^ 3 - 3 * x 0 * x 1 ^ 2, 3 * x 0 ^ 2 * x 1 - x 1 ^ 3]

theorem cubicField_zero (x : Vec 2) : cubicField x 0 = x 0 ^ 3 - 3 * x 0 * x 1 ^ 2 := rfl

theorem cubicField_one (x : Vec 2) : cubicField x 1 = 3 * x 0 ^ 2 * x 1 - x 1 ^ 3 := rfl

theorem contDiff_cubicField : ContDiff ℝ 3 cubicField := by
  rw [contDiff_pi]
  intro j
  fin_cases j
  · show ContDiff ℝ 3 (fun x : Vec 2 => x 0 ^ 3 - 3 * x 0 * x 1 ^ 2)
    fun_prop
  · show ContDiff ℝ 3 (fun x : Vec 2 => 3 * x 0 ^ 2 * x 1 - x 1 ^ 3)
    fun_prop

theorem differentiable_cubicField : Differentiable ℝ cubicField :=
  contDiff_cubicField.differentiable three_ne_zero'

theorem differentiable_cubicField_apply (j : Fin 2) :
    Differentiable ℝ (fun y => cubicField y j) :=
  differentiable_pi.1 differentiable_cubicField j

theorem partialD_cubicField_00 (x : Vec 2) :
    partialD cubicField x 0 0 = 3 * x 0 ^ 2 - 3 * x 1 ^ 2 := by
  rw [partialD_eq_pd (differentiable_cubicField x)]
  refine pd_eq_of_line_cubic (c := cubicField x 0) (E := 3 * x 0) (F := 1)
    (differentiable_cubicField_apply 0 x) fun t => ?_
  simp only [cubicField_zero, line_apply]
  simp
  ring

theorem partialD_cubicField_01 (x : Vec 2) :
    partialD cubicField x 0 1 = 6 * x 0 * x 1 := by
  rw [partialD_eq_pd (differentiable_cubicField x)]
  refine pd_eq_of_line_cubic (c := cubicField x 1) (E := 3 * x 1) (F := 0)
    (differentiable_cubicField_apply 1 x) fun t => ?_
  simp only [cubicField_one, line_apply]
  simp
  ring

theorem partialD_cubicField_10 (x : Vec 2) :
    partialD cubicField x 1 0 = -(6 * x 0 * x 1) := by
  rw [partialD_eq_pd (differentiable_cubicField x)]
  refine pd_eq_of_line_cubic (c := cubicField x 0) (E := -(3 * x 0)) (F := 0)
    (differentiable_cubicField_apply 0 x) fun t => ?_
  simp only [cubicField_zero, line_apply]
  simp
  ring

theorem partialD_cubicField_11 (x : Vec 2) :
    partialD cubicField x 1 1 = 3 * x 0 ^ 2 - 3 * x 1 ^ 2 := by
  rw [partialD_eq_pd (differentiable_cubicField x)]
  refine pd_eq_of_line_cubic (c := cubicField x 1) (E := -(3 * x 1)) (F := -1)
    (differentiable_cubicField_apply 1 x) fun t => ?_
  simp only [cubicField_one, line_apply]
  simp
  ring

theorem isConformalKilling_cubicField : IsConformalKilling (fun _ => (1 : ℝ)) cubicField := by
  refine ⟨contDiff_cubicField, fun x => 3 * x 0 ^ 2 - 3 * x 1 ^ 2, fun x i j => ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [partialD_cubicField_00, partialD_cubicField_01, partialD_cubicField_10,
      partialD_cubicField_11] <;> ring

theorem cubicField_ne_family (a : Vec 2) (A : Tens 2) (lam : ℝ) (b : Vec 2) :
    cubicField ≠ family (fun _ => (1 : ℝ)) a A lam b := by
  intro h
  have key : ∀ t : ℝ, t ^ 3 = a 0 + (A 0 0 + lam) * t + b 0 * t ^ 2 := by
    intro t
    have e := congrFun (congrFun h ![t, 0]) 0
    rw [cubicField_zero] at e
    simp [family, Fin.sum_univ_two] at e
    rw [e]
    ring
  have k0 := key 0
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key 2
  norm_num at k0 k1 k2 k3
  linarith

/-- (8) In dimension two there is a conformal Killing field that is not `family η a A lam b` for
any `a`, `A`, `lam`, `b`, with no condition on the matrix `A`: the hypothesis `3 ≤ n` of
`isConformalKilling_iff` matters. -/
theorem exists_conformalKilling_two_not_family :
    ∃ ω : Vec 2 → Vec 2, IsConformalKilling (fun _ => (1 : ℝ)) ω ∧
      ¬ ∃ (a : Vec 2) (A : Tens 2) (lam : ℝ) (b : Vec 2), ω = family (fun _ => 1) a A lam b := by
  refine ⟨cubicField, isConformalKilling_cubicField, ?_⟩
  rintro ⟨a, A, lam, b, h⟩
  exact cubicField_ne_family a A lam b h

/-! ### The Lorentzian plane -/

/-- The field `((x₀ + x₁)³, −(x₀ + x₁)³)`: a function of the null coordinate `u = x₀ + x₁` only. -/
def nullCubicField : Vec 2 → Vec 2 :=
  fun x => ![(x 0 + x 1) ^ 3, -(x 0 + x 1) ^ 3]

theorem nullCubicField_zero (x : Vec 2) : nullCubicField x 0 = (x 0 + x 1) ^ 3 := rfl

theorem nullCubicField_one (x : Vec 2) : nullCubicField x 1 = -(x 0 + x 1) ^ 3 := rfl

theorem contDiff_nullCubicField : ContDiff ℝ 3 nullCubicField := by
  rw [contDiff_pi]
  intro j
  fin_cases j
  · show ContDiff ℝ 3 (fun x : Vec 2 => (x 0 + x 1) ^ 3)
    fun_prop
  · show ContDiff ℝ 3 (fun x : Vec 2 => -(x 0 + x 1) ^ 3)
    fun_prop

theorem differentiable_nullCubicField : Differentiable ℝ nullCubicField :=
  contDiff_nullCubicField.differentiable three_ne_zero'

theorem differentiable_nullCubicField_apply (j : Fin 2) :
    Differentiable ℝ (fun y => nullCubicField y j) :=
  differentiable_pi.1 differentiable_nullCubicField j

theorem partialD_nullCubicField_00 (x : Vec 2) :
    partialD nullCubicField x 0 0 = 3 * (x 0 + x 1) ^ 2 := by
  rw [partialD_eq_pd (differentiable_nullCubicField x)]
  refine pd_eq_of_line_cubic (c := nullCubicField x 0) (E := 3 * (x 0 + x 1)) (F := 1)
    (differentiable_nullCubicField_apply 0 x) fun t => ?_
  simp only [nullCubicField_zero, line_apply]
  simp
  ring

theorem partialD_nullCubicField_01 (x : Vec 2) :
    partialD nullCubicField x 0 1 = -(3 * (x 0 + x 1) ^ 2) := by
  rw [partialD_eq_pd (differentiable_nullCubicField x)]
  refine pd_eq_of_line_cubic (c := nullCubicField x 1) (E := -(3 * (x 0 + x 1))) (F := -1)
    (differentiable_nullCubicField_apply 1 x) fun t => ?_
  simp only [nullCubicField_one, line_apply]
  simp
  ring

theorem partialD_nullCubicField_10 (x : Vec 2) :
    partialD nullCubicField x 1 0 = 3 * (x 0 + x 1) ^ 2 := by
  rw [partialD_eq_pd (differentiable_nullCubicField x)]
  refine pd_eq_of_line_cubic (c := nullCubicField x 0) (E := 3 * (x 0 + x 1)) (F := 1)
    (differentiable_nullCubicField_apply 0 x) fun t => ?_
  simp only [nullCubicField_zero, line_apply]
  simp
  ring

theorem partialD_nullCubicField_11 (x : Vec 2) :
    partialD nullCubicField x 1 1 = -(3 * (x 0 + x 1) ^ 2) := by
  rw [partialD_eq_pd (differentiable_nullCubicField x)]
  refine pd_eq_of_line_cubic (c := nullCubicField x 1) (E := -(3 * (x 0 + x 1))) (F := -1)
    (differentiable_nullCubicField_apply 1 x) fun t => ?_
  simp only [nullCubicField_one, line_apply]
  simp
  ring

theorem isConformalKilling_nullCubicField : IsConformalKilling ![1, -1] nullCubicField := by
  refine ⟨contDiff_nullCubicField, fun x => 3 * (x 0 + x 1) ^ 2, fun x i j => ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [partialD_nullCubicField_00, partialD_nullCubicField_01, partialD_nullCubicField_10,
      partialD_nullCubicField_11] <;> ring

theorem nullCubicField_ne_family (a : Vec 2) (A : Tens 2) (lam : ℝ) (b : Vec 2) :
    nullCubicField ≠ family ![1, -1] a A lam b := by
  intro h
  have key : ∀ t : ℝ, t ^ 3 = a 0 + (A 0 0 + lam) * t + b 0 * t ^ 2 := by
    intro t
    have e := congrFun (congrFun h ![t, 0]) 0
    rw [nullCubicField_zero] at e
    simp [family, Fin.sum_univ_two] at e
    rw [e]
    ring
  have k0 := key 0
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key 2
  norm_num at k0 k1 k2 k3
  linarith

/-- In the Lorentzian plane (`η = (1, −1)`) there is a conformal Killing field that is not
`family η a A lam b` for any `a`, `A`, `lam`, `b`, with no condition on the matrix `A`: a cubic
function of one null coordinate. So the hypothesis `3 ≤ n` of `isConformalKilling_iff` cannot be
dropped in signature `(1, 1)` either. -/
theorem exists_conformalKilling_lorentzian_two_not_family :
    ∃ ω : Vec 2 → Vec 2, IsConformalKilling ![1, -1] ω ∧
      ¬ ∃ (a : Vec 2) (A : Tens 2) (lam : ℝ) (b : Vec 2), ω = family ![1, -1] a A lam b := by
  refine ⟨nullCubicField, isConformalKilling_nullCubicField, ?_⟩
  rintro ⟨a, A, lam, b, h⟩
  exact nullCubicField_ne_family a A lam b h

end

end ConformalKillingFlat
