module
public import ConformalKillingFlat.Spaces
public import ConformalKillingFlat.Rigidity

@[expose] public section
/-!
# Killing fields of flat space are the affine fields with antisymmetric linear part

No metric and no hypothesis on the dimension: in lowered-index form the Killing equation
`∂_i ω_j + ∂_j ω_i = 0` does not involve the metric.
-/

namespace ConformalKillingFlat

noncomputable section

variable {n : ℕ}

/-- Step (v): the first derivatives of a Killing field are constant. -/
theorem IsKilling.partialD_eq {ω : Vec n → Vec n} (h : IsKilling ω) (x : Vec n) (i j : Fin n) :
    partialD ω x i j = partialD ω 0 i j := by
  have hc := h.1
  have hd : Differentiable ℝ ω := hc.differentiable three_ne_zero'
  have hpd : ∀ x i j, partialD ω x i j = pd i (fun y => ω y j) x := fun x i j =>
    partialD_eq_pd (hd x) i j
  have hW : ∀ c, ContDiff ℝ 3 (fun y => ω y c) := fun c => contDiff_pi.1 hc c
  have hPd : ∀ b c, Differentiable ℝ (pd b (fun y => ω y c)) := fun b c =>
    (contDiff_pd (hW c) two_add_one_le_three b).differentiable (by norm_num)
  have heq : ∀ x i j, pd i (fun y => ω y j) x + pd j (fun y => ω y i) x
      = 2 * (fun _ : Vec n => (0 : ℝ)) x * (fun _ _ : Fin n => (0 : ℝ)) i j := by
    intro x i j
    rw [← hpd, ← hpd, h.2 x i j]
    simp
  have hT := second_deriv hc (φ := fun _ => 0) (differentiable_const 0) (fun _ _ => 0) heq
  have hT0 : ∀ x a b c, pd a (pd b (fun y => ω y c)) x = 0 := by
    intro x a b c
    rw [hT x a b c]
    simp
  rw [hpd, hpd]
  exact eq_of_pd_eq_zero (hPd i j) (fun y a => hT0 y a i j) x 0

/-- The first derivative of a field at the origin, as a matrix. -/
def killA (ω : Vec n → Vec n) : Tens n := fun i j => partialD ω 0 i j

theorem IsKilling.killA_transpose {ω : Vec n → Vec n} (h : IsKilling ω) :
    (killA ω).transpose = -killA ω := by
  ext i j
  have e := h.2 0 j i
  simp only [Matrix.transpose_apply, Matrix.neg_apply, killA]
  linear_combination e

/-- A Killing field is the affine field with the same value and first derivative at the origin. -/
theorem IsKilling.eq_affine {ω : Vec n → Vec n} (h : IsKilling ω) (x : Vec n) (j : Fin n) :
    ω x j = ω 0 j + ∑ i, killA ω i j * x i := by
  obtain ⟨F, hF⟩ : ∃ F, F = family (fun _ => (1 : ℝ)) (ω 0) (killA ω) 0 0 := ⟨_, rfl⟩
  have hd : Differentiable ℝ ω := h.1.differentiable three_ne_zero'
  have hd' : Differentiable ℝ F := by
    rw [hF]
    exact differentiable_family _ _ _ _ _
  have hz : ∀ x i j, partialD (ω - F) x i j = 0 := by
    intro x i j
    rw [partialD_sub (hd x) (hd' x), hF, partialD_family, h.partialD_eq x i j]
    simp [familyD, killA]
  have key : (ω - F) x = (ω - F) 0 := eq_of_partialD_eq_zero (hd.sub hd') hz x 0
  have e0 : (ω - F) 0 = 0 := by rw [Pi.sub_apply, hF, family_zero, sub_self]
  have e1 : ω x - F x = 0 := by rw [← Pi.sub_apply, key, e0]
  rw [sub_eq_zero.1 e1, hF, family_affine]

/-- (3) In every dimension, the Killing fields of flat space are exactly the affine fields
`a + A x` with `A` antisymmetric. -/
theorem isKilling_iff (ω : Vec n → Vec n) :
    IsKilling ω ↔ ∃ (a : Vec n) (A : Tens n), A.transpose = -A ∧
      ∀ x j, ω x j = a j + ∑ i, A i j * x i := by
  constructor
  · intro h
    exact ⟨ω 0, killA ω, h.killA_transpose, h.eq_affine⟩
  · rintro ⟨a, A, hA, h⟩
    have e : ω = family (fun _ => (1 : ℝ)) a A 0 0 := by
      funext x j
      rw [h x j, family_affine]
    rw [e]
    exact isKilling_family _ a hA

end

end ConformalKillingFlat
