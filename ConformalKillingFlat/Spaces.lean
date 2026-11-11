module
public import ConformalKillingFlat.Family

@[expose] public section
/-!
# The vector spaces of conformal Killing and Killing fields
-/

namespace ConformalKillingFlat

noncomputable section

variable {n : ℕ}

/-- The real vector space of conformal Killing fields of the metric `η`. -/
def conformalKilling (η : Vec n) : Submodule ℝ (Vec n → Vec n) where
  carrier := {ω | IsConformalKilling η ω}
  add_mem' := by
    rintro ω₁ ω₂ ⟨h₁, φ₁, e₁⟩ ⟨h₂, φ₂, e₂⟩
    refine ⟨h₁.add h₂, fun x => φ₁ x + φ₂ x, fun x i j => ?_⟩
    have d₁ : DifferentiableAt ℝ ω₁ x := (h₁.differentiable three_ne_zero') x
    have d₂ : DifferentiableAt ℝ ω₂ x := (h₂.differentiable three_ne_zero') x
    rw [partialD_add d₁ d₂, partialD_add d₁ d₂]
    linear_combination e₁ x i j + e₂ x i j
  zero_mem' := by
    refine ⟨contDiff_const, fun _ => 0, fun x i j => ?_⟩
    rw [partialD_zero, partialD_zero]
    ring
  smul_mem' := by
    rintro c ω ⟨h, φ, e⟩
    refine ⟨h.const_smul c, fun x => c * φ x, fun x i j => ?_⟩
    have d : DifferentiableAt ℝ ω x := (h.differentiable three_ne_zero') x
    rw [partialD_smul d, partialD_smul d]
    linear_combination c * e x i j

/-- The real vector space of Killing fields on `ℝⁿ` (`n` implicit). -/
def killing : Submodule ℝ (Vec n → Vec n) where
  carrier := {ω | IsKilling ω}
  add_mem' := by
    rintro ω₁ ω₂ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    refine ⟨h₁.add h₂, fun x i j => ?_⟩
    have d₁ : DifferentiableAt ℝ ω₁ x := (h₁.differentiable three_ne_zero') x
    have d₂ : DifferentiableAt ℝ ω₂ x := (h₂.differentiable three_ne_zero') x
    rw [partialD_add d₁ d₂, partialD_add d₁ d₂]
    linear_combination e₁ x i j + e₂ x i j
  zero_mem' := by
    refine ⟨contDiff_const, fun x i j => ?_⟩
    rw [partialD_zero, partialD_zero]
    ring
  smul_mem' := by
    rintro c ω ⟨h, e⟩
    refine ⟨h.const_smul c, fun x i j => ?_⟩
    have d : DifferentiableAt ℝ ω x := (h.differentiable three_ne_zero') x
    rw [partialD_smul d, partialD_smul d]
    linear_combination c * e x i j

theorem mem_conformalKilling {η : Vec n} {ω : Vec n → Vec n} :
    ω ∈ conformalKilling η ↔ IsConformalKilling η ω := Iff.rfl

theorem mem_killing {ω : Vec n → Vec n} : ω ∈ killing ↔ IsKilling ω := Iff.rfl

theorem IsKilling.isConformalKilling {ω : Vec n → Vec n} (h : IsKilling ω) (η : Vec n) :
    IsConformalKilling η ω :=
  ⟨h.1, fun _ => 0, fun x i j => by rw [h.2 x i j]; ring⟩

/-- (4) Killing fields are conformal Killing, for every metric. -/
theorem killing_le_conformalKilling (η : Vec n) : killing ≤ conformalKilling η :=
  fun _ h => IsKilling.isConformalKilling h η

end

end ConformalKillingFlat
