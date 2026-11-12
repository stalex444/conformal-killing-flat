module
public import ConformalKillingFlat.Killing
public import ConformalKillingFlat.Skew

@[expose] public section
/-!
# Dimension counts

The parametrization of the explicit family by `ℝⁿ × skew n × ℝ × ℝⁿ` is linear and (for `n ≥ 1`
and a metric with entries `±1`) injective; by the classification its range is the space of
conformal Killing fields for `n ≥ 3`.
The Killing subfamily is parametrized by `ℝⁿ × skew n` in every dimension. Both parametrizations
are linear equivalences onto the solution spaces (`paramEquiv`, `paramEquivK`), so both spaces are
finite-dimensional (`finite_conformalKilling`, `finite_killing`).
-/

namespace ConformalKillingFlat

noncomputable section

variable {n : ℕ}

/-- The parametrization of the explicit family by `ℝⁿ × skew n × ℝ × ℝⁿ`, as a linear map. -/
def paramMap (η : Vec n) : (Vec n × skew n × ℝ × Vec n) →ₗ[ℝ] (Vec n → Vec n) where
  toFun p := family η p.1 (p.2.1 : Tens n) p.2.2.1 p.2.2.2
  map_add' p q := by
    funext x j
    simp only [family, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
      Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    funext x j
    simp only [family, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Pi.smul_apply,
      Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]
    ring

theorem paramMap_apply (η a : Vec n) (A : skew n) (lam : ℝ) (b : Vec n) :
    paramMap η (a, A, lam, b) = family η a (A : Tens n) lam b := rfl

theorem paramMap_injective {η : Vec n} (hη : IsSignature η) (i₀ : Fin n) :
    Function.Injective (paramMap η) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, ⟨A, hA⟩, lam, b⟩ hp
  rw [paramMap_apply] at hp
  have hA' : A.transpose = -A := hA
  have hp' : family η a A lam b = 0 := hp
  have ha : a = 0 := by
    rw [← family_zero η a A lam b, hp']
    rfl
  have hD : ∀ x i j, familyD η A lam b x i j = 0 := by
    intro x i j
    rw [← partialD_family η a, hp', partialD_zero]
  have hcf : ∀ x : Vec n, lam + 2 * ∑ k, b k * x k = 0 := by
    intro x
    rw [← cf_family hη a hA' lam b i₀ x, hp']
    simp [cf, partialD_zero]
  have hlam : lam = 0 := by simpa using hcf 0
  have hb : b = 0 := by
    funext k
    have e := hcf (Pi.single k 1)
    simpa [hlam, Pi.single_apply] using e
  have hA0 : A = 0 := by
    ext i j
    have e := hD 0 i j
    simpa [familyD, hlam] using e
  subst ha hlam hb hA0
  rfl

theorem range_paramMap {η : Vec n} (hη : IsSignature η) (hn : 3 ≤ n) :
    LinearMap.range (paramMap η) = conformalKilling η := by
  ext ω
  constructor
  · rintro ⟨⟨a, A, lam, b⟩, rfl⟩
    exact isConformalKilling_family η a A A.2 lam b
  · intro h
    obtain ⟨a, A, lam, b, hA, rfl⟩ := (isConformalKilling_iff η hη hn ω).1 h
    exact ⟨(a, ⟨A, hA⟩, lam, b), rfl⟩

theorem finrank_param_arith (n : ℕ) :
    n + (n * (n - 1) / 2 + (1 + n)) = (n + 1) * (n + 2) / 2 := by
  obtain ⟨k, hk⟩ := Nat.even_mul_pred_self n
  have e : n * (n - 1) / 2 = k := by omega
  rw [e]
  symm
  apply Nat.div_eq_of_eq_mul_left (by norm_num)
  cases n with
  | zero => simp at hk; omega
  | succ m =>
    simp only [Nat.add_sub_cancel] at hk
    nlinarith [hk]

theorem finrank_paramK_arith (n : ℕ) : n + n * (n - 1) / 2 = n * (n + 1) / 2 := by
  obtain ⟨k, hk⟩ := Nat.even_mul_pred_self n
  have e : n * (n - 1) / 2 = k := by omega
  rw [e]
  symm
  apply Nat.div_eq_of_eq_mul_left (by norm_num)
  cases n with
  | zero => simp at hk; omega
  | succ m =>
    simp only [Nat.add_sub_cancel] at hk
    nlinarith [hk]

/-- For `n ≥ 3` and every signature, the parametrization is a linear equivalence between
`ℝⁿ × skew n × ℝ × ℝⁿ` and the space of conformal Killing fields. -/
def paramEquiv {η : Vec n} (hη : IsSignature η) (hn : 3 ≤ n) :
    (Vec n × skew n × ℝ × Vec n) ≃ₗ[ℝ] conformalKilling η :=
  (LinearEquiv.ofInjective (paramMap η) (paramMap_injective hη ⟨0, by omega⟩)).trans
    (LinearEquiv.ofEq _ _ (range_paramMap hη hn))

theorem paramEquiv_apply {η : Vec n} (hη : IsSignature η) (hn : 3 ≤ n)
    (p : Vec n × skew n × ℝ × Vec n) :
    (paramEquiv hη hn p : Vec n → Vec n) = family η p.1 (p.2.1 : Tens n) p.2.2.1 p.2.2.2 := rfl

/-- For `n ≥ 3` and every signature, the space of conformal Killing fields is
finite-dimensional. -/
theorem finite_conformalKilling (η : Vec n) (hη : IsSignature η) (hn : 3 ≤ n) :
    Module.Finite ℝ (conformalKilling η) :=
  Module.Finite.equiv (paramEquiv hη hn)

/-- (5) For `n ≥ 3` and every signature, the conformal Killing fields of flat space form a real
vector space of dimension `(n + 1)(n + 2)/2`. The space is finite-dimensional
(`finite_conformalKilling`), so this is not the default value of `Module.finrank`. -/
theorem finrank_conformalKilling (η : Vec n) (hη : IsSignature η) (hn : 3 ≤ n) :
    Module.finrank ℝ (conformalKilling η) = (n + 1) * (n + 2) / 2 := by
  have i₀ : Fin n := ⟨0, by omega⟩
  rw [← range_paramMap hη hn, LinearMap.finrank_range_of_inj (paramMap_injective hη i₀),
    ← finrank_param_arith]
  simp [Module.finrank_prod, finrank_skew]

/-- The parametrization of the affine fields `a + A x` by `ℝⁿ × skew n`, as a linear map. -/
def paramMapK : (Vec n × skew n) →ₗ[ℝ] (Vec n → Vec n) :=
  paramMap (fun _ => (1 : ℝ)) ∘ₗ (LinearMap.id.prodMap (LinearMap.inl ℝ (skew n) (ℝ × Vec n)))

theorem paramMapK_apply (a : Vec n) (A : skew n) :
    paramMapK (a, A) = family (fun _ => (1 : ℝ)) a (A : Tens n) 0 0 := rfl

theorem paramMapK_injective : Function.Injective (paramMapK (n := n)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, ⟨A, hA⟩⟩ hp
  rw [paramMapK_apply] at hp
  have hp' : family (fun _ => (1 : ℝ)) a A 0 0 = 0 := hp
  have ha : a = 0 := by
    rw [← family_zero (fun _ => (1 : ℝ)) a A 0 0, hp']
    rfl
  have hA0 : A = 0 := by
    ext i j
    have e : familyD (fun _ => (1 : ℝ)) A 0 0 0 i j = 0 := by
      rw [← partialD_family (fun _ => (1 : ℝ)) a, hp', partialD_zero]
    simpa [familyD] using e
  subst ha hA0
  rfl

theorem range_paramMapK : LinearMap.range (paramMapK (n := n)) = killing := by
  ext ω
  constructor
  · rintro ⟨⟨a, A⟩, rfl⟩
    exact isKilling_family _ a A.2
  · intro h
    obtain ⟨a, A, hA, hω⟩ := (isKilling_iff ω).1 h
    refine ⟨(a, ⟨A, hA⟩), ?_⟩
    rw [paramMapK_apply]
    funext x j
    rw [hω x j, family_affine]

/-- In every dimension the parametrization is a linear equivalence between `ℝⁿ × skew n` and the
space of Killing fields. -/
def paramEquivK : (Vec n × skew n) ≃ₗ[ℝ] killing (n := n) :=
  (LinearEquiv.ofInjective paramMapK paramMapK_injective).trans
    (LinearEquiv.ofEq _ _ range_paramMapK)

theorem paramEquivK_apply (p : Vec n × skew n) :
    (paramEquivK p : Vec n → Vec n) = family (fun _ => (1 : ℝ)) p.1 (p.2 : Tens n) 0 0 := rfl

/-- In every dimension the space of Killing fields is finite-dimensional. -/
instance finite_killing : Module.Finite ℝ (killing (n := n)) :=
  Module.Finite.equiv paramEquivK

/-- (6) In every dimension the Killing fields of flat space form a real vector space of dimension
`n (n + 1)/2`. The space is finite-dimensional (`finite_killing`). -/
theorem finrank_killing : Module.finrank ℝ (killing (n := n)) = n * (n + 1) / 2 := by
  rw [← range_paramMapK, LinearMap.finrank_range_of_inj paramMapK_injective,
    ← finrank_paramK_arith]
  simp [Module.finrank_prod, finrank_skew]

/-- (7) In dimension four, for every signature, the conformal Killing fields form a
15-dimensional space. -/
theorem finrank_conformalKilling_four (η : Vec 4) (hη : IsSignature η) :
    Module.finrank ℝ (conformalKilling η) = 15 := by
  rw [finrank_conformalKilling η hη (by norm_num)]

/-- (7) In dimension four the Killing fields form a 10-dimensional space. -/
theorem finrank_killing_four : Module.finrank ℝ (killing (n := 4)) = 10 := by
  rw [finrank_killing]

end

end ConformalKillingFlat
