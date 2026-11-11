module
public import ConformalKillingFlat.Spaces

@[expose] public section
/-!
# The converse: every conformal Killing field belongs to the explicit family (`n ≥ 3`)
-/

namespace ConformalKillingFlat

noncomputable section

variable {n : ℕ}

/-- In dimension at least three there is an index different from two given ones. -/
theorem exists_ne_ne (hn : 3 ≤ n) (a b : Fin n) : ∃ c, c ≠ a ∧ c ≠ b := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b} := by
    intro c _
    by_cases hc : c = a
    · simp [hc]
    · simp [h c hc]
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- The algebraic core: an `n × n` array `H` (`n ≥ 3`) satisfying the integrability identity coming
from the symmetry of third derivatives vanishes. -/
theorem hessian_eq_zero_of_identity {η : Vec n} (hη : IsSignature η) (hn : 3 ≤ n)
    (H : Fin n → Fin n → ℝ)
    (hK : ∀ d a b c,
      H d a * etaM η b c + H d b * etaM η c a - H d c * etaM η a b
        = H a d * etaM η b c + H a b * etaM η c d - H a c * etaM η d b) :
    ∀ a b, H a b = 0 := by
  have hoff : ∀ d b, d ≠ b → H d b = 0 := by
    intro d b hdb
    obtain ⟨a, had, hab⟩ := exists_ne_ne hn d b
    have e := hK d a b a
    rw [etaM_of_ne η (Ne.symm hab), etaM_self, etaM_of_ne η hab, etaM_of_ne η had,
      etaM_of_ne η hdb] at e
    have e' : H d b * η a = 0 := by linarith
    exact (mul_eq_zero.1 e').resolve_right (hη.ne_zero a)
  have hdiag : ∀ d a, d ≠ a → H d d * η a = -(H a a * η d) := by
    intro d a hda
    have e := hK d a d a
    rw [etaM_of_ne η hda, etaM_self, etaM_of_ne η (Ne.symm hda), etaM_self] at e
    linarith
  intro a b
  by_cases hab : a = b
  · subst hab
    obtain ⟨c, hca, -⟩ := exists_ne_ne hn a a
    obtain ⟨e, hea, hec⟩ := exists_ne_ne hn a c
    have e1 := hdiag a c (Ne.symm hca)
    have e2 := hdiag a e (Ne.symm hea)
    have e3 := hdiag c e (Ne.symm hec)
    rcases hη a with h1 | h1 <;> rcases hη c with h2 | h2 <;> rcases hη e with h3 | h3 <;>
      simp only [h1, h2, h3] at e1 e2 e3 <;> linarith
  · exact hoff a b hab

/-- Step (ii): the second derivatives of a `C³` solution of `∂_i ω_j + ∂_j ω_i = 2 φ g_ij`
(`g` any constant array) are determined by the gradient of `φ`. -/
theorem second_deriv {ω : Vec n → Vec n} (hc : ContDiff ℝ 3 ω) {φ : Vec n → ℝ}
    (hφ : Differentiable ℝ φ) (g : Fin n → Fin n → ℝ)
    (heq : ∀ x i j,
      pd i (fun y => ω y j) x + pd j (fun y => ω y i) x = 2 * φ x * g i j) :
    ∀ x a b c, pd a (pd b (fun y => ω y c)) x
      = pd a φ x * g b c + pd b φ x * g c a - pd c φ x * g a b := by
  have hW : ∀ c, ContDiff ℝ 3 (fun y => ω y c) := fun c => contDiff_pi.1 hc c
  have hW2 : ∀ c, ContDiff ℝ 2 (fun y => ω y c) := fun c => (hW c).of_le (by norm_num)
  have hP : ∀ b c, Differentiable ℝ (pd b (fun y => ω y c)) := fun b c =>
    (contDiff_pd (hW c) two_add_one_le_three b).differentiable (by norm_num)
  have E1 : ∀ x a b c, pd c (pd a (fun y => ω y b)) x + pd c (pd b (fun y => ω y a)) x
      = 2 * pd c φ x * g a b := by
    intro x a b c
    have h1 := pd_add (hP a b x) (hP b a x) c
    have h2 : (fun y => pd a (fun y => ω y b) y + pd b (fun y => ω y a) y)
        = fun y => 2 * φ y * g a b := funext fun y => heq y a b
    rw [h2] at h1
    have h3 : pd c (fun y => 2 * φ y * g a b) x = 2 * pd c φ x * g a b := by
      have hd : DifferentiableAt ℝ (fun y => 2 * φ y) x := (hφ x).const_mul 2
      rw [pd_mul_const hd, pd_const_mul (hφ x)]
    linarith
  intro x a b c
  have s1 := pd_comm (hW2 b) a c x
  have s2 := pd_comm (hW2 a) b c x
  have s3 := pd_comm (hW2 c) b a x
  linarith [E1 x a b c, E1 x b c a, E1 x c a b]

/-- Step (iii): for `n ≥ 3` the conformal factor of a `C³` solution has vanishing second
derivatives. -/
theorem hessian_phi_eq_zero {η : Vec n} (hη : IsSignature η) (hn : 3 ≤ n)
    {ω : Vec n → Vec n} (hc : ContDiff ℝ 3 ω) {φ : Vec n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (heq : ∀ x i j,
      pd i (fun y => ω y j) x + pd j (fun y => ω y i) x = 2 * φ x * etaM η i j) :
    ∀ x d a, pd d (pd a φ) x = 0 := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have h2 := second_deriv hc hφd (etaM η) heq
  have hW : ∀ c, ContDiff ℝ 3 (fun y => ω y c) := fun c => contDiff_pi.1 hc c
  have hP : ∀ b c, ContDiff ℝ 2 (pd b (fun y => ω y c)) := fun b c =>
    contDiff_pd (hW c) two_add_one_le_three b
  have hφ1 : ∀ a, Differentiable ℝ (pd a φ) := fun a =>
    (contDiff_pd hφ one_add_one_le_two a).differentiable (by norm_num)
  intro x
  have K : ∀ d a b c, pd d (pd a (pd b (fun y => ω y c))) x
      = pd d (pd a φ) x * etaM η b c + pd d (pd b φ) x * etaM η c a
        - pd d (pd c φ) x * etaM η a b := by
    intro d a b c
    have e : pd a (pd b (fun y => ω y c))
        = fun y => pd a φ y * etaM η b c + pd b φ y * etaM η c a - pd c φ y * etaM η a b :=
      funext fun y => h2 y a b c
    rw [e, pd_lin3 (hφ1 a x) (hφ1 b x) (hφ1 c x)]
  apply hessian_eq_zero_of_identity hη hn (fun d a => pd d (pd a φ) x)
  intro d a b c
  have s := pd_comm (hP b c) d a x
  have k1 := K d a b c
  have k2 := K a d b c
  rw [← k1, ← k2, s]

theorem contDiff_cf {η : Vec n} {ω : Vec n → Vec n} (hc : ContDiff ℝ 3 ω) (i₀ : Fin n) :
    ContDiff ℝ 2 (cf η ω i₀) := by
  show ContDiff ℝ 2 (fun x => η i₀ * partialD ω x i₀ i₀)
  exact contDiff_const.mul (contDiff_partialD hc two_add_one_le_three i₀ i₀)

/-- The conformal factor of a conformal Killing field is read off any diagonal entry. -/
theorem IsConformalKilling.factor_eq {η : Vec n} (hη : IsSignature η) {ω : Vec n → Vec n}
    (h : IsConformalKilling η ω) (i₀ : Fin n) (x : Vec n) (i j : Fin n) :
    partialD ω x i j + partialD ω x j i = 2 * cf η ω i₀ x * etaM η i j := by
  obtain ⟨-, ψ, hψ⟩ := h
  have h0 := hψ x i₀ i₀
  simp only [↓reduceIte] at h0
  have e : ψ x = cf η ω i₀ x := by
    unfold cf
    linear_combination (-(η i₀) / 2) * h0 - ψ x * hη.mul_self i₀
  rw [hψ x i j, e]
  rfl

/-- Rigidity (`n ≥ 3`): a conformal Killing field vanishing to first order at the origin, whose
conformal factor has vanishing gradient at the origin, is zero. -/
theorem eq_zero_of_isConformalKilling {η : Vec n} (hη : IsSignature η) (hn : 3 ≤ n)
    {ω : Vec n → Vec n} (h : IsConformalKilling η ω) (i₀ : Fin n)
    (h0 : ω 0 = 0) (h1 : ∀ i j, partialD ω 0 i j = 0)
    (h2 : ∀ a, pd a (cf η ω i₀) 0 = 0) : ω = 0 := by
  have hc := h.1
  have hd : Differentiable ℝ ω := hc.differentiable three_ne_zero'
  have hpd : ∀ x i j, partialD ω x i j = pd i (fun y => ω y j) x := fun x i j =>
    partialD_eq_pd (hd x) i j
  have hW : ∀ c, ContDiff ℝ 3 (fun y => ω y c) := fun c => contDiff_pi.1 hc c
  have hWd : ∀ c, Differentiable ℝ (fun y => ω y c) := fun c =>
    (hW c).differentiable three_ne_zero'
  have hPd : ∀ b c, Differentiable ℝ (pd b (fun y => ω y c)) := fun b c =>
    (contDiff_pd (hW c) two_add_one_le_three b).differentiable (by norm_num)
  have hφ2 : ContDiff ℝ 2 (cf η ω i₀) := contDiff_cf hc i₀
  have hφd : Differentiable ℝ (cf η ω i₀) := hφ2.differentiable (by norm_num)
  have hφ1 : ∀ a, Differentiable ℝ (pd a (cf η ω i₀)) := fun a =>
    (contDiff_pd hφ2 one_add_one_le_two a).differentiable (by norm_num)
  have heq : ∀ x i j, pd i (fun y => ω y j) x + pd j (fun y => ω y i) x
      = 2 * cf η ω i₀ x * etaM η i j := by
    intro x i j
    rw [← hpd, ← hpd]
    exact h.factor_eq hη i₀ x i j
  have hH := hessian_phi_eq_zero hη hn hc hφ2 heq
  have hT := second_deriv hc hφd (etaM η) heq
  -- the gradient of the conformal factor vanishes
  have hgrad : ∀ x a, pd a (cf η ω i₀) x = 0 := by
    intro x a
    rw [eq_of_pd_eq_zero (hφ1 a) (fun y d => hH y d a) x 0]
    exact h2 a
  -- hence all second derivatives vanish
  have hT0 : ∀ x a b c, pd a (pd b (fun y => ω y c)) x = 0 := by
    intro x a b c
    rw [hT x a b c, hgrad x a, hgrad x b, hgrad x c]
    ring
  -- hence all first derivatives vanish
  have hP0 : ∀ x b c, pd b (fun y => ω y c) x = 0 := by
    intro x b c
    rw [eq_of_pd_eq_zero (hPd b c) (fun y a => hT0 y a b c) x 0, ← hpd]
    exact h1 b c
  -- hence the field vanishes
  funext x
  funext c
  have e := eq_of_pd_eq_zero (hWd c) (fun y b => hP0 y b c) x 0
  have e' : ω x c = ω 0 c := e
  rw [e', h0]
  rfl

/-- The antisymmetric part of the first derivative at the origin. -/
def canonA (η : Vec n) (ω : Vec n → Vec n) (i₀ : Fin n) : Tens n :=
  fun i j => partialD ω 0 i j - cf η ω i₀ 0 * etaM η i j

/-- The gradient of the conformal factor at the origin, halved. -/
def canonB (η : Vec n) (ω : Vec n → Vec n) (i₀ : Fin n) : Vec n :=
  fun k => pd k (cf η ω i₀) 0 / 2

theorem IsConformalKilling.canonA_transpose {η : Vec n} (hη : IsSignature η)
    {ω : Vec n → Vec n} (h : IsConformalKilling η ω) (i₀ : Fin n) :
    (canonA η ω i₀).transpose = -canonA η ω i₀ := by
  ext i j
  have e := h.factor_eq hη i₀ 0 j i
  simp only [Matrix.transpose_apply, Matrix.neg_apply, canonA]
  rw [etaM_comm η i j]
  linear_combination e

/-- Steps (ii)–(iv) assembled: for `n ≥ 3` a conformal Killing field is the member of the explicit
family with the same value, first derivative and conformal-factor gradient at the origin. -/
theorem IsConformalKilling.eq_family {η : Vec n} (hη : IsSignature η) (hn : 3 ≤ n)
    {ω : Vec n → Vec n} (h : IsConformalKilling η ω) (i₀ : Fin n) :
    ω = family η (ω 0) (canonA η ω i₀) (cf η ω i₀ 0) (canonB η ω i₀) := by
  have hA := h.canonA_transpose hη i₀
  obtain ⟨F, hF⟩ : ∃ F, F = family η (ω 0) (canonA η ω i₀) (cf η ω i₀ 0) (canonB η ω i₀) :=
    ⟨_, rfl⟩
  rw [← hF]
  have h' : IsConformalKilling η F := by
    rw [hF]
    exact isConformalKilling_family η (ω 0) _ hA _ _
  have hδ : IsConformalKilling η (ω - F) := (conformalKilling η).sub_mem h h'
  have hd : Differentiable ℝ ω := h.1.differentiable three_ne_zero'
  have hd' : Differentiable ℝ F := h'.1.differentiable three_ne_zero'
  have hδD : ∀ x i j, partialD (ω - F) x i j = partialD ω x i j
      - familyD η (canonA η ω i₀) (cf η ω i₀ 0) (canonB η ω i₀) x i j := by
    intro x i j
    rw [partialD_sub (hd x) (hd' x), hF, partialD_family]
  have key := eq_zero_of_isConformalKilling hη hn hδ i₀ ?_ ?_ ?_
  · exact sub_eq_zero.1 key
  · rw [Pi.sub_apply, hF, family_zero, sub_self]
  · intro i j
    rw [hδD]
    simp [familyD, canonA]
  · intro k
    have e : cf η (ω - F) i₀ = fun x => cf η ω i₀ x - cf η F i₀ x := by
      funext x
      unfold cf
      rw [partialD_sub (hd x) (hd' x)]
      ring
    have hdP : Differentiable ℝ (cf η ω i₀) := (contDiff_cf h.1 i₀).differentiable (by norm_num)
    have hdF : Differentiable ℝ (cf η F i₀) := (contDiff_cf h'.1 i₀).differentiable (by norm_num)
    rw [e, pd_sub (hdP 0) (hdF 0), hF, pd_cf_family hη _ hA]
    simp only [canonB]
    ring

/-- (2) For `n ≥ 3` and every signature, the conformal Killing fields of flat space are exactly
the fields of the explicit family: translations `a`, rotations `A`, the dilation `lam`, special
conformal fields `b`. -/
theorem isConformalKilling_iff (η : Vec n) (hη : IsSignature η) (hn : 3 ≤ n)
    (ω : Vec n → Vec n) :
    IsConformalKilling η ω ↔ ∃ (a : Vec n) (A : Tens n) (lam : ℝ) (b : Vec n),
      A.transpose = -A ∧ ω = family η a A lam b := by
  constructor
  · intro h
    have i₀ : Fin n := ⟨0, by omega⟩
    exact ⟨ω 0, canonA η ω i₀, cf η ω i₀ 0, canonB η ω i₀, h.canonA_transpose hη i₀,
      h.eq_family hη hn i₀⟩
  · rintro ⟨a, A, lam, b, hA, rfl⟩
    exact isConformalKilling_family η a A hA lam b

end

end ConformalKillingFlat
