module
public import ConformalKillingFlat.Defs
public import ConformalKillingFlat.Calculus
public import ConformalKillingFlat.Family
public import ConformalKillingFlat.Spaces
public import ConformalKillingFlat.Rigidity
public import ConformalKillingFlat.Killing
public import ConformalKillingFlat.Skew
public import ConformalKillingFlat.Dimension
public import ConformalKillingFlat.Control
public import ConformalKillingFlat.Current

@[expose] public section
/-!
# Classification of the conformal Killing fields of flat pseudo-Euclidean space: the proof library

A covector field `ω` on `ℝⁿ` with a diagonal metric `η` (entries `±1`, any signature) is
*conformal Killing* if it is `C³` and `∂_i ω_j + ∂_j ω_i = 2 φ η_ij` for some function `φ`; it is
*Killing* if `φ = 0`.

Main results (namespace `ConformalKillingFlat`):

* `isConformalKilling_family`: every member of the explicit family with `A` antisymmetric
  (translations, rotations, dilation, special conformal fields) is conformal Killing; no
  hypothesis on `η`.
* `isConformalKilling_iff`: for `n ≥ 3` and every signature, the conformal Killing fields are
  exactly the explicit family.
* `isKilling_iff`: in every dimension the Killing fields are exactly the affine fields `a + A x`
  with `A` antisymmetric (no metric enters).
* `killing_le_conformalKilling`: Killing fields are conformal Killing.
* `finite_conformalKilling`, `finrank_conformalKilling`: for `n ≥ 3` the conformal Killing fields
  form a finite-dimensional real vector space of dimension `(n + 1)(n + 2)/2`; `paramEquiv` is the
  linear equivalence with the parameter space `ℝⁿ × skew n × ℝ × ℝⁿ`.
* `finite_killing`, `finrank_killing`: the Killing fields form a finite-dimensional real vector
  space of dimension `n (n + 1)/2`; `paramEquivK` is the linear equivalence with `ℝⁿ × skew n`.
* `finrank_conformalKilling_four`, `finrank_killing_four`: 15 and 10 in dimension four.
* `skew_eq_so`: the space `skew n` of antisymmetric matrices is the underlying submodule of
  Mathlib's `LieAlgebra.Orthogonal.so (Fin n) ℝ`.
* `exists_conformalKilling_two_not_family`: in the Euclidean plane the classification fails (`z³`).
  `exists_conformalKilling_lorentzian_two_not_family`: it fails in the Lorentzian plane as well (a
  cubic function of one null coordinate). Each field is not `family η a A lam b` for any real
  matrix `A`, antisymmetric or not.
* `div_current`: the product rule `div (T·ω) = (div T)·ω + Σ_ij T^{ij} ∂_i ω_j` at a point where
  the tensor field `T` and the covector field `ω` are differentiable; no symmetry hypothesis.
  `div_current_of_conformal`: if moreover `T x` is symmetric and
  `∂_i ω_j + ∂_j ω_i = 2 φ η_ij` at `x`, then `div (T·ω) = (div T)·ω + φ · tr_η T` at `x`.
* `currents_conserved_iff_conformalKilling`: among `C³` fields, the currents `T·ω` of every
  differentiable, symmetric, divergence-free, `η`-trace-free tensor field are divergence-free iff
  `ω` is conformal Killing (no hypothesis on `η`); `currents_conserved_iff_killing`: without the
  trace condition, iff Killing. Constant tensor fields are admitted and already suffice for the
  forward directions. For a metric with entries `±1` the first statement has content from `n = 2`
  on; the second has content from `n = 1`.
* `dilation_isConformalKilling_not_isKilling`: for `n ≥ 1` and a metric with entries `±1`, the
  dilation separates the two classes.

Scope. "Every signature" means a diagonal metric with entries `±1`; a general nondegenerate
constant metric is reached by a linear change of coordinates that is not formalized here. The
spaces `conformalKilling η` and `killing` are the spaces of `C³` solutions. The numbers
`(n + 1)(n + 2)/2` and `n (n + 1)/2` are dimensions of real vector spaces: no Lie bracket and no
isomorphism with an orthogonal Lie algebra is stated. The fields are covector fields `ω_j` (the
vector field is `ξ^i = η^{ij} ω_j`, an equivalent reformulation not stated here). The regularity is
`C³`, part of the definition: nothing is claimed about solutions of lower regularity.

Files: shared definitions in `Defs`, the calculus library in `Calculus`, the explicit family in
`Family`, the two submodules in `Spaces`, the converse in `Rigidity`, the Killing case in
`Killing`, antisymmetric matrices in `Skew`, the dimension counts in `Dimension`, the
two-dimensional controls in `Control`, the currents in `Current`. `Challenge.lean` carries its own
copy of the definitions and imports Mathlib only; `Solution.lean` proves the compared statements
from this library; `Axioms.lean` prints the axioms.
-/
