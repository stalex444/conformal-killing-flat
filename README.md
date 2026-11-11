# Conformal Killing fields of flat space: classification, dimension counts, conserved currents

Kernel-checked, in Lean 4 + Mathlib. On `ℝⁿ` with a diagonal metric `η` whose entries are `±1`
(every signature), a covector field `ω` is **conformal Killing** when it is `C³` and
`∂_i ω_j + ∂_j ω_i = 2 φ η_ij` for some function `φ`, and **Killing** when it is `C³` and
`∂_i ω_j + ∂_j ω_i = 0`. This repository proves that for `n ≥ 3` the conformal Killing fields are
exactly the translations, the rotations, the dilation and the special conformal fields, a real
vector space of dimension `(n + 1)(n + 2)/2`; that in every dimension the Killing fields are
exactly the translations and rotations, a space of dimension `n (n + 1)/2`; that the current
`T·ω` of a symmetric tensor field satisfies `div (T·ω) = (div T)·ω + φ · tr_η T`; and that
conservation of these currents characterizes the two classes of fields.

Statements 1–4 are classical (the classification of the conformal Killing fields of `ℝ^{p,q}` for
`p + q ≥ 3`, which is the infinitesimal counterpart of Liouville's theorem on conformal maps, and
the Killing fields of flat space). Statement 6 is the standard identity behind the conserved
currents of a trace-free stress tensor. Statements 5 and 9 are standard examples. In statements 7
and 8 the direction from the equation to conserved currents is statement 6; the other direction
was not found stated in the sources read for this entry, is elementary, and is not claimed as
new. No statement here is claimed as a new theorem. The identity of statement 6 is already
formalized in one dimension and signature, and special cases of the currents are formalized
elsewhere; see "Prior formalization" below.

## Who this is for

Formal developments of quantum field theory that carry a stress tensor and its Ward identities.
Two public Lean developments state parts of this subject in four dimensions:

- The Yang–Mills release
  [`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028/tree/3456e5e75cf8d4cd558955a5c7638fba2d68f464)
  states the conformal Killing equation on Euclidean `ℝ⁴`, shows that translations, the dilation and
  rotations satisfy it, proves the current identity for the Maxwell stress, and proves that the
  current of a conserved symmetric stress against a Killing field is conserved inside correlation
  functions.
- [`openai/math`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/TemperedDistribution/ConformalIdentities.lean)
  proves the identity of statement 6 for `n = 4` and signature `(1,3)`.

In neither was a statement found of which fields solve the equation, of how many there are, of
the special conformal fields, or of the converse of the current statement (search of 2026-11-11;
"Prior formalization" below says where it looked and what it could not search). Statements 1–5
give the solutions and their number in every dimension `n ≥ 3` and every signature, and
statements 6–9 give the identity and its converse in every dimension, as statements that import
Mathlib only and that such a development can be checked against.

The entry may also serve formalizations of conformal field theory, where `(n + 1)(n + 2)/2` is the
dimension of the conformal algebra (the algebra itself is not formalized here), and work on
Killing fields in Lean's differential geometry, which at present treats Riemannian manifolds in
general and not the flat classification.

## The compared statements (namespace `FlatConformalKilling`)

`Challenge.lean` imports Mathlib only and carries its definitions. Points and covectors are
functions `Fin n → ℝ` (`Vec n`); a field is `ω : Vec n → Vec n`, read as the covector field with
components `ω_j`; `partialD ω x i j = fderiv ℝ ω x (Pi.single i 1) j` is `∂_i ω_j` at `x`. The
metric is `η : Vec n`, read as the diagonal matrix with entries `η i`; `IsSignature η` says every
entry is `1` or `-1`. `IsConformalKilling η ω` and `IsKilling ω` are the two equations, each with
the hypothesis that `ω` is `C³`. `family η a A lam b` is the field

`ω_j(x) = a_j + Σ_i A_ij x_i + lam η_j x_j + 2 (b·x) η_j x_j − b_j Σ_i η_i x_i²`.

`conformalKilling η` and `killing` are the sets of solutions as submodules of the real vector
space of all fields. A tensor is an `n × n` real matrix (`Tens n`); for a tensor field `T`,
`divT T x j = Σ_i ∂_i T^{ij}`, `current T ω x i = Σ_j T^{ij} ω_j`, `divJ J x = Σ_i ∂_i J^i` and
`traceEta η M = Σ_i η_i M^{ii}`.

Statements 1–5 are the classification. Statements 6–9 concern the conserved currents of these fields:
they say which fields give conserved currents.

| # | name | statement |
|---|------|-----------|
| 1 | `conformalKilling_iff_family` | for `n ≥ 3` and `IsSignature η`: `ω` is conformal Killing if and only if `ω = family η a A lam b` for some `a`, `b`, `lam` and an antisymmetric matrix `A` |
| 2 | `killing_iff_affine` | in every dimension: `ω` is Killing if and only if `ω_j(x) = a_j + Σ_i A_ij x_i` with `A` antisymmetric |
| 3 | `finrank_conformalKilling` | for `n ≥ 3` and `IsSignature η`: the conformal Killing fields form a finite-dimensional real vector space of dimension `(n + 1)(n + 2)/2` |
| 4 | `finrank_killing` | in every dimension: the Killing fields form a finite-dimensional real vector space of dimension `n (n + 1)/2` |
| 5 | `plane_conformalKilling_not_family` | a control for `n ≥ 3` in statement 1: in the Euclidean plane, `η = (1, 1)`, there is a conformal Killing field that is not `family η a A lam b` for any `a`, `A`, `lam`, `b`, where `A` is any real matrix, antisymmetric or not |
| 6 | `div_current_of_conformal` | if `T` and `ω` are differentiable at `x`, `T x` is symmetric and `∂_i ω_j + ∂_j ω_i = 2 φ η_ij` at `x`, then `div (T·ω) = Σ_j (div T)^j ω_j + φ · tr_η T` at `x`; no hypothesis on `η` |
| 7 | `currents_conserved_iff_conformalKilling` | a `C³` field `ω` is conformal Killing if and only if `T·ω` is divergence-free for every differentiable, symmetric, divergence-free, `η`-trace-free tensor field `T`; no hypothesis on `η` |
| 8 | `currents_conserved_iff_killing` | a `C³` field `ω` is Killing if and only if `T·ω` is divergence-free for every differentiable, symmetric, divergence-free tensor field `T` |
| 9 | `dilation_conformalKilling_not_killing` | for `n ≥ 1` and `IsSignature η`: the dilation `ω_j = η_j x_j` is conformal Killing and is not Killing |

The witness in the proof of statement 5 is `ConformalKillingFlat.cubicField`, the real and
imaginary parts of `z³`. Every compared theorem depends on `propext`, `Classical.choice` and
`Quot.sound` only.

## The mathematics in plain words

An infinitesimal motion of `ℝⁿ` is a vector field; lowering its index with the metric gives the
covector field `ω`. The symmetric part of its derivative, `∂_i ω_j + ∂_j ω_i`, measures how the
motion changes the metric. If it vanishes the motion is an infinitesimal isometry (a Killing
field); if it is a multiple `2φ` of the metric at each point, the motion rescales the metric and
preserves angles (a conformal Killing field). The members of the family are: translations `a`,
rotations `A` (for an indefinite metric these include the boosts), the dilation `lam`, with `φ`
constant, and the special conformal fields `b`, with `φ = 2 b·x`. In dimension two the equation is
much weaker: in the Euclidean plane it is the Cauchy–Riemann system, and every holomorphic
function is a solution, which is why statement 1 needs `n ≥ 3`.

A symmetric tensor field `T` and a field `ω` give a current `J^i = Σ_j T^{ij} ω_j`. Because `T` is
symmetric, only the symmetric part of `∂ω` enters the divergence of `J`, and statement 6 follows.
So the current is divergence-free when `T` is divergence-free and `ω` is Killing, or when `T` is
divergence-free and trace-free and `ω` is conformal Killing. Statements 7 and 8 say that these are
the only `C³` fields with that property.

## The proofs

**Classification (statements 1–5).**

1. *The family solves the equation.* A direct computation of the derivatives of
   `family η a A lam b` (`partialD_family`, `isConformalKilling_family`); the conformal factor is
   `lam + 2 b·x`. No hypothesis on `η` is used here.
2. *Second derivatives.* For a `C³` solution, differentiating the equation and using the symmetry
   of second derivatives three times gives
   `∂_a ∂_b ω_c = ∂_a φ · η_bc + ∂_b φ · η_ca − ∂_c φ · η_ab` (`second_deriv`). Here `φ` is taken
   to be `η_0 ∂_0 ω_0`, which the equation forces and which is `C²`.
3. *Where `n ≥ 3` enters.* Differentiating once more and using the symmetry of third derivatives
   gives an algebraic identity on the Hessian `H` of `φ`. For two indices `d ≠ b`, a third index
   `a` different from both exists exactly when `n ≥ 3`, and the identity then gives `H_db = 0`;
   for the diagonal entries it gives `H_dd η_a = −H_aa η_d` for `d ≠ a`, and three distinct
   indices force `H_dd = 0` (`hessian_eq_zero_of_identity`, `hessian_phi_eq_zero`). So `φ` is
   affine. In dimension two there is no third index, and statement 5 shows that the conclusion
   fails.
4. *Rigidity.* A solution that vanishes at the origin together with its first derivative and the
   gradient of its factor is zero: the gradient of `φ` is constant, hence zero; then all second
   derivatives of `ω` vanish by step 2; then the first derivatives are constant, hence zero; then
   `ω` is constant, hence zero (`eq_zero_of_isConformalKilling`). Applied to the difference of a
   solution and the member of the family with the same value, first derivative and gradient of
   the factor at the origin, this gives statement 1 (`IsConformalKilling.eq_family`).
5. *Killing fields.* With `φ = 0`, step 2 says that all second derivatives vanish, in every
   dimension, so the first derivatives are constant and antisymmetric (`IsKilling.partialD_eq`,
   `isKilling_iff`). No metric and no restriction on `n` is involved.
6. *Dimensions.* The map from parameters `(a, A, lam, b)` to fields is linear and injective, and by
   statement 1 its range is the space of conformal Killing fields (`paramEquiv`); the
   antisymmetric matrices have dimension `n (n − 1)/2` (`finrank_skew`), so the total is
   `n + n (n − 1)/2 + 1 + n = (n + 1)(n + 2)/2`. In the same way `paramEquivK` gives
   `n + n (n − 1)/2 = n (n + 1)/2` for the Killing fields.
7. *The control.* The field `(Re z³, Im z³)` satisfies the equation with `φ = 3 (x² − y²)`. Along
   the first axis it is cubic, and `family η a A lam b` is a polynomial of degree at most two
   there for every real matrix `A`, so the antisymmetry of `A` is not used
   (`cubicField_ne_family`).

**Conserved currents: which fields give them (statements
6–9).** Statement 6 is the product rule
`div J = Σ_j (div T)^j ω_j + Σ_ij T^{ij} ∂_i ω_j` (`div_current`) together with the fact that a
symmetric matrix pairs only with the symmetric part of `∂ω` (`sum_sym_mul_of_conformal`). In
statements 7 and 8 the direction from the equation to conserved currents is statement 6. For the
other direction, a constant tensor field `M` is divergence-free and its current has divergence
`Σ_ij M^{ij} ∂_i ω_j`. Taking `M = E_ij + E_ji` gives `∂_i ω_j + ∂_j ω_i = 0`; this tensor is
`η`-trace-free when `i ≠ j`, and in statement 8 it is used for all `i`, `j`. Taking
`M = η_j E_ii − η_i E_jj`, which is `η`-trace-free for every `η`, gives
`η_j ∂_i ω_i = η_i ∂_j ω_j`, so the diagonal entries of `∂ω` are a common multiple of the entries
of `η` (an index with `η_i = 0` is treated separately, with `M = 2 E_ii`). Statement 9 is the computation `∂_i ω_j = η_ij` for the dilation, whose factor is `1`.

The proofs were written from a plan of this classical argument, not from the text of one source;
"Relation to the literature" says how they compare with the sources.

## Scope

- The metric is diagonal with entries `±1`, in any order. A general nondegenerate constant metric
  is reached by a linear change of coordinates, which is not formalized. Statements 6 and 7 make
  no assumption on `η`.
- The solutions are `C³` covector fields on all of `ℝⁿ`; the regularity is part of the two
  definitions. Nothing is claimed about solutions of lower regularity or about fields on a proper
  open subset.
- The fields are covector fields `ω_j`. The vector field is `ξ^i = η_i ω_i`; the statements are
  not restated for it. In this lowered form the Killing equation does not involve the metric.
- The numbers in statements 3 and 4 are dimensions of real vector spaces (`Module.finrank`, with
  `Module.Finite` stated alongside). No Lie bracket is defined and no isomorphism with an
  orthogonal Lie algebra is stated.
- In statements 7 and 8 the tensor fields range over all differentiable fields. Constant tensor
  fields are admitted and already suffice for the direction from conserved currents to the
  equation, which is therefore a pointwise fact of linear algebra. Nothing is said about
  compactly supported tensor fields. None of statements 6–9 depends on statements 1–5; statements 6–8
  hold in every dimension and statement 9 for `n ≥ 1`.
- Statement 7 has content from `n = 2` on: for `n ≤ 1` and a metric with entries `±1`, both sides
  hold for every `C³` field. Statement 8 has content from `n = 1` on.
- Statement 5 is a single example in the Euclidean plane. It excludes `family η a A lam b` for
  every real matrix `A`, which is stronger than a control restricted to the antisymmetric `A` of
  statement 1. No compared statement tests the hypothesis `n ≥ 3` of statement 3. The library has
  a second example of the same form, in the Lorentzian plane
  (`exists_conformalKilling_lorentzian_two_not_family`; not compared).

## Not formalized

- General constant metrics, by change of coordinates.
- Solutions of regularity below `C³`, and fields on proper open subsets of `ℝⁿ`.
- The vector-field form of the statements, and the passage from conformal flows to the equation.
- The Lie algebra structure on the solution spaces and the isomorphism of the conformal Killing
  fields with `so(p+1, q+1)`.
- The finite conformal transformations, that is, Liouville's theorem on conformal maps.
- Dimension two beyond the two examples.
- Compactly supported tensor fields in statements 7 and 8.

## Relation to the literature

- **Statements 1 and 3.** M. Schottenloher, *A Mathematical Introduction to Conformal Field
  Theory*, 2nd ed., Lecture Notes in Physics 759, Springer, 2008, Chapter 1: a conformal Killing
  field of `ℝ^{p,q}` satisfies `X_{μ,ν} + X_{ν,μ} = κ g_{μν}` (Theorem 1.4); the factor `κ`
  satisfies `(n − 2) κ_{,μν} + g_{μν} Δκ = 0` (Theorem 1.6) and is affine for `n > 2` (§1.4.1);
  and every conformal Killing field on a connected open subset of `ℝ^{p,q}`, `p + q > 2`, is
  `X(q) = 2⟨q,b⟩q − ⟨q,q⟩b + λq + c + ωq` with `ω ∈ o(p,q)` (Theorem 1.7). Statement 1 is this
  classification in lowered-index form, as an equivalence, for `C³` fields on all of `ℝⁿ`. The
  source assumes smooth fields and allows connected open subsets; neither statement contains the
  other. P. Ginsparg, *Applied Conformal Field Theory* (Les Houches 1988), arXiv:hep-th/9108028,
  §1.1, derives the same list for signature `(p,q)` and counts
  `(p+q) + ½(p+q)(p+q−1) + 1 + (p+q) = ½(p+q+1)(p+q+2)` generators, the number of statement 3.
- **Statements 2 and 4.** Schottenloher, §1.4.1, determines the fields with factor zero as
  `X(q) = c + ωq`, `ω ∈ o(p,q)`. That section is headed "Case 1: n = p + q > 2"; its argument for
  the fields with factor zero does not use the restriction, and statement 2 is proved here in
  every dimension. M. Blau, *Lecture Notes on General Relativity* (Universität
  Bern; version of November 10, 2026), (9.81)–(9.82), gives the same solution of the Killing
  equation in inertial coordinates, and (14.2)–(14.4) the bound `n + n(n−1)/2 = n(n+1)/2` on the
  number of independent Killing fields, attained by `n`-dimensional Minkowski space.
- **Statement 5.** In the Euclidean plane the conformal Killing fields are the holomorphic
  functions (Schottenloher, §1.4.2; Ginsparg, §1.2); `z³` is one that is not of degree at most
  two.
- **Statement 6 and one direction of statements 7 and 8.** Blau, (10.11)–(10.12) and
  (10.15)–(10.16): for a symmetric `T` and a conformal Killing vector `C` with
  `∇_μ C_ν + ∇_ν C_μ = 2σ g_{μν}`, `∇_μ (T^{μν} C_ν) = (∇_μ T^{μν}) C_ν + σ T^{μν} g_{μν}`.
  D. Simmons-Duffin, *The Conformal Bootstrap* (TASI 2015 lectures; read as arXiv:1602.07982,
  where the title is *TASI Lectures on the Conformal Bootstrap*), (18)–(23), does the same
  computation in flat Euclidean space and presents the Killing and conformal Killing equations as
  the conditions under which the currents are conserved.
- **The other direction of statements 7 and 8** (conserved currents imply the equation) was not
  found stated in the sources read for this entry. Simmons-Duffin's text calls the equation a
  "requirement" but proves only that it suffices. The direction is elementary: it is the
  constant-tensor computation described above. It is given its own proof here and is not claimed
  as new; whether it is printed elsewhere was not established.
- **Statement 9.** The dilatation `X(q) = λq` has a constant nonzero factor (Schottenloher,
  §1.4.1; Blau, (10.19)).
- **The proofs.** Step 2 above is the formula printed as (2.13) in J. Qualls, *Lectures on
  Conformal Field Theory*, arXiv:1511.04074, who gives chapter 4 of Di Francesco, Mathieu and
  Sénéchal, *Conformal Field Theory* (Springer, 1997; not opened for this entry) as a main
  reference. Step 3 reaches the conclusion of Schottenloher's Theorem 1.6 and §1.4.1 by choosing
  a third index, where the sources contract with the metric. Step 4 replaces Schottenloher's
  subtraction of the quadratic and dilation fields and his appeal to the Killing case.
- **Liouville.** J. Liouville, *Extension au cas des trois dimensions de la question du tracé
  géographique*, Note VI in G. Monge, *Application de l'analyse à la géométrie*, 5th ed.,
  Bachelier, Paris, 1850, pp. 609–616, asks for the maps of three-dimensional Euclidean space
  under which infinitely small parts stay similar and concludes that the formula given by the
  transformation by reciprocal radii is the most general one. That is a theorem on finite maps;
  it is not formalized here. Statements 1 and 3 are its infinitesimal counterpart, in every dimension `n ≥ 3` and
  every signature.
- **Current literature.** The subject is conformal geometry of flat pseudo-Euclidean space and
  its use in field theory (MSC 53C18, 53B30, 81T40, 70S10). The classification and the dimension
  `(d+1)(d+2)/2` are the starting point of conformal field theory in dimension `d ≥ 3`:
  D. Poland, S. Rychkov and A. Vichi, *The conformal bootstrap: Theory, numerical techniques,
  and applications*, Rev. Mod. Phys. 91 (2019), 015002 (read as arXiv:1805.04405v3), §III.A,
  state them, attribute the theorem on finite maps to Liouville and cite pp. 609–616 of Monge
  (1850); Simmons-Duffin's lectures build the conformal charges from the currents of statement
  6. In general relativity, Blau's notes treat the currents in §§10.1–10.3 and conformal Killing
  vectors in §§13.8–13.10, where the last section describes conformal Killing vectors with
  harmonic factor as having appeared recently in the study of black-hole perturbations. In
  formal mathematics, Killing fields on Riemannian manifolds and the conformal current identity
  in dimension four have been formalized in Lean in the projects listed under "Prior
  formalization", in commits dated from 2026-10-06 to 2026-11-08 (linked there, under "Dates").
  Interest in formalizing the theorem on finite maps is older: a thread of 2–3 August 2021 on the
  Lean Zulip,
  ["Alternative proofs of Liouville's theorem on conformal maps"](https://leanprover-community.github.io/archive/stream/116395-maths/topic/Alternative.20proofs.20of.20Liouville's.20theorem.20on.20conformal.20maps.html),
  asks how to formalize Liouville's theorem for `C⁴` conformal maps between Euclidean spaces and
  receives advice on a proof to follow. It is a discussion of three messages; it links no
  repository and no finished proof.
- **How the sources were read.** Schottenloher's Chapter 1 in an Internet Archive capture of the
  chapter file on the author's university page (not in the Springer edition); Ginsparg,
  Simmons-Duffin, Qualls and Poland–Rychkov–Vichi in their arXiv versions; Blau's notes in the
  version of November 10, 2026 from the author's page; Liouville's Note in the OCR text of an
  Internet Archive scan. Di Francesco–Mathieu–Sénéchal and Callan–Coleman–Jackiw (cited for the
  application) were not opened. `formalization.yaml` gives the sections read and the links.

## Prior formalization

Search of 2026-11-11, by statement. The links, commits and a fuller description of each item are
in `formalization.yaml` under `related_formalizations`. The report of that search and the reports
of the sessions that wrote the Lean are working records of the author's project and are not part
of this repository. What this section says about another repository is given with a link at a
commit; what it says about the search and about contact is the author's account.

- **Statement 6, in one dimension and signature.**
  [`openai/math`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/TemperedDistribution/ConformalIdentities.lean),
  file `lean/OAI/Analysis/TemperedDistribution/ConformalIdentities.lean`: for `n = 4` and
  signature `(1,3)`, with `T` a symmetric tensor of tempered distributions and the field a
  covector field of temperate growth, `conformal_current_divergence` is the identity of statement
  6 and `conformal_current_conserved` is the direction of statement 7 from the equation to
  conserved currents. The same file shows that translations and Lorentz generators satisfy its
  conformal Killing predicate. It is distributional, which statement 6 is not; it treats one
  dimension and one signature; and it has no classification, no dimension count, no dilation or
  special conformal field, and not the direction from conserved currents to the equation.
- **Special cases on Euclidean `ℝ⁴`.** The Yang–Mills release
  [`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028/tree/3456e5e75cf8d4cd558955a5c7638fba2d68f464):
  `YM/Next/MAXWELL/Current.lean` has a predicate named `Killing` that is the conformal Killing
  equation in components, and `current_div`, the divergence of the current of the polarized
  Maxwell stress, which is symmetric and trace-free; `YM/Next/MAXWELL/Affine.lean` shows that
  translations, the dilation and rotations satisfy the predicate; `YM/Work/A01/Conserve.lean` has
  the Killing equation, translations and rotations as solutions, and `divergence`, the
  conservation of the current of a conserved symmetric stress inside correlation functions.
- **Killing fields.**
  [`facebookresearch/atlas-lean`](https://github.com/facebookresearch/atlas-lean/tree/18d1aa399b6ebaa8cd9c4a48795b43f6734c3785):
  Killing fields on a Riemannian manifold; on a finite-dimensional real inner product space,
  constant fields are Killing and a linear field is Killing if and only if it is skew
  (`MathlibExt/Geometry/Manifold/Riemannian/Killing/VectorSpace.lean`); and, for the
  energy-momentum tensor of the scalar wave equation on Minkowski space, the divergence of the
  current of a field and its vanishing for a Killing field
  (`v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM14/WaveEnergy.lean`, a file in
  which other declarations are left unproved).
  [`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti/tree/1e668f5e55bc20f2eb87f4ba49b48833470290d1/TauCeti/Geometry/Manifold/Riemannian/Killing):
  the general theory of Killing fields on Riemannian manifolds.
- **Not found in any of these:** that every Killing field of flat space is affine, or that every
  conformal Killing field is in the family of statement 1; a dimension count; a special
  conformal field; or a statement that conserved currents imply the equation.
- **Dates** (author dates of the commits, UTC). The OpenAI file was added in
  [adc7f124](https://github.com/openai/math/commit/adc7f1241b42e322a6451854ab7e4b4c146bf78a)
  ("Initial commit"), 2026-10-06. The atlas-lean Killing file was added in
  [6a576f39](https://github.com/facebookresearch/atlas-lean/commit/6a576f39873cb4e541c1e6a460a409f4b848f43d),
  2026-10-28; its wave-equation file is of 2026-08-24
  ([9c4f7703](https://github.com/facebookresearch/atlas-lean/commit/9c4f77036677e8aa896a0c1af4662384bb41ab55)).
  TauCeti's Killing directory was written in three commits, 2026-11-04 to 2026-11-08
  ([3e389ef8](https://github.com/TauCetiProject/TauCeti/commit/3e389ef8b2114fa643ab3d939e71ea99ab748085),
  [2856b93c](https://github.com/TauCetiProject/TauCeti/commit/2856b93cb8b144ce491ce422bd499c2f21aa496e),
  [37853b55](https://github.com/TauCetiProject/TauCeti/commit/37853b557381de79a4744a7aba900611e9406fa4)).
  The Yang–Mills release begins with the commit read here, 2026-11-05.

Contact with these developments (the author's account, from the working records named above).
The OpenAI file, atlas-lean and TauCeti were found by the search, which ran while the library was
being written; the reports of the sessions that wrote the Lean name none of their files, and the
OpenAI file was first opened for this entry after the library and the compared statements were
complete. The Yang–Mills release is different: before this library was written, the author's
project had read `YM/Next/MAXWELL/Current.lean` and `YM/Work/A01/Conserve.lean` and had built a
separate add-on library on the release's definitions (not part of this repository). This
repository does not import the release and does not use its definitions. All four are recorded
in `formalization.yaml` with the relationship "other", not "independent".

No formalization of statements 1–5, or of the direction of statements 7 and 8 from conserved
currents to the equation, was found on 2026-11-11 in: Mathlib (sources at the pin; names on
master through Loogle; issue and pull-request search); Lean 3 mathlib, Physlib, the sphere
eversion, FLT, lean-liquid, flt-regular and formal-conjectures projects, and the other Lean files
indexed by Sourcegraph; the rest of `openai/math` (Sourcegraph, scoped to the repository); the
titles, abstracts and keywords of all Archive of Formal Proofs entries; the Coq/Rocq files
indexed by Sourcegraph and `math-comp/analysis`; HOL Light; Metamath `set.mm`; the Palomar
registry (search API); and web searches for Mizar and Naproche. The 2021 thread on the Lean Zulip
named under "Current literature" is a discussion of how Liouville's theorem on conformal maps
could be proved in Lean; no repository or finished proof is linked from it.

What the search could not do. GitHub code search was not available, so coverage of Lean
repositories beyond those named rests on Sourcegraph's public index, which is partial (it does
not index the Yang–Mills release or Isabelle theory files). The full text of Archive of Formal
Proofs entries, the Isabelle distribution, the Mizar library, Naproche, Coquelicot and the Lean
sources of registered Palomar entries were not searched. A web search surfaced arXiv:2608.21502,
*A Lean Formalization of Hamilton's Three-Manifold Theorem*; its repository was not located, so
it was not checked for Killing fields. In the Yang–Mills release the declaration outlines of the
three files named above were read; its other Lean files were searched for the words "killing" and
"conformal" and not read. In TauCeti's directory, at the commit linked above, the declaration
outline of `Basic.lean` was read, and `Flow.lean` and `Converse.lean` were opened for their main
theorems and searched for the word "conformal"; three later commits to the directory, the last
dated 2026-11-11
([528f652a](https://github.com/TauCetiProject/TauCeti/commit/528f652a8cacf295804b3932c295aba1eab1cc9b)),
were not read. Nothing in the other repositories was compiled; their statements are quoted from
source. This is a dated search, not a claim of priority.

## Application (cited; no compared statement asserts it)

For `n = 4` and a Lorentzian signature the space of statement 3 has dimension 15 and the space of
statement 4 has dimension 10: the infinitesimal conformal symmetries of Minkowski space and its
infinitesimal isometries, the Poincaré generators (Blau, §10.3; the library has the two numbers
as `finrank_conformalKilling_four` and `finrank_killing_four`). Statement 6 is the conservation
law used for them in field theory: the current of a conserved symmetric stress tensor against a
Killing field is conserved, and against a conformal Killing field it is conserved when the stress
tensor is also trace-free (Blau, §§10.1–10.2; Simmons-Duffin, (18)–(24); for the improvement of
an energy-momentum tensor to a trace-free one and the dilatation current `T^{ab} x_b`, Callan,
Coleman and Jackiw, Ann. Phys. 59 (1970), as cited by Blau, §22.4). The Maxwell stress tensor is trace-free in dimension four (Blau, (7.122)); the
author's registry entry PALOMAR-2026-10-14-000009
([`pdt-em-source-selection`](https://github.com/stalex444/pdt-em-source-selection/tree/1c9ba637b5e664a88b6487d463515587616476e1))
characterizes it among symmetric quadratic sources by covariance and zero trace, or by
conservation on source-free fields. That entry works with first jets, not with tensor fields on
`ℝⁿ`; the passage between the two settings is not formalized, and neither repository imports the
other.

## Files

| file | content |
|------|---------|
| `Challenge.lean` | the definitions and the nine statements, unproved; imports Mathlib only |
| `Solution.lean` | the same definitions and statements, proved by transfer from the library |
| `ConformalKillingFlat.lean` | root of the proof library |
| `ConformalKillingFlat/Defs.lean`, `ConformalKillingFlat/Calculus.lean` | the definitions and the lemmas on partial derivatives |
| `ConformalKillingFlat/Family.lean`, `ConformalKillingFlat/Spaces.lean` | the explicit family and the two solution spaces |
| `ConformalKillingFlat/Rigidity.lean`, `ConformalKillingFlat/Killing.lean` | statements 1 and 2 |
| `ConformalKillingFlat/Skew.lean`, `ConformalKillingFlat/Dimension.lean` | antisymmetric matrices; statements 3 and 4 |
| `ConformalKillingFlat/Control.lean` | statement 5 and the Lorentzian example |
| `ConformalKillingFlat/Current.lean` | statements 6–9 |
| `Axioms.lean` | `#print axioms` for the compared and library theorems |
| `comparator.json` | the compared names |
| `formalization.yaml` | registry metadata |
| `BUILD.txt`, `SHA256SUMS` | build record and file hashes |

## Build

Lean `v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

MIT licence (`LICENSE`). Developed with AI assistance (Anthropic Claude, in Claude Code) under
the author's direction; `formalization.yaml` records the production and the review.
