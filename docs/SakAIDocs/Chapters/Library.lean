import Verso
import VersoManual
import VersoBlueprint
import LeanOA.Mathlib.RingTheory.Annihilator
import LeanOA.Ultraweak.Annihilator
import LeanOA.Ultraweak.CentralSupport
import LeanOA.Ultraweak.CompleteAdditivity
import LeanOA.Ultraweak.BoundedOperatorClosedness
import LeanOA.Ultraweak.BoundedOperatorRelativeKaplansky
import LeanOA.Ultraweak.KaplanskyDensity
import LeanOA.Ultraweak.NormalOrder
import LeanOA.Ultraweak.Opposite
import LeanOA.Ultraweak.ElementPolarDecomposition
import LeanOA.Ultraweak.FunctionalJordanDecomposition
import LeanOA.Ultraweak.FunctionalPolarDecomposition
import LeanOA.Ultraweak.FunctionalSupport
import LeanOA.Ultraweak.OrthogonalProjectionSum
import LeanOA.Ultraweak.PredualUniqueness
import LeanOA.Ultraweak.ProjectionDecomposition
import LeanOA.Ultraweak.ProjectionChain
import LeanOA.Ultraweak.ProjectionLattice
import LeanOA.Ultraweak.RelativeKaplanskyDensity
import LeanOA.Ultraweak.SpectralApproximation
import LeanOA.Ultraweak.SpectralBand
import LeanOA.Ultraweak.SpectralProjectionStrong
import LeanOA.Ultraweak.Support
import LeanOA.Ultraweak.TaggedSpectralSum
import LeanOA.Ultraweak.TruncatedSpectralSum

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean
open Informal

#doc (Manual) "Library and API path" =>

The mathematical chapters explain why results are needed.  This page points
to the reusable library layers in which they live.

{index}[ultraweak topology]
{index}[predual]
{index}[Kaplansky density theorem]
{index}[polar decomposition]
{index}[support projection, of a functional]
{index}[null left ideal]
{index}[orthogonal positive functionals]
{index}[Jordan decomposition, of a normal functional]
{index}[polar decomposition, of a normal functional]
{index}[absolute value, of a normal functional]

# Duality and ultraweak topology

The `Ultraweak` namespace contains the specified-predual topology, its
continuous dual, transport maps, multiplication, star, order, and closure
interfaces.  Predual uniqueness is exposed through
{name}`Predual.equiv` and related equivalences rather
than through a Sakai-numbered wrapper.

The fixed-element extraction lemma
{name}`Ultraweak.tendsto_parts_of_tendsto_sub` separates the limits of two
pieces from the ultraweak limit of their difference.  When the extractor is
a star projection and the pieces are eventually nonnegative,
{name}`Ultraweak.posPart_negPart_eq_of_tendsto_sub_of_isStarProjection`
identifies those limits with Mathlib's positive and negative parts.  This
general $`C^*`-level API does not assert an arbitrary spectral-resolution
theorem.

The canonical positive-functional normality predicate remains
{name}`PositiveLinearMap.IsNormalOnProjections`.  Its source-facing order
characterizations are
{name}`PositiveLinearMap.isNormalOnProjections_iff_scottContinuous` and
{name}`PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_bounded_nonneg`;
the chain-restricted characterization is
{name}`PositiveLinearMap.isNormalOnProjections_iff_scottContinuousOn_chains`.
Its specified-predual bridge is
{name}`PositiveLinearMap.mem_continuousDual_of_scottContinuousOn_chains`;
the specified-predual form of Sakai 1.13.2 is
{name}`PositiveLinearMap.scottContinuousOn_bounded_nonneg_iff_mem_continuousDual`.
No second normal-functional structure or predicate is introduced.

# Projection and ideal interfaces

The complete lattice instance for star projections is
{name}`IsStarProjection.instCompleteLatticeSubtypeOfWStarAlgebra`.  Closed
one-sided ideal classification is exposed in the native `Ideal` namespace;
closed two-sided ideals use Mathlib's native `TwoSidedIdeal` rather than a
repository-specific substitute.

The semiring-level annihilator API is {name}`Ideal.leftAnnihilator` and
{name}`Ideal.rightAnnihilator`; the latter encodes a right ideal in the
multiplicative opposite.  Ring-valued two-sided packaging uses
{name}`TwoSidedIdeal.annihilatorOfIdeal` and its opposite-ring analogue.
Ultraweak closedness is a separate layer, beginning with
{name}`Ideal.isClosed_leftAnnihilator`.

The support-projection API begins with {name}`WStarAlgebra.leftSupport` and
{name}`WStarAlgebra.rightSupport`.  Their leastness characterizations are
{name}`WStarAlgebra.leftSupport_le_iff` and
{name}`WStarAlgebra.rightSupport_le_iff`; the self-adjoint specialization is
{name}`WStarAlgebra.support_le_iff`.  Adjoint transport and the support of
a bundled self-adjoint element are exposed by
{name}`WStarAlgebra.leftSupport_star` and {name}`WStarAlgebra.support`.
The support of a projection itself simplifies through
{name}`WStarAlgebra.support_coe_isStarProjection`, and
{name}`WStarAlgebra.le_support_of_smul_le` turns a strictly positive scalar
lower bound on a projection into support inclusion.
The reusable full-support criterion
{name}`WStarAlgebra.leftSupport_eq_one_of_algebraMap_le` applies to any
element bounded below by a strictly positive real scalar; it is not tied to
spectral projections or even to a self-adjoint input type.

The order lemma
{name}`IsStarProjection.mul_eq_self_of_nonneg_of_le_of_mul_eq_self` lives in
the general C-star-algebra projection layer.  It expresses the hereditary
fact that a projection fixing a positive upper bound fixes every smaller
positive element, and is used to prove support monotonicity without any
W-star-specific argument.

The ordered-difference identity
{name}`IsStarProjection.sub_mul_sub_eq_zero_of_le` is stated for nonunital
$`C^*`-algebras.  It says that $`p\leq q\leq r\leq s` makes the projection
differences $`q-p` and $`s-r` orthogonal, and contains no spectral or
$`W^*`-algebra assumptions.

For an arbitrary pairwise orthogonal family of star projections,
{name}`IsStarProjection.orthogonalFinsetSum` is the finite-subset partial sum.
Its projection and order interfaces culminate in
{name}`IsStarProjection.isLUB_range_orthogonalFinsetSum` and the ambient-order
variant {name}`IsStarProjection.isLUB_range_coe_orthogonalFinsetSum`.
The finite-subset net converges to the existing projection supremum through
{name}`IsStarProjection.tendsto_toUltraweak_orthogonalFinsetSum` and
{name}`IsStarProjection.tendsto_toStrong_orthogonalFinsetSum`.  The index type
is arbitrary; this API introduces neither countability nor a new infinite-sum
object.

For a nonempty projection chain in a $`W^*`-algebra,
{name}`IsChain.exists_orthogonal_projection_family` produces an orthogonal
family whose supremum is the chain LUB.  Its finite-domination clause gives
every finite partial sum a common upper bound lying in the original chain;
the reusable finite-sum order lemma is
{name}`IsStarProjection.orthogonalFinsetSum_le_of_forall_le`.
Commutation with a fixed element passes to any nonempty directed projection
LUB through {name}`IsStarProjection.commute_of_isLUB`.

Complete additivity remains a theorem-only interface.  The scalar bridge
{name}`Complex.hasSum_iff_isLUB_finsetSum_of_nonneg` identifies Mathlib's
`HasSum` with the LUB of all finite subsums for a nonnegative family.
The operator-algebra endpoints are
{name}`PositiveLinearMap.IsNormalOnProjections.hasSum_orthogonal`,
{name}`PositiveLinearMap.isNormalOnProjections_of_hasSum_orthogonal`, and
{name}`PositiveLinearMap.isNormalOnProjections_iff_hasSum_orthogonal`.
They introduce no bundled complete-additivity predicate and no countability
assumption.

# Support of a normal positive functional

The GNS null left ideal
{name}`PositiveLinearMap.nullIdeal` is defined for an arbitrary positive
functional on a $`C^*`-algebra; it does not carry an unnecessary normality or
$`W^*`-algebra assumption.  Its defining and coefficient-vanishing
interfaces are {name}`PositiveLinearMap.mem_nullIdeal` and
{name}`PositiveLinearMap.mem_nullIdeal_iff_forall_apply_star_mul_eq_zero`.

For a specified predual, normality gives strong and ultraweak closedness via
{name}`PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_strong` and
{name}`PositiveLinearMap.IsNormalOnProjections.isClosed_nullIdeal_ultraweak`.
The second theorem follows the source route through coincidence of strong and
ultraweak closures on convex sets.

The intrinsic $`W^*`-algebra construction is
{name}`PositiveLinearMap.support`.  It takes an explicit proof of the
established `PositiveLinearMap.IsNormalOnProjections` predicate; the chosen
predual remains internal.  The null-ideal generator and right-annihilator
interfaces are
{name}`PositiveLinearMap.nullIdeal_eq_span_one_sub_support` and
{name}`PositiveLinearMap.mem_nullIdeal_iff_mul_support_eq_zero`.  The right
orientation matters: nullity is $`x s(\varphi)=0`.

The projection-order characterization is
{name}`PositiveLinearMap.apply_eq_zero_iff_le_one_sub_support`, packaged as a
greatest-element statement by
{name}`PositiveLinearMap.isGreatest_setOf_apply_eq_zero`.  The source cutdown
API consists of {name}`PositiveLinearMap.apply_mul_support`,
{name}`PositiveLinearMap.apply_support_mul`, and
{name}`PositiveLinearMap.apply_support_mul_support`.

Sakai's full-support definition of faithfulness is exposed by
{name}`PositiveLinearMap.support_eq_one_iff_apply_star_mul_self_eq_zero_imp`.
The useful support-corner consequences are
{name}`PositiveLinearMap.apply_star_mul_self_eq_zero_iff_on_support_corner`
and
{name}`PositiveLinearMap.apply_eq_zero_iff_of_nonneg_on_support_corner`.
These reuse `IsStarProjection.Corner`; no competing corner or functional-
faithfulness structure is introduced.  The corner theorems are derived
consequences of Definition 1.14.2 rather than separate verbatim source
statements.

# Orthogonality and functional Jordan decomposition

Sakai's norm-theoretic relation is
{name}`PositiveLinearMap.IsOrthogonal`, defined at nonunital $`C^*`-algebra
generality.  Its intrinsic $`W^*`-algebra characterization for normal
positive functionals is
{name}`PositiveLinearMap.isOrthogonal_iff_support_mul_eq_zero`.  The two
directions are also available separately as
{name}`PositiveLinearMap.isOrthogonal_of_support_mul_eq_zero` and
{name}`PositiveLinearMap.support_mul_eq_zero_of_isOrthogonal`.

The source-facing Sakai 1.14.3 endpoint is
{name}`Ultraweak.existsUnique_orthogonal_decomposition_of_isSelfAdjoint`.
It accepts the existing continuous-linear-functional representation on a
specified ultraweak topology and returns a unique pair of ordinary positive
linear maps, each carrying an explicit
`PositiveLinearMap.IsNormalOnProjections` proof.  The difference is stated
after pullback to the ordinary normed algebra, and `IsOrthogonal` records the
exact additive norm identity.  Complementary carrier projections and the
positive polar factor remain private implementation data.  No choice-based
positive/negative-part definitions or second normal-functional structure are
introduced.

# General functional polar decomposition

The exact Sakai 1.14.4 endpoint is
{name}`Ultraweak.existsUnique_functional_polar_decomposition`.  Its input is
the existing continuous-linear-functional representation on a specified
ultraweak topology.  Its unique pair $`(v,\varphi)` consists of an algebra
element and an ordinary positive linear map carrying an explicit
`PositiveLinearMap.IsNormalOnProjections` proof.  The factorization uses the
source's right-action convention:

$`
  g(x)=\varphi(xv),
`

represented by {name}`PositiveLinearMap.cutoff`.  The same theorem includes
the norm equality, the initial-support equation $`v^*v=s(\varphi)`, and the
final-support equation $`vv^*=s(\lvert g^*\rvert)`.  Its `ExistsUnique`
packages uniqueness of the whole pair, not only uniqueness of the positive
factor.

The canonical positive factor $`\lvert g\rvert` is
{name}`Ultraweak.functionalAbs`.  Its normality, normalized factorization,
norm, and recognition interfaces are respectively
{name}`Ultraweak.functionalAbs_isNormalOnProjections`,
{name}`Ultraweak.functionalAbs_spec`,
{name}`Ultraweak.norm_functionalAbs`, and
{name}`Ultraweak.eq_functionalAbs_of_polar_decomposition`.  The separately
discoverable final-support lemma is
{name}`Ultraweak.functional_polar_decomposition_final_projection`; the
initial-support-only package used internally by the source theorem is
{name}`Ultraweak.existsUnique_functional_polar_decomposition_basic`.

Conjugation of an ordinary positive functional is the general $`C^*`-level
operation {name}`PositiveLinearMap.conjugate`.  Normality is preserved by
{name}`PositiveLinearMap.IsNormalOnProjections.conjugate`, and
{name}`PositiveLinearMap.support_conjugate_eq_mul_star` supplies the support
transport needed for the final projection.  No new normal-functional wrapper
or partial-isometry predicate is introduced: the equation
$`v^*v=s(\varphi)` already says that the initial product is a projection.

# Element polar decomposition

Mathlib's {name}`CFC.abs` remains the canonical absolute value.  The narrow
$`W^*`-bridge {name}`WStarAlgebra.support_abs` identifies its support with
the established right support; {name}`WStarAlgebra.support_abs_star` gives
the corresponding final-support form.

The existence interface
{name}`WStarAlgebra.exists_element_polar_decomposition` exposes only the
factorization and the two canonical support equations.  The algebraic
theorem {name}`WStarAlgebra.element_polar_decomposition_unique` needs only
the factorization and initial-support equations, while
{name}`WStarAlgebra.existsUnique_element_polar_decomposition` packages the
exact statement of Sakai 1.12.1.  The useful modulus-square consequence
{name}`CFC.mul_star_eq_of_eq_mul_abs` is stated independently at the weaker
abstract nonunital real-CFC level.

# Lower spectral projections

The positive cutoff
{name}`CStarAlgebra.spectralPositivePart` is deliberately defined at the
$`C^*`-algebra level.  Its named continuous-functional-calculus bridge,
identification with positive part, and fixed-element norm continuity are
{name}`CStarAlgebra.spectralPositivePart_eq_cfc`,
{name}`CStarAlgebra.spectralPositivePart_eq_posPart` and
{name}`CStarAlgebra.continuous_spectralPositivePart`.

The W-star layer begins only when support is taken:
{name}`WStarAlgebra.spectralProjectionIio`.  Its primary interfaces are the
leastness characterization
{name}`WStarAlgebra.spectralProjectionIio_le_iff`, monotonicity
{name}`WStarAlgebra.spectralProjectionIio_mono`, ultraweak directed-net continuity
{name}`WStarAlgebra.tendsto_spectralProjectionIio_of_monotone`, and intrinsic
strong left continuity
{name}`WStarAlgebra.continuousWithinAt_spectralProjectionIio_strong`.  The exact
sequential source theorem, which does not assume monotonicity, is
{name}`WStarAlgebra.tendsto_spectralProjectionIio_strong`.  The `Iio`
suffix distinguishes this half-line cut from a future set-indexed spectral
projection API.

Calculations can use the left and right support-action simp lemmas
{name}`WStarAlgebra.spectralProjectionIio_mul_spectralPositivePart` and
{name}`WStarAlgebra.spectralPositivePart_mul_spectralProjectionIio` without
unfolding the projection construction.

The scalar-cut recovery and band APIs are
{name}`WStarAlgebra.sub_mul_spectralProjectionIio`,
{name}`WStarAlgebra.commute_spectralProjectionIio`, and
{name}`WStarAlgebra.spectralProjectionIio_band_bounds`.  Sakai's packaged
increment estimate is
{name}`WStarAlgebra.spectralProjectionIio_increment_bounds`.
The endpoint formulas and their ultraweak consequences are
{name}`WStarAlgebra.spectralProjectionIio_eq_zero_of_le_neg_norm`,
{name}`WStarAlgebra.spectralProjectionIio_eq_one_of_norm_lt`,
{name}`WStarAlgebra.tendsto_spectralProjectionIio_atBot`, and
{name}`WStarAlgebra.tendsto_spectralProjectionIio_atTop`.

Finite-partition approximation is exposed without a repository-specific
partition type.  The constructions are {name}`WStarAlgebra.lowerSpectralSum`
and {name}`WStarAlgebra.upperSpectralSum`; their main interfaces are the
bracketing theorem
{name}`WStarAlgebra.lowerSpectralSum_le_self_and_self_le_upperSpectralSum`,
the order-gap estimate
{name}`WStarAlgebra.upperSpectralSum_sub_lowerSpectralSum_le_smul_one`, and
the norm estimate
{name}`WStarAlgebra.norm_upperSpectralSum_sub_lowerSpectralSum_le`.

Norm convergence for an arbitrary filtered family of divisions with
mesh tending to zero is exposed by
{name}`WStarAlgebra.tendsto_lowerSpectralSum` and
{name}`WStarAlgebra.tendsto_upperSpectralSum`.  The concrete nested witness
uses {name}`WStarAlgebra.dyadicSpectralCut` and
{name}`WStarAlgebra.dyadicSpectralMesh`; refinement and convergence are
recorded by {name}`WStarAlgebra.dyadicSpectralCut_refines`,
{name}`WStarAlgebra.tendsto_lowerSpectralSum_dyadic`, and
{name}`WStarAlgebra.tendsto_upperSpectralSum_dyadic`.  The dyadic-grid
arithmetic is stated for seminormed additive star groups, independently of
the W-star application.

The theorem-level spectral-band API avoids introducing a bundled spectral
family.  Ordered differences are projections by
{name}`WStarAlgebra.isStarProjection_spectralProjectionIio_sub`; commutation,
adjacent additivity, and disjoint-band orthogonality are exposed by
{name}`WStarAlgebra.commute_spectralProjectionIio_sub_spectralProjectionIio_sub`,
{name}`WStarAlgebra.spectralProjectionIio_sub_add_sub`, and
{name}`WStarAlgebra.spectralProjectionIio_sub_mul_spectralProjectionIio_sub_eq_zero`.

Arbitrary tagged sums are {name}`WStarAlgebra.taggedSpectralSum`; the endpoint
specializations are the canonical bridges
{name}`WStarAlgebra.taggedSpectralSum_eq_lowerSpectralSum` and
{name}`WStarAlgebra.taggedSpectralSum_eq_upperSpectralSum`.  The main analytic
interfaces are the lower/upper sandwich
{name}`WStarAlgebra.lowerSpectralSum_le_taggedSpectralSum_and_taggedSpectralSum_le_upperSpectralSum`,
the mesh estimate {name}`WStarAlgebra.norm_taggedSpectralSum_sub_self_le`, and
filter-general convergence {name}`WStarAlgebra.tendsto_taggedSpectralSum`.
The named topology bridge is
{name}`WStarAlgebra.tendsto_taggedSpectralSum_ultraweak`.
The dyadic specialization is
{name}`WStarAlgebra.tendsto_taggedSpectralSum_dyadic`.  These declarations do
not define a spectral measure or integral.

Truncated-affine recovery remains theorem-level and reuses the same finite
sums.  The single-band interface
{name}`WStarAlgebra.spectralPositivePart_mul_spectralProjectionIio_sub_bounds`
handles a cutoff lying inside a band.  Its finite consequence is the sharp
mesh estimate
{name}`WStarAlgebra.norm_truncated_affine_taggedSpectralSum_sub_spectralPositivePart_le`.
Filter-general norm and specified-ultraweak convergence are
{name}`WStarAlgebra.tendsto_truncated_affine_taggedSpectralSum` and
{name}`WStarAlgebra.tendsto_truncated_affine_taggedSpectralSum_ultraweak`;
the concrete dyadic specialization is
{name}`WStarAlgebra.tendsto_truncated_affine_taggedSpectralSum_dyadic`.
The target is the existing Mathlib-CFC object
{name}`CStarAlgebra.spectralPositivePart`, not a new integral operation.

# Central ideals and central support

Ultraweakly closed native two-sided ideals are classified by central
projections in
{name}`TwoSidedIdeal.existsUnique_isStarProjection_mem_center_eq_span_of_isClosed_ultraweak`.
The reusable interfaces are
{name}`IsStarProjection.Central.orderIsoUltraweakClosedTwoSidedIdeal` and
{name}`IsStarProjection.Central.le_centralGenerator_iff_mem`.

Central support is {name}`WStarAlgebra.centralSupport`; its leastness API is
{name}`WStarAlgebra.le_centralSupport` and
{name}`WStarAlgebra.centralSupport_le_iff`.  Sakai 1.10.7 is exposed in the
stronger reusable form
{name}`WStarAlgebra.centralSupport_mul_centralSupport_eq_zero_iff`.

# Nonunital generated algebras

The nonunital closure layer parallels the unital API without forcing the
ambient identity into a generated algebra.  Its principal declarations are
{name}`NonUnitalStarSubalgebra.ultraweakClosure`,
{name}`NonUnitalStarSubalgebra.ultraweakAdjoin`, and
{name}`NonUnitalStarSubalgebra.ultraweakClosure_minimal`.  Closed nonunital
star subalgebras inherit a C-star structure and an internal identity through
{name}`NonUnitalStarSubalgebra.IsUltraweakClosed.nonUnitalCStarAlgebra` and
{name}`NonUnitalStarSubalgebra.IsUltraweakClosed.isUnital`.

# Opposite transport

The specified-predual equivalence {name}`Ultraweak.opCLE` identifies the
ultraweak spaces of a normed space and its multiplicative opposite.  It is
defined through the weak-bilinear transport API and requires no algebra
multiplication structure.

# Density

The Kaplansky density implementation is split between the reusable C-star algebra
transform in `LeanOA.CStarAlgebra.KaplanskyDensity` and the duality/topology
argument in `LeanOA.Ultraweak.KaplanskyDensity`.  The endpoint is
{name}`Ultraweak.SakaiInvariantTestSpace.kaplansky_density_Sak_1_9_1`.
The ambient-relative layer in
`LeanOA.Ultraweak.RelativeKaplanskyDensity` keeps the target closure explicit;
its endpoint is
{name}`Ultraweak.SakaiInvariantTestSpace.kaplansky_density_of_testWeakClosure_eq`.
For bounded operators, `LeanOA.Ultraweak.BoundedOperatorWOTClosure` identifies
the finite-coefficient test-weak closure with Mathlib WOT, and
`LeanOA.Ultraweak.BoundedOperatorRelativeKaplansky` exposes the concrete
rewrite theorem {name}`Ultraweak.kaplansky_density_wotClosure`.
`LeanOA.Mathlib.Analysis.LocallyConvex.SquareSummableConvergenceCLM` supplies
the generic square-summable convergence carrier and its continuous identity
to pointwise convergence.  `LeanOA.Ultraweak.BoundedOperatorUltrastrong`
identifies each of its defining $`B(H)` seminorms with the GNS seminorm of a
positive diagonal coefficient-series functional and exposes the continuous
identity from intrinsic strong convergence.
`LeanOA.Ultraweak.BoundedOperatorClosedness` then exposes the four concrete
closedness predicates, the series-test-to-WOT identity, the relative
unit-ball normalization lemmas, and
{name}`NonUnitalStarSubalgebra.operatorTopologyClosedness_tfae`.  The four
pairwise WOT equivalences are separately named for theorem search.  Its
generic dependencies {name}`Ultraweak.testWeakRestrictionL` and
{name}`Ultraweak.Strong.isClosed_ofStrong_preimage_iff_ofUltraweak_preimage`
remain usable for arbitrary nested predual test spaces and arbitrary
real-convex ambient subsets, respectively.

# Portability rule

New declarations are placed at the weakest useful level.  Algebraic
annihilators belong in a ring-theoretic staging module; topology-specific
closedness belongs in the ultraweak layer; projection lemmas that need only a
unital C-star algebra belong with the general C-star algebra projection API.

# Declaration coverage

The Verso cutover included a declaration-level audit of the completed Section
1.10 work.  Every named public declaration introduced in the annihilator,
opposite-transport, nonunital-closure, support, two-sided-ideal, and
central-support modules is attached to its mathematical Blueprint node or
named on this API path.  The two general projection lemmas are covered as
well.  New Section 1.11 declarations are linked from the
lower-spectral-projection chapter and this API path.  Thus the site records
the reusable helper API in addition to the 87 headline mathematical nodes
inherited from the former graph.
