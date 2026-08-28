import Verso
import VersoManual
import VersoBlueprint
import LeanOA.Mathlib.RingTheory.Annihilator
import LeanOA.Ultraweak.Annihilator
import LeanOA.Ultraweak.CentralSupport
import LeanOA.Ultraweak.KaplanskyDensity
import LeanOA.Ultraweak.Opposite
import LeanOA.Ultraweak.PredualUniqueness
import LeanOA.Ultraweak.ProjectionLattice
import LeanOA.Ultraweak.SpectralProjection
import LeanOA.Ultraweak.Support

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

# Duality and ultraweak topology

The `Ultraweak` namespace contains the specified-predual topology, its
continuous dual, transport maps, multiplication, star, order, and closure
interfaces.  Predual uniqueness is exposed through
{name}`Predual.equiv` and related equivalences rather
than through a Sakai-numbered wrapper.

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
{name}`WStarAlgebra.rightSupport_le_iff`; adjoint transport and the support of
a bundled self-adjoint element are exposed by
{name}`WStarAlgebra.leftSupport_star` and {name}`WStarAlgebra.support`.

The order lemma
{name}`IsStarProjection.mul_eq_self_of_nonneg_of_le_of_mul_eq_self` lives in
the general C-star-algebra projection layer.  It expresses the hereditary
fact that a projection fixing a positive upper bound fixes every smaller
positive element, and is used to prove support monotonicity without any
W-star-specific argument.

# Lower spectral projections

The positive cutoff
{name}`CStarAlgebra.spectralPositivePart` is deliberately defined at the
C-star-algebra level.  Its identification with positive part and its
fixed-element norm continuity are
{name}`CStarAlgebra.spectralPositivePart_eq_posPart` and
{name}`CStarAlgebra.continuous_spectralPositivePart`.

The W-star layer begins only when support is taken:
{name}`WStarAlgebra.spectralProjectionIio`.  Its primary interfaces are the
leastness characterization
{name}`WStarAlgebra.spectralProjectionIio_le_iff`, monotonicity
{name}`WStarAlgebra.spectralProjectionIio_mono`, and directed-net continuity
{name}`WStarAlgebra.tendsto_spectralProjectionIio_of_monotone`.  The `Iio`
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
