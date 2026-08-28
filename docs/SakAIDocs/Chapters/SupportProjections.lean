import Verso
import VersoManual
import VersoBlueprint
import LeanOA.Mathlib.Algebra.Star.NonUnitalSubalgebra
import LeanOA.Mathlib.Analysis.CStarAlgebra.Projection
import LeanOA.Ultraweak.Annihilator
import LeanOA.Ultraweak.CentralSupport
import LeanOA.Ultraweak.Support

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Support projections and central support" =>

This chapter is the completed formalization target after Sakai's Theorem 1.9.1.  It
completes Section 1.10 through Proposition 1.10.7.  Its results
construct left, right, and self-adjoint support projections, identify
ultraweakly closed two-sided ideals with central projections, and prove the
orthogonality theorem for central supports.

{index}[support projection]
{index}[central support]
{index}[annihilator]

This chapter is also the bridge to Sakai's spectral resolution in Section
1.11, where the spectral family is defined by
$`e(\lambda)=s((\lambda 1-h)^{+})`.

The local Mathlib version and the original LeanOA repository have no
operator-algebra support-projection or central-support construction to reuse.
The implementation should nevertheless be connective tissue around existing
general objects: `LinearMap.ker`, native `Ideal` and `TwoSidedIdeal`,
`Set.center`, the complete lattice of projections, and Mathlib's nonunital
star-subalgebra closure API.

:::group "algebraic-annihilators"
Algebraic annihilators, without topology or normed-space assumptions.
:::

# Algebraic annihilators
%%%
tag := "algebraic-annihilators"
%%%

For a subset $`S` of a semiring $`R`, write
$`\operatorname{Ann}_{\ell}(S)=\{x\in R\mid xs=0\text{ for every }s\in S\}`
and
$`\operatorname{Ann}_{r}(S)=\{x\in R\mid sx=0\text{ for every }s\in S\}`.

:::definition "def:one_sided_annihilators" (parent := "algebraic-annihilators") (lean := "Ideal.leftAnnihilator, Ideal.mem_leftAnnihilator, Ideal.leftAnnihilator_singleton, Ideal.rightAnnihilator, Ideal.mem_rightAnnihilator, Ideal.rightAnnihilator_singleton, Ideal.rightAnnihilator_eq_leftAnnihilator_image_op")
Let $`R` be a semiring and $`S\subseteq R`.  Define the left annihilator of
$`S` as an `Ideal R` and the right annihilator as an
`Ideal (MulOpposite R)`.  For a singleton, these are kernels of fixed
multiplication maps in $`R` and its opposite.

The definitions are infima of `LinearMap.ker`; their membership lemmas reduce
to the pointwise conditions above.  No star operation, order, norm, topology,
or scalar field occurs in this interface.
:::

:::definition "def:two_sided_annihilators" (parent := "algebraic-annihilators") (lean := "TwoSidedIdeal.annihilatorOfIdeal, TwoSidedIdeal.mem_annihilatorOfIdeal, TwoSidedIdeal.asIdeal_annihilatorOfIdeal, TwoSidedIdeal.annihilatorOfIdealOpposite, TwoSidedIdeal.mem_annihilatorOfIdealOpposite, TwoSidedIdeal.asIdealOpposite_annihilatorOfIdealOpposite")
For a ring $`R`, the annihilator of a left ideal $`I`,
$`\{x\in R\mid xs=0\text{ for every }s\in I\}`, and the annihilator of a
right ideal $`J`,
$`\{x\in R\mid sx=0\text{ for every }s\in J\}`, are native Mathlib
`TwoSidedIdeal R`s.

Mathlib's current `TwoSidedIdeal` is ring-based even though the two-sided
closure argument itself does not use a multiplicative identity and the
one-sided annihilator layer needs only a semiring.  The public assumptions
track the actual upstream object boundary.
:::

:::proof "def:two_sided_annihilators"
Absorption on one side follows by associativity and zero multiplication.  On
the other side, use closure of $`I` under left multiplication.  The right-ideal
case is transported from the left-ideal construction through
`TwoSidedIdeal.unop`; both constructions expose membership simp lemmas and
their underlying one-sided ideals.
:::

:::lemma_ "lem:annihilators_ultraweak_closed" (parent := "algebraic-annihilators") (lean := "Ideal.isClosed_leftAnnihilator, Ideal.isClosed_rightAnnihilator, TwoSidedIdeal.isClosed_annihilatorOfIdeal, TwoSidedIdeal.isClosed_annihilatorOfIdealOpposite")
Let $`M` be a C-star algebra with specified complete predual $`P`.  The left and
right annihilators of an arbitrary subset of $`M` are ultraweakly closed.  The
two-sided annihilator of any left or right ideal is also ultraweakly closed
through its underlying complex submodule.

This uses {uses "def:one_sided_annihilators"}[],
{uses "def:two_sided_annihilators"}[], and
{uses "lem:star_left_mul_right_mul_sig_cts_Sak_1_7_8"}[].
:::

:::proof "lem:annihilators_ultraweak_closed"
Each annihilator is an intersection of kernels of maps $`x\mapsto xa` or
$`x\mapsto ax`.  Fixed multiplication is already ultraweakly continuous, so
the kernels are closed and arbitrary intersections remain closed.  The proof
uses the transported submodule API and does not repeat a net argument.
:::

:::lemma_ "lem:ultraweak_op_homeomorph" (parent := "algebraic-annihilators") (lean := "Ultraweak.opCLE, Ultraweak.opCLE_apply, Ultraweak.opCLE_symm_apply, Ultraweak.isClosed_image_opCLE_iff")
The canonical maps $`\operatorname{op}:M\to M^{\mathrm{op}}` and
$`\operatorname{unop}:M^{\mathrm{op}}\to M` induce mutually inverse
complex-linear homeomorphisms for the ultraweak topologies determined by a
specified predual $`P`.  Consequently a subset is ultraweakly closed exactly
when its image in the opposite algebra is ultraweakly closed.
:::

:::proof "lem:ultraweak_op_homeomorph"
The specified predual on $`M^{\mathrm{op}}` is transported from that on $`M`
along Mathlib's `op`/`unop` linear isometric equivalence.  Applying
`WeakBilin.congr` gives a continuous linear equivalence whose forward and
inverse maps are `op` and `unop`.  The formal result is a general fact about
specified preduals, with no algebra multiplication assumptions.
:::

:::group "support-projections"
Left, right, and self-adjoint support projections.
:::

# Left, right, and self-adjoint support
%%%
tag := "support-projections"
%%%

The public support projections should not retain a choice of predual.  For a
W-star algebra $`M`, define them in the canonical complete lattice of star
projections by
$`l(a)=\bigwedge\{p\mid pa=a\}` and
$`r(a)=\bigwedge\{p\mid ap=a\}`.

:::definition "def:left_right_support_Sak_1_10_3" (parent := "support-projections") (lean := "WStarAlgebra.leftSupport, WStarAlgebra.rightSupport")
For $`a` in a W-star algebra $`M`, its _left support_ $`l(a)` is the
infimum of projections $`p` satisfying $`pa=a`, and its _right support_
$`r(a)` is the infimum of projections $`q` satisfying $`aq=a`.

The construction uses
{uses "prop:proj_compl_lat_wstar_Sak_1_10_2"}[].
:::

:::proposition "prop:left_right_support_characterization" (parent := "support-projections") (lean := "WStarAlgebra.leftSupport_mul, WStarAlgebra.mul_rightSupport, WStarAlgebra.leftSupport_le_iff, WStarAlgebra.rightSupport_le_iff, WStarAlgebra.leftAnnihilator_singleton_eq_span, WStarAlgebra.rightAnnihilator_singleton_eq_span, WStarAlgebra.mul_leftSupport_eq_zero_iff, WStarAlgebra.rightSupport_mul_eq_zero_iff, WStarAlgebra.mul_support_eq_zero_iff, WStarAlgebra.support_mul_eq_zero_iff, WStarAlgebra.mul_support_posPart, WStarAlgebra.support_posPart_mul")
For every $`a\in M`, $`l(a)a=a` and $`ar(a)=a`.  For every projection
$`p`,
$`l(a)\leq p\Longleftrightarrow pa=a` and
$`r(a)\leq p\Longleftrightarrow ap=a`.

Equivalently, the singleton annihilators are
$`\operatorname{Ann}_{\ell}(\{a\})=M(1-l(a))` and
$`\operatorname{Ann}_{r}(\{a\})=(1-r(a))M`.
Consequently, multiplication by a support projection has the same zero
kernel as multiplication by the element it supports, on the appropriate
side.  For self-adjoint elements this is available on both sides.

This uses {uses "def:left_right_support_Sak_1_10_3"}[],
{uses "lem:annihilators_ultraweak_closed"}[],
{uses "prop:left_ideals_in_wstar_proj_Sak_1_10_1"}[], and
{uses "cor:right_ideals_in_wstar_proj_Sak_1_10_1"}[].
:::

:::proof "prop:left_right_support_characterization"
Write the left annihilator as $`Me` for its unique projection $`e`.  Then
$`(1-e)a=a`.  If $`pa=a`, the projection $`1-p` annihilates $`a`, hence
$`1-p\leq e` and $`1-e\leq p`.  Thus $`1-e` has the universal property of
$`l(a)`.  The right-support result is the same argument in the opposite
algebra.  The universal properties and annihilator identities should be the
primary API.
:::

:::lemma_ "lem:support_star_compatibility" (parent := "support-projections") (lean := "WStarAlgebra.leftSupport_star, WStarAlgebra.rightSupport_star, WStarAlgebra.IsSelfAdjoint.leftSupport_eq_rightSupport, WStarAlgebra.support, WStarAlgebra.support_mul, WStarAlgebra.mul_support, WStarAlgebra.leftSupport_zero, WStarAlgebra.rightSupport_zero, WStarAlgebra.leftSupport_one, WStarAlgebra.rightSupport_one, WStarAlgebra.leftSupport_smul, WStarAlgebra.rightSupport_smul, WStarAlgebra.leftSupport_mono_of_nonneg, WStarAlgebra.rightSupport_mono_of_nonneg, WStarAlgebra.leftSupport_eq_one_of_algebraMap_le, IsStarProjection.mul_eq_self_of_nonneg_of_le_of_mul_eq_self")
For every $`a\in M`, $`l(a^*)=r(a)` and $`r(a^*)=l(a)`.  If $`h=h^*`,
these projections agree.  Their common value $`s(h)` is the support
projection of $`h`.  Left support is invariant under multiplication by a
nonzero scalar and monotone on nonnegative elements.  In particular, if
$`r>0` and $`r1\leq a`, then $`l(a)=1`.

This uses {uses "prop:left_right_support_characterization"}[].
:::

:::proof "lem:support_star_compatibility"
Taking adjoints converts $`pa=a` into $`a^*p=a^*` because $`p` is
self-adjoint.  Apply the two order characterizations and antisymmetry.  This
argument is algebraic once the support universal properties are available.

The support-one criterion follows by comparing $`l(r1)` and $`l(a)`:
scalar invariance identifies the first projection with $`l(1)=1`, while
monotonicity forces it below $`l(a)`.  This general argument is later reused
for the upper endpoint of the spectral family.
:::

:::group "generated-nonunital-algebra"
The nonunital ultraweak algebra generated by one element.
:::

# The nonunital ultraweak algebra generated by an element
%%%
tag := "generated-nonunital-algebra"
%%%

Sakai's W-star subalgebra generated by $`h` in Proposition 1.10.4 need not
contain the ambient identity.  Its internal identity is $`s(h)`.  The existing
unital ultraweak-closure construction is therefore not the right formal object.

:::lemma_ "lem:internal_unit_is_projection" (parent := "generated-nonunital-algebra") (lean := "IsUnital.isStarProjection_coe_unit")
Let $`N` be a star-closed multiplicative subobject of a star magma.  If $`N`
has an internal identity, then the ambient value of that identity is a star
projection.  In particular, this applies to star-stable nonunital subalgebras
of star rings.
:::

:::proof "lem:internal_unit_is_projection"
Idempotence is a unit law.  Apply the right unit law to the adjoint of the
identity and take adjoints to prove self-adjointness.  The formal theorem only
assumes `Mul`, `StarMul`, `SetLike`, `MulMemClass`, and `StarMemClass`; it has no
associative, additive, scalar, normed, or topological assumptions.  The
ultraweak left-ideal argument uses this public result.
:::

:::definition "def:nonunital_ultraweak_closure" (parent := "generated-nonunital-algebra") (lean := "Ultraweak.ofNonUnitalStarSubalgebra, Ultraweak.mem_ofNonUnitalStarSubalgebra, Ultraweak.ofNonUnitalStarSubalgebra_toSubmodule, NonUnitalStarSubalgebra.IsUltraweakClosed, NonUnitalStarSubalgebra.ultraweakClosure, NonUnitalStarSubalgebra.mem_ultraweakClosure, NonUnitalStarSubalgebra.ultraweakAdjoin")
For a nonunital star subalgebra $`S` of a C-star algebra with specified predual,
define its ultraweak transport, the predicate that it is ultraweakly closed,
its ultraweak closure, and the nonunital ultraweak star algebra generated by a
set.
:::

:::proposition "prop:nonunital_ultraweak_closure_api" (parent := "generated-nonunital-algebra") (lean := "NonUnitalStarSubalgebra.IsUltraweakClosed.norm_isClosed, NonUnitalStarSubalgebra.le_ultraweakClosure, NonUnitalStarSubalgebra.ultraweakClosure_minimal, NonUnitalStarSubalgebra.ultraweakClosure_eq_self, NonUnitalStarSubalgebra.subset_ultraweakAdjoin, NonUnitalStarSubalgebra.isUltraweakClosed_ultraweakAdjoin, NonUnitalStarSubalgebra.ultraweakAdjoin_le, NonUnitalStarSubalgebra.IsUltraweakClosed.nonUnitalCStarAlgebra, NonUnitalStarSubalgebra.IsUltraweakClosed.isUnital, NonUnitalStarSubalgebra.isUnital_ultraweakClosure, IsStarProjection.Corner.isUltraweakClosed_nonUnitalStarSubalgebra")
The nonunital ultraweak closure contains the original algebra, is ultraweakly
closed, and is minimal among ultraweakly closed nonunital star subalgebras
containing it.  It inherits a nonunital C-star algebra structure.  With a complete
predual it is internally unital, the ambient value of its identity is a star
projection, and ultraweak closure preserves commutativity.

This uses {uses "def:nonunital_ultraweak_closure"}[],
{uses "lem:wstar_unital"}[], and
{uses "lem:internal_unit_is_projection"}[].
:::

:::proof "prop:nonunital_ultraweak_closure_api"
Mirror the established unital ultraweak-closure API and reuse Mathlib's
topological closure for nonunital star subalgebras.  Internal unitality is an
application of the existing closed-submodule theorem to the underlying
submodule and its tautological linear isometry, not a second proof of Sakai's
unitality theorem.
:::

:::proposition "prop:support_mem_generated_wstar_Sak_1_10_4" (parent := "generated-nonunital-algebra") (lean := "WStarAlgebra.coe_unit_ultraweakAdjoin_singleton_eq_support, WStarAlgebra.support_mem_ultraweakAdjoin")
Let $`h=h^*` and let $`C` be the nonunital ultraweak star algebra generated
by $`h`.  Then $`s(h)\in C`.  More strongly, with the inherited nonunital
C-star algebra structure, the ambient value of $`C`'s internal identity is
$`s(h)`.

This uses {uses "lem:support_star_compatibility"}[],
{uses "prop:left_right_support_characterization"}[], and
{uses "prop:nonunital_ultraweak_closure_api"}[].
:::

:::proof "prop:support_mem_generated_wstar_Sak_1_10_4"
Let $`p\in C` be the internal identity.  Since $`ph=h`, leastness gives
$`s(h)\leq p`.  The element $`h` belongs to the projection corner
$`s(h)Ms(h)`, and that corner is already known to be ultraweakly closed.
Minimality therefore puts all of $`C`, in particular $`p`, in this corner;
thus $`s(h)p=p`.  Projection order also gives $`s(h)p=s(h)`, so $`p=s(h)`.
This proof reuses the corner API instead of rebuilding an annihilator-closure
argument.
:::

:::group "central-ideals"
Ultraweakly closed two-sided ideals and central projections.
:::

# Closed two-sided ideals and central projections
%%%
tag := "central-ideals"
%%%

Use Mathlib's bundled `TwoSidedIdeal M`.  Its underlying left and right ideals
are `TwoSidedIdeal.asIdeal` and `TwoSidedIdeal.asIdealOpposite`; ultraweak
closedness is imposed on their common underlying complex submodule.

:::proposition "prop:closed_two_sided_ideal_central_projection_Sak_1_10_5" (parent := "central-ideals") (lean := "TwoSidedIdeal.isClosed_asIdealOpposite, TwoSidedIdeal.existsUnique_isStarProjection_mem_center_eq_span_of_isClosed_ultraweak")
Every ultraweakly closed two-sided ideal $`J` of a W-star algebra $`M` has
the form $`J=Mz=zM` for a unique central projection $`z`.  Formally, $`J`
is a native `TwoSidedIdeal M`, and the conclusion identifies its underlying
left ideal with `Ideal.span {z}` and its opposite underlying left ideal with
`Ideal.span {MulOpposite.op z}`.

This uses {uses "prop:left_ideals_in_wstar_proj_Sak_1_10_1"}[],
{uses "cor:right_ideals_in_wstar_proj_Sak_1_10_1"}[], and
{uses "lem:ultraweak_op_homeomorph"}[].
:::

:::proof "prop:closed_two_sided_ideal_central_projection_Sak_1_10_5"
Apply the left-ideal classification.  Transport closedness through the
opposite-algebra homeomorphism and apply the right-ideal classification to get
projections $`z_\ell` and $`z_r`.  Both are identities on the same ideal, so
$`z_\ell=z_r=z`.  For $`x\in M`, both $`xz` and $`zx` lie in $`J`;
using $`z` as both identities gives $`xz=zxz=zx`.  Uniqueness comes from
either one-sided representation.
:::

:::corollary "cor:central_projection_closed_ideal_order_iso" (parent := "central-ideals") (lean := "TwoSidedIdeal.UltraweakClosed, TwoSidedIdeal.completeLatticeUltraweakClosed, IsStarProjection.Central, IsStarProjection.Central.span, IsStarProjection.Central.span_asIdeal, IsStarProjection.Central.span_asIdealOpposite, IsStarProjection.Central.span_le_span_iff, IsStarProjection.Central.centralGenerator, IsStarProjection.Central.centralGenerator_asIdeal, IsStarProjection.Central.centralGenerator_asIdealOpposite, IsStarProjection.Central.le_centralGenerator_iff_mem, IsStarProjection.Central.centralGenerator_mem, IsStarProjection.Central.centralGenerator_span, IsStarProjection.Central.orderIsoUltraweakClosedTwoSidedIdeal, IsStarProjection.Central.instCompleteLatticeCentralOfWStarAlgebra")
Central projections in $`M`, ordered by the ambient projection order, are
order-isomorphic to ultraweakly closed two-sided ideals via $`z\mapsto Mz`.
Consequently the subtype of central projections is a complete lattice.

This uses
{uses "prop:closed_two_sided_ideal_central_projection_Sak_1_10_5"}[] and
{uses "prop:proj_compl_lat_wstar_Sak_1_10_2"}[].
:::

:::proof "cor:central_projection_closed_ideal_order_iso"
Restrict the existing order isomorphism between projections and ultraweakly
closed left ideals.  The preceding proposition identifies which such ideals
are two-sided.  Arbitrary intersections remain closed and two-sided, so the
same infimum construction transports the complete lattice.  Use a subtype of
Mathlib's projection subtype together with membership in `Set.center`, rather
than introduce new notions of projection or centrality.
:::

:::definition "def:central_support_Sak_1_10_6" (parent := "central-ideals") (lean := "IsStarProjection.Central.oneSub, IsStarProjection.Central.oneSub_val, IsStarProjection.Central.oneSub_oneSub, WStarAlgebra.centralSupport")
If $`p` is a projection in $`M`, its _central support_ $`c(p)` is the
infimum, in the complete lattice of central projections, of all central
projections $`z` satisfying $`p\leq z`.

This uses {uses "cor:central_projection_closed_ideal_order_iso"}[].
:::

:::proposition "prop:central_support_characterization" (parent := "central-ideals") (lean := "WStarAlgebra.le_centralSupport, WStarAlgebra.centralSupport_le_iff, WStarAlgebra.centralSupport_mono, WStarAlgebra.centralSupport_central, WStarAlgebra.centralSupport_idem, WStarAlgebra.centralSupport_eq_iff_mem_center")
The central support $`c(p)` is central, $`p\leq c(p)`, and for every central
projection $`z`,
$`c(p)\leq z\Longleftrightarrow p\leq z`.  The operation $`c` is monotone
and idempotent, and $`c(p)=p` precisely when $`p` is central.

This uses {uses "def:central_support_Sak_1_10_6"}[].
:::

:::proof "prop:central_support_characterization"
The order isomorphism constructs a least central majorant by classifying the
ultraweakly closed two-sided annihilator of the principal right ideal generated
by $`p`.  This proves that the displayed infimum is itself above $`p`; the
remaining leastness, monotonicity, idempotence, and fixed-point laws are then
order-theoretic.  The complete-lattice instance preserves the ambient subtype
order definitionally.
:::

:::group "central-orthogonality"
Orthogonality of central supports.
:::

# Orthogonality of central supports
%%%
tag := "central-orthogonality"
%%%

:::lemma_ "lem:projection_mul_eq_zero_iff_le_complement" (parent := "central-orthogonality") (lean := "IsStarProjection.mul_eq_zero_iff_le_one_sub")
If $`p` and $`q` are projections in a unital C-star algebra, then
$`pq=0\Longleftrightarrow p\leq 1-q`.  Equivalently, two projections are
disjoint in the projection order exactly when their product is zero.

This uses {uses "lem:proj_sub_pos_iff_comm_eq_self"}[].
:::

:::proof "lem:projection_mul_eq_zero_iff_le_complement"
Apply the existing characterization $`p\leq r\Longleftrightarrow pr=p` to
$`r=1-q` and expand $`p(1-q)`.  This belongs in the general C-star algebra
projection API and is not specialized to W-star algebras.
:::

:::proposition "prop:central_support_orthogonal_Sak_1_10_7" (parent := "central-orthogonality") (lean := "WStarAlgebra.centralSupport_mul_centralSupport_eq_zero_of_forall_mul_mul_eq_zero")
Let $`p,q` be projections in a W-star algebra $`M`.  If $`pxq=0` for every
$`x\in M`, then $`c(p)c(q)=0`.

This uses {uses "def:two_sided_annihilators"}[],
{uses "lem:annihilators_ultraweak_closed"}[],
{uses "prop:closed_two_sided_ideal_central_projection_Sak_1_10_5"}[],
{uses "prop:central_support_characterization"}[], and
{uses "lem:projection_mul_eq_zero_iff_le_complement"}[].
:::

:::proof "prop:central_support_orthogonal_Sak_1_10_7"
Let $`J` be the two-sided annihilator of the right ideal $`pM`.  The
hypothesis says $`q\in J`, and $`J` is ultraweakly closed.  Write $`J=Mz`
for a central projection $`z`.  Then $`q\leq z` and $`c(q)\leq z`, so
$`pc(q)=0`.  Hence $`p\leq 1-c(q)`; since the complement is central,
minimality gives $`c(p)\leq 1-c(q)`, equivalently $`c(p)c(q)=0`.
:::

:::corollary "cor:central_support_orthogonal_iff" (parent := "central-orthogonality") (lean := "WStarAlgebra.centralSupport_mul_centralSupport_eq_zero_iff")
For projections $`p,q` in $`M`,
$`c(p)c(q)=0\Longleftrightarrow (\forall x\in M,\;pxq=0)`.

This uses {uses "prop:central_support_orthogonal_Sak_1_10_7"}[] and
{uses "prop:central_support_characterization"}[].
:::

:::proof "cor:central_support_orthogonal_iff"
One direction is the preceding proposition.  Conversely use
$`p\leq c(p)`, $`q\leq c(q)`, and centrality to insert $`c(p)` and
$`c(q)` into $`pxq`; the product vanishes because $`c(p)c(q)=0`.  This
equivalence is the reusable API form of Sakai's proposition.
:::
