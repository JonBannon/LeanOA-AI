# Shared API status

Status reflects integration review through the first Sakai 1.12 production wave (2026-08-31),
whose WS-1/WS-3 checkpoint is `6d24a2feb704cae6e4bedc00d6bc9f17c601f310`. This is not a
promise of permanent immutability.

## GREEN — stable downstream surfaces

| Area | Principal modules | Why stable / consumers |
| --- | --- | --- |
| Weak-duality and specified-predual bridges | `IsWeak`, `Ultraweak.Basic`, `Ultraweak.Dual`, `Ultraweak.WStarAlgebra` | Named maps and compatibility interfaces underpin most ultraweak work. Changes require deliberate migration, but current clients may depend on them. |
| Ultraweak and intrinsic strong topology | `Ultraweak.Algebra`, `ContinuousStar`, `Multiplication`, `Strong`, `StrongProjection` | Established topology-facing API. Projection domination plus ultraweak convergence now has a reusable strong upgrade, and directed projection LUBs converge strongly. |
| Fixed-projection ultraweak decomposition | `Ultraweak.ProjectionDecomposition` | General ordered-C-star theorem layer: a fixed extraction identity separates an ultraweak difference limit and identifies positive/negative parts under eventual positivity. It introduces no spectral-family abstraction. |
| Projection lattice and support | `ProjectionLattice`, `Support`, `Corner` | Completed Section 1.10 and current spectral construction consume these interfaces. Support leastness, projection simp lemmas, and the positive-scalar projection lower-bound criterion are stable consumers of the same support object. |
| Ideals and central support | `Annihilator`, `Ideal`, `TwoSidedIdeal`, `CentralSupport`, `Opposite` | Completed, documented native-object API. The alternative upstream representation remains a separate review question. |
| Lower spectral projections | `CStarAlgebra.Spectral`, `Ultraweak.SpectralProjection`, `Ultraweak.SpectralProjectionStrong` | Half-line semantics and naming are intentionally fixed. Sakai 1.11.1 is source-formalized in `s(M,M_*)` without an extra monotonicity hypothesis; current finite sums depend on the same projection object. |
| Finite spectral sums, bands, and convergence | `Ultraweak.SpectralSum`, `Ultraweak.SpectralApproximation`, `Ultraweak.SpectralBand`, `Ultraweak.TaggedSpectralSum`, `Ultraweak.TruncatedSpectralSum` | Checked theorem-level frontier, including arbitrary tagged sums, sharp truncated-affine mesh estimates with an unaligned cutoff, and explicit norm-to-ultraweak convergence to the existing CFC target. These modules deliberately commit to no spectral-measure representation. |
| Polar-decomposition foundations | `Mathlib.Analysis.CStarAlgebra.Abs`, `Mathlib.Analysis.CStarAlgebra.Projection`, `Ultraweak.AbsSupport` | `CFC.abs_mul_eq_zero_iff` and `CFC.mul_abs_eq_zero_iff` are the stable nonunital $C^*$-annihilator bridges. `IsStarProjection.mul_star_mul_self`, `mul_star_mul_self_assoc`, and `mul_star_self` are the stable partial-isometry consequences. `WStarAlgebra.support_abs` is the canonical simp rewrite and `WStarAlgebra.support_abs_star` is the named starred rewrite; they use the existing support object and add no normality or explicit-predual assumption. |
| Verso package architecture | `docs/SakAIDocs`, `scripts/build-verso-site.sh` | Sole documentation source with verified migration parity and checked declaration links. |

## YELLOW — evolving, consume cautiously

| Area | Owner | Reason / consumers | Stabilization criterion |
| --- | --- | --- | --- |
| Mirrored Mathlib extension layer | architecture + Mathlib reconnaissance | Some declarations may move upstream or be replaced by newer Mathlib APIs. | Per-module overlap audit and a migration plan for any upstream replacement. |
| Positive-functional / representation assembly | architecture | Sak-AI uses Mathlib GNS plus local functional APIs, but has no separate broad representation layer. | A real Sakai consumer demonstrates the missing interface and design review chooses its home. |
| Legacy mathematical typography in Verso | Verso stream | Existing source consistently uses older plain-text forms; new prose follows the recorded convention. | One systematic documentation-only migration, not scattered edits. |

## RED — architecture owner only

| Area | Owner | Reason / downstream pressure | Stabilization criterion |
| --- | --- | --- | --- |
| Arbitrary lower spectral resolution and its relationship to a set-indexed projection-valued measure | lead architecture | A refinement-plus-mesh finite-cut candidate, prescribed-cut stability, and complete pointwise/family uniqueness are kernel-checked in scratch. The source audit proves that Sakai uses `s(M,M_*)`, not `σ(M,M_*)`, but classifies the undefined integral semantics LEVEL C. Strong convergence of the same candidate net is checked to imply the existing ultraweak hypotheses. | Do not publish the candidate as Sakai's semantics. A future PVM must induce the intrinsic laws and a precisely stated representation by lower-half-line restriction. |
| Operator-valued spectral integral | lead architecture | D002's candidates remain inadequate. The refinement transaction removes the technical cofinality, endpoint, mesh, and support blockers for a clarified modern theorem, while the historical term remains genuinely ambiguous. | Stabilize only when a genuine mathematical consumer or a coherent PVM construction fixes the interface; never label the checked candidate as Sakai's definition. |
| Alternative `TwoSidedIdeal` representation or instance refactor | human review + architecture | `REVIEW_QUEUE.md` records two materially different designs. | Human decision or upstream Mathlib resolution. |
| Foundational predual/representation instance redesign | human review + architecture | Junction API with broad downstream dependence and explicit anti-definitional-equality constraints. | A documented migration with compatibility proof and downstream validation. |
