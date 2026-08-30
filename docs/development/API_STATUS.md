# Shared API status

Status reflects integration review through the fixed-projection ultraweak decomposition transaction
(2026-08-30), not a promise of permanent immutability.

## GREEN — stable downstream surfaces

| Area | Principal modules | Why stable / consumers |
| --- | --- | --- |
| Weak-duality and specified-predual bridges | `IsWeak`, `Ultraweak.Basic`, `Ultraweak.Dual`, `Ultraweak.WStarAlgebra` | Named maps and compatibility interfaces underpin most ultraweak work. Changes require deliberate migration, but current clients may depend on them. |
| Ultraweak algebra operations | `Ultraweak.Algebra`, `ContinuousStar`, `Multiplication`, `Strong` | Established topology-facing operation API used by normality, density, ideals, and support. |
| Fixed-projection ultraweak decomposition | `Ultraweak.ProjectionDecomposition` | General ordered-C-star theorem layer: a fixed extraction identity separates an ultraweak difference limit and identifies positive/negative parts under eventual positivity. It introduces no spectral-family abstraction. |
| Projection lattice and support | `ProjectionLattice`, `Support`, `Corner` | Completed Section 1.10 and current spectral construction consume these interfaces. Support leastness, projection simp lemmas, and the positive-scalar projection lower-bound criterion are stable consumers of the same support object. |
| Ideals and central support | `Annihilator`, `Ideal`, `TwoSidedIdeal`, `CentralSupport`, `Opposite` | Completed, documented native-object API. The alternative upstream representation remains a separate review question. |
| Lower spectral projections | `CStarAlgebra.Spectral`, `Ultraweak.SpectralProjection` | Half-line semantics and naming are intentionally fixed; current finite sums depend on them. |
| Finite spectral sums, bands, and convergence | `Ultraweak.SpectralSum`, `Ultraweak.SpectralApproximation`, `Ultraweak.SpectralBand`, `Ultraweak.TaggedSpectralSum`, `Ultraweak.TruncatedSpectralSum` | Checked theorem-level frontier, including arbitrary tagged sums, sharp truncated-affine mesh estimates with an unaligned cutoff, and explicit norm-to-ultraweak convergence to the existing CFC target. These modules deliberately commit to no spectral-measure representation. |
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
| Arbitrary lower spectral resolution and its relationship to a set-indexed projection-valued measure | lead architecture | Finite cutoff algebra and the complete support/uniqueness implication are kernel-checked under explicit approximation data, but Sakai's abstract representation has no division-independent Lean semantics. | Prove that a refinement-directed representation is stable under insertion of arbitrary cuts and supplies the exact moment and residual nets. A future PVM must induce the accepted intrinsic laws by lower-half-line restriction. |
| Operator-valued spectral integral | lead architecture | D002's candidates remain inadequate. D004 isolates the missing operation as an ultraweak Radon--Stieltjes representation/refinement bridge, not another CFC or support theorem. | A source-faithful division/refinement semantics must produce the checked support-recovery inputs before any integral or measurable-calculus interface is stabilized. |
| Alternative `TwoSidedIdeal` representation or instance refactor | human review + architecture | `REVIEW_QUEUE.md` records two materially different designs. | Human decision or upstream Mathlib resolution. |
| Foundational predual/representation instance redesign | human review + architecture | Junction API with broad downstream dependence and explicit anti-definitional-equality constraints. | A documented migration with compatibility proof and downstream validation. |
