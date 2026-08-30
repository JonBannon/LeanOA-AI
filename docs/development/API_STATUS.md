# Shared API status

Status reflects integration review through the first spectral parallel wave (2026-08-30), not a
promise of permanent immutability.

## GREEN — stable downstream surfaces

| Area | Principal modules | Why stable / consumers |
| --- | --- | --- |
| Weak-duality and specified-predual bridges | `IsWeak`, `Ultraweak.Basic`, `Ultraweak.Dual`, `Ultraweak.WStarAlgebra` | Named maps and compatibility interfaces underpin most ultraweak work. Changes require deliberate migration, but current clients may depend on them. |
| Ultraweak algebra operations | `Ultraweak.Algebra`, `ContinuousStar`, `Multiplication`, `Strong` | Established topology-facing operation API used by normality, density, ideals, and support. |
| Projection lattice and support | `ProjectionLattice`, `Support`, `Corner` | Completed Section 1.10 and current spectral construction consume these interfaces. |
| Ideals and central support | `Annihilator`, `Ideal`, `TwoSidedIdeal`, `CentralSupport`, `Opposite` | Completed, documented native-object API. The alternative upstream representation remains a separate review question. |
| Lower spectral projections | `CStarAlgebra.Spectral`, `Ultraweak.SpectralProjection` | Half-line semantics and naming are intentionally fixed; current finite sums depend on them. |
| Finite spectral sums, bands, and convergence | `Ultraweak.SpectralSum`, `Ultraweak.SpectralApproximation`, `Ultraweak.SpectralBand`, `Ultraweak.TaggedSpectralSum` | Checked theorem-level frontier, including arbitrary tagged sums and explicit norm-to-ultraweak convergence. These modules deliberately commit to no spectral-measure representation. |
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
| Set-indexed spectral resolution / projection-valued measure | lead architecture | The next frontier needs integral notation, but the correct relationship to Mathlib measure APIs is not yet established. | Pinned/current Mathlib audit, concrete consumer requirements, and a reviewed decision record. |
| Operator-valued spectral integral | lead architecture | Choosing Bochner integration, an operator-valued measure, or a Riemann–Stieltjes completion now would be expensive to reverse. | A minimal canonical representation theorem can be stated without a competing measure theory. |
| Alternative `TwoSidedIdeal` representation or instance refactor | human review + architecture | `REVIEW_QUEUE.md` records two materially different designs. | Human decision or upstream Mathlib resolution. |
| Foundational predual/representation instance redesign | human review + architecture | Junction API with broad downstream dependence and explicit anti-definitional-equality constraints. | A documented migration with compatibility proof and downstream validation. |
