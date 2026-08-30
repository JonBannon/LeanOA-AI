# Shared API status

Status reflects integration review through the truncated-affine recovery transaction (2026-08-30),
not a promise of permanent immutability.

## GREEN — stable downstream surfaces

| Area | Principal modules | Why stable / consumers |
| --- | --- | --- |
| Weak-duality and specified-predual bridges | `IsWeak`, `Ultraweak.Basic`, `Ultraweak.Dual`, `Ultraweak.WStarAlgebra` | Named maps and compatibility interfaces underpin most ultraweak work. Changes require deliberate migration, but current clients may depend on them. |
| Ultraweak algebra operations | `Ultraweak.Algebra`, `ContinuousStar`, `Multiplication`, `Strong` | Established topology-facing operation API used by normality, density, ideals, and support. |
| Projection lattice and support | `ProjectionLattice`, `Support`, `Corner` | Completed Section 1.10 and current spectral construction consume these interfaces. |
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
| Arbitrary lower spectral resolution and its relationship to a set-indexed projection-valued measure | lead architecture | The canonical truncated-affine theorem now identifies the exact CFC target, and a scratch arbitrary-family theorem works under exact finite endpoints plus norm moment convergence. Those hypotheses are stronger than Sakai's ultraweak representation and do not recover unsampled family values. | A source-faithful fixed-projection ultraweak decomposition, continuity-from-below argument, and insertion-at-the-cut theorem recover support without assuming it. A future PVM must then induce the accepted intrinsic laws by lower-half-line restriction. |
| Operator-valued spectral integral | lead architecture | D002's candidates remain inadequate; the new CFC-compatible theorem does not supply an ultraweak integral for an arbitrary family, and support is not continuous under norm or ultraweak limits. | Source-faithful resolution laws and support recovery must be kernel-checked before any integral or measurable-calculus interface is stabilized. |
| Alternative `TwoSidedIdeal` representation or instance refactor | human review + architecture | `REVIEW_QUEUE.md` records two materially different designs. | Human decision or upstream Mathlib resolution. |
| Foundational predual/representation instance redesign | human review + architecture | Junction API with broad downstream dependence and explicit anti-definitional-equality constraints. | A documented migration with compatibility proof and downstream validation. |
