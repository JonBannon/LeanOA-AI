# Workstreams

All active streams are governed by `SAKAI_DESIGN_CONTRACT.md`. The baseline is `92db74d` on
`master`; worktree and branch names are filled in when launched.

## Candidate theorem clusters

Scores are qualitative: low/medium/high.

| Candidate | Dependency level | API stability | Downstream payoff | Collision risk | Difficulty | Independent? |
| --- | --- | --- | --- | --- | --- | --- |
| Spectral-band projection/order/orthogonality lemmas | current `SpectralProjection` | GREEN→YELLOW helper API | high for sums and measures | low | medium | yes |
| Tagged spectral sums and mesh estimate | current `SpectralSum` | GREEN→YELLOW helper API | high for integral packaging | low | medium-high | yes |
| Generic monotone projection-family finite-sum lemmas | Mathlib projection/order | YELLOW | medium-high | medium | medium | yes, if no bundled structure |
| Spectral integral interface | all completed spectral files | RED | very high | high | high | architecture only |
| Set-indexed spectral resolution / PVM | projection lattice + measure theory | RED | very high | very high | very high | no |
| Uniqueness portion of Sakai 1.11.3 | spectral representation interface | RED/unavailable | high | high | high | not yet |
| Recovering norm from states (legacy future node) | positive functionals | GREEN/YELLOW | medium | low | medium | yes |
| Pure-state/extreme-point TODO cluster | positive functionals + `Extreme` | YELLOW | medium | medium | high | possibly |
| Systematic Verso typography migration | docs only | GREEN | presentation | low | low | yes |
| Annihilator/upstream cleanup | ideals | human-gated RED | medium | high | medium | no |

The first two theorem clusters are selected because they consume the completed spectral frontier,
can live in separate new modules, directly reduce distance to the spectral-integral checkpoint, and
do not require choosing the RED measure interface. Mathlib reconnaissance runs beside them; the lead
owns architecture/integration. Verso review follows as soon as an agent slot opens.

## Active streams

### Lead architecture and integration

- **Owner:** lead agent
- **Scope:** coordination layer, design enforcement, IQ-001, review, integration, full validation
- **Owned files:** `docs/development/`, umbrella/import changes during integration
- **Forbidden:** silently settling the human-gated ideal representation or inventing a PVM API
- **Status:** ACTIVE

### Mathlib spectral/integration reconnaissance

- **Owner:** first-wave worker
- **Scope:** pinned/current Mathlib search, existing Sak-AI overlap, exact options for integral
  packaging; update only its report in its worktree
- **Dependencies:** read-only theorem library and design records
- **Status:** READY

### Spectral-band theorem cluster

- **Owner:** first-wave worker
- **Scope:** bounded projection, order, commutation, and orthogonality facts derived from the existing
  `spectralProjectionIio`; prefer generic existing Mathlib lemmas and no new foundational structure
- **Owned modules:** one new spectral-band module plus a worker report
- **Status:** READY

### Tagged spectral-sum theorem cluster

- **Owner:** first-wave worker
- **Scope:** tagged sums with tags inside adjacent cuts, bracketing/error estimates, and convergence
  consequences where possible; no integral or measure definition
- **Owned modules:** one new tagged-sum module plus a worker report
- **Status:** READY

### Verso exposition audit

- **Owner:** second-wave worker
- **Scope:** declaration-link and typography audit; document only integrated results
- **Owned modules:** `docs/SakAIDocs/` and an audit report
- **Status:** QUEUED pending an agent slot and integration-ready Lean declarations
