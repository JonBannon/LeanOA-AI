# Workstreams

All streams are governed by `SAKAI_DESIGN_CONTRACT.md`. Reconnaissance began at `92db74d`; the
parallel implementation worktrees were cut from coordination baseline `463d37e` on `master`.

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
- **Status:** COMPLETE; focused/full Lean validation, lint, the stable Verso build, and the manifest
  check all pass

### Mathlib spectral/integration reconnaissance

- **Owner:** `mathlib_spectral_audit`
- **Scope:** pinned/current Mathlib search, existing Sak-AI overlap, exact options for integral
  packaging; update only its report in its worktree
- **Dependencies:** read-only theorem library and design records
- **Worktree/branch:** `/private/tmp/sakai-agent-mathlib-463d37e`, `agent/mathlib-spectral`
- **Status:** COMPLETE and integrated as `4cf9ded`; found no suitable PVM/integral replacement and
  recommended the theorem-level ultraweak limit bridge

### Spectral-band theorem cluster

- **Owner:** `spectral_bands`
- **Scope:** bounded projection, order, commutation, and orthogonality facts derived from the existing
  `spectralProjectionIio`; prefer generic existing Mathlib lemmas and no new foundational structure
- **Owned modules:** one new spectral-band module plus a worker report
- **Worktree/branch:** `/private/tmp/sakai-agent-bands-463d37e`, `agent/spectral-bands`
- **Status:** COMPLETE; worker commit `d50aa7a` integrated as `c9e18f8`, then architecture extracted
  the generic nonunital projection lemma and revalidated the focused module

### Tagged spectral-sum theorem cluster

- **Owner:** `tagged_spectral_sums`
- **Scope:** tagged sums with tags inside adjacent cuts, bracketing/error estimates, and convergence
  consequences where possible; no integral or measure definition
- **Owned modules:** one new tagged-sum module plus a worker report
- **Worktree/branch:** `/private/tmp/sakai-agent-tagged-463d37e`,
  `agent/tagged-spectral-sums`
- **Status:** COMPLETE proposal integrated by the lead; endpoint-tag bridges and the named
  ultraweak convergence corollary were added during integration review

### Verso spectral-frontier audit

- **Owner:** `verso_spectral_audit`
- **Scope:** declaration-link and typography audit; document only integrated results
- **Owned modules:** read-only public Verso audit and
  `docs/development/reports/VERSO_SPECTRAL_AUDIT.md`
- **Status:** COMPLETE; recommended and checked the three-node mathematical presentation, direct
  declaration imports, current-frontier update, and measured-count validation

### Independent integration review

- **Owner:** `integration_review`
- **Scope:** read-only mathematical/API review of the general projection, spectral-band, and tagged
  sum changes
- **Status:** COMPLETE; no correctness blockers, requested the two endpoint-tag bridges and
  identified the exact current-Mathlib signature migration for the order-interval norm lemma

## Spectral-integral interface scratch transaction

This bounded transaction starts at `397e006`. It compares, in disposable worktrees, a generic
tagged-partition convergence predicate with a spectral-family-specific predicate. Experimental
definitions remain outside public imports and Verso; the lead will integrate only a decision record
and any independently justified coordination updates.

### Generic tagged-partition prototype

- **Owner:** `spectral_integral_generic`
- **Scope:** Candidate A and its eight required stress tests
- **Owned files:** scratch files and private worker report in its isolated worktree
- **Worktree/branch:** `/private/tmp/sakai-spectral-integral-generic-af7e794`,
  `agent/spectral-integral-generic`
- **Status:** COMPLETE at local commit `0ee56d4`; kernel checks pass, no placeholders, not integrated
  or pushed

### Spectral-family-specific prototype

- **Owner:** `spectral_integral_specific`
- **Scope:** Candidate B, weighted spectral sums, identity comparison, and stress tests
- **Owned files:** scratch files and private worker report in its isolated worktree
- **Worktree/branch:** `/private/tmp/sakai-spectral-integral-specific-af7e794`,
  `agent/spectral-integral-specific`
- **Status:** COMPLETE at local commit `30f266a`; kernel checks pass, no placeholders, not integrated
  or pushed

### Independent prototype review

- **Owner:** `spectral_integral_review`
- **Scope:** compare both candidates and perform only targeted Mathlib/original-LeanOA review
- **Owned files:** private comparison proof and review report in its isolated worktree
- **Worktree/branch:** `/private/tmp/sakai-spectral-integral-review-af7e794`,
  `agent/spectral-integral-review`
- **Status:** COMPLETE at local commit `0bf4f0c`; proved all-integrands equivalence and recommended
  Outcome 3, with no public candidate and no push

### Lead architecture and integration

- **Owner:** lead agent
- **Scope:** contracts, cross-prototype equivalence test, D002 decision, coordination updates, and
  validation
- **Status:** COMPLETE; D002 records the decision to publish neither candidate, and `lake build`
  (3112 jobs) plus `lake lint` pass on the integration branch

## Truncated-affine recovery transaction

This bounded transaction starts at `d4db7b0`. It treats Mathlib CFC as the canonical continuous
calculus, seeks theorem-level truncated-affine recovery, and tests only scratch lower-family
interfaces compatible with a future PVM. No stream may publish a general integral, PVM, or
term-dependent spectral-resolution typeclass.

### Canonical truncated-affine theorem

- **Owner:** `truncated_affine_canonical`
- **Scope:** pinned CFC audit needed by the proof, partial-interval estimate, canonical norm and
  specified-ultraweak convergence, CFC target identification
- **Owned files:** isolated scratch/report files and at most one proposed theorem-level production
  module
- **Worktree/branch:** `/private/tmp/sakai-truncated-affine-canonical-b20209b`,
  `agent/truncated-affine-canonical`
- **Status:** COMPLETE at worker commit `18ddb9a`; production module integrated as `80bc2d8`.
  The sharp mesh theorem permits the cutoff to lie inside a band and targets the existing CFC
  positive part. The Verso follow-up was integrated as `2d43874`. No new structure was introduced.

### Arbitrary competing resolution

- **Owner:** `competing_resolution`
- **Scope:** explicit-hypothesis replay for `e'`, minimum assumption ledger, circularity audit
- **Owned files:** isolated scratch files and private worker report
- **Worktree/branch:** `/private/tmp/sakai-competing-resolution-b20209b`,
  `agent/competing-resolution`
- **Status:** COMPLETE scratch result at local commit `de8e2bb`; not integrated or pushed. The
  finite algebraic theorem generalized, but the norm-convergent moment and exact endpoint route is
  stronger than Sakai's ultraweak hypotheses and does not recover support. Its consolidated
  assumption-ledger follow-up was integrated as `9dcf1f5`.

### Support recovery and CFC/PVM audit

- **Owner:** `support_cfc_pvm`
- **Scope:** support theorem and endpoint convention, pinned/current CFC architecture, future-PVM
  refactorability and ultraweak-transfer analysis
- **Owned files:** isolated scratch files and private worker report
- **Worktree/branch:** `/private/tmp/sakai-support-cfc-pvm-b20209b`,
  `agent/support-cfc-pvm`
- **Status:** COMPLETE scratch/audit result at local commit `f5daad0`; not integrated or pushed.
  It fixed the strict `Iio` endpoint convention, isolated the order/continuity hypotheses needed
  for support recovery, and confirmed that support cannot be passed through norm limits. Its D003
  and compatibility-report follow-up was integrated as `9781e55`.

### Lead architecture and integration

- **Owner:** lead agent
- **Scope:** contracts, source fidelity, proof review, minimality/generalization review, D003,
  assumption and compatibility reports, coordination updates, full validation
- **Status:** COMPLETE; the theorem layer, named CFC bridge, umbrella import, Verso node, D003, and
  required reports are integrated. Lower-family, resolution, PVM, and integral structures remain
  RED and unpublished. Focused/full Lean validation, lint, and the Verso build/check pass.

## Fixed-projection spectral-uniqueness transaction

This bounded transaction starts at `162271a`. It reconstructs and tests the fixed-projection
ultraweak proof in the uniqueness clause of Sakai 1.11.3. Mathlib CFC remains canonical, every
competing-family hypothesis stays explicit, and no stream may publish a resolution, integral, or
PVM abstraction independently.

### Sakai source and finite cutoff decomposition

- **Owner:** `uniqueness_source_finite`
- **Scope:** exact source audit, insertion of `r`, finite band/projection identities, hypothesis
  provenance
- **Owned files:** isolated scratch Lean and private worker report
- **Status:** COMPLETE at scratch commit `6e349da`; the source/finite report is integrated at
  `017eff6` and the consolidated eight-column hypothesis ledger at `6b62428`. The finite proof
  retains the left-endpoint residual and uses the strict `Iio`/`Ico` atom convention.

### Fixed-projection ultraweak/order infrastructure

- **Owner:** `fixed_projection_ultraweak`
- **Scope:** fixed multiplication through specified-ultraweak limits, closed order, reusable
  topology facts, Mathlib overlap
- **Owned files:** isolated scratch/report and at most one reviewed general production proposal
- **Status:** COMPLETE at worker commit `c637cb7`; the audit report and `support_le_iff` are
  integrated. Existing separate multiplication and closed-order APIs were reused rather than
  wrapped. Architecture review accepted the stronger total-only decomposition for production in
  `Ultraweak.ProjectionDecomposition`.

### Competing-family support recovery

- **Owner:** `competing_support_recovery`
- **Scope:** both support inequalities, continuity-from-below, endpoint convention, and uniqueness
  under explicit source-faithful hypotheses
- **Owned files:** isolated scratch Lean and private worker report
- **Status:** COMPLETE at scratch commit `b25d751`; the report is integrated at `017eff6`.
  Both support inequalities, the `Iio` LUB step, support equality, and pointwise/family uniqueness
  kernel-check conditional on explicit inserted-cut approximation data.

### Lead architecture and integration

- **Owner:** lead agent
- **Scope:** source-fidelity review, contracts, dependency-aware proof integration, hypothesis
  ledger, public API decision, Verso only for production mathematics, full validation
- **Status:** COMPLETE; D004 accepts the generic decomposition and support helpers, rejects a
  premature resolution/PVM/integral structure, and identifies the exact remaining
  Radon--Stieltjes/refinement bridge. The 3,114-job theorem build, `lake lint`, and the Verso
  build/check pass; the generated graph has 103 nodes and 175 edges with 492 manifest entries.

## Radon--Stieltjes refinement-bridge transaction

This bounded transaction starts at `0e5a794`. It audits existing Riemann--Stieltjes formalizations
before local implementation, then tests the smallest refinement-directed semantics capable of
closing Sakai 1.11.3 under asymptotic endpoints and ultraweak convergence. Mathlib CFC remains
canonical. No stream may publish a PVM, general integral, or competing resolution independently.

### External Riemann--Stieltjes audit

- **Owner:** `rs_external_audit`
- **Scope:** PNT+, `teorth/analysis`, pinned/current Mathlib, original LeanOA, provenance, and exact
  reuse classification
- **Owned files:** one isolated external-audit report
- **Status:** COMPLETE and integrated as `9ce196c`; exact versions, licenses, declarations,
  placeholders, endpoint conventions, and reuse classifications are recorded in the required
  eight-column report

### Division/refinement/cofinality

- **Owner:** `rs_refinement`
- **Scope:** generic finite divisions, refinement, finite prescribed cuts, common refinement,
  cofinality, and generic limit restriction
- **Owned files:** isolated scratch/report and at most one reviewed generic production proposal
- **Status:** COMPLETE in scratch; `948b7c4` reuses Mathlib's `Ici`/`atTop` cofinality and proves
  richer-filter eventual-identity insertion, while `f7bd0bd` supplies the sorted finite-cut and
  asymptotic-endpoint adapter. No production proposal was accepted.

### Source-faithful Radon--Stieltjes bridge

- **Owner:** `rs_bridge`
- **Scope:** moment sums, asymptotic endpoint residuals, representation filter, inserted-cut
  translated limit, and compatibility with the existing conditional support proof
- **Owned files:** isolated scratch/report; no public integral/resolution structure
- **Status:** COMPLETE conditionally in scratch; `8ced075` proves the abstract translated-moment
  and endpoint-residual bridge, and `f431754` proves a nontrivial concrete filter combining
  refinement, shrinking mesh, endpoint escape, and prescribed-cut invariance. Source equivalence
  remains OPEN / RED.

### Lead architecture, uniqueness integration, and Verso

- **Owner:** lead agent
- **Scope:** external-reuse decision, shared API ownership, integration of the conditional support
  proof, completion of Sakai 1.11.3 if source hypotheses close, public API judgment, Verso, and full
  validation
- **Status:** CONDITIONAL PROOF COMPLETE / SOURCE REVIEW ACTIVE; `9ec05eb` and `5b719f1` assemble
  finite indices, support recovery, pointwise identification, and family
  uniqueness under the explicit candidate moment limit. Nothing became public or entered Verso;
  the full theorem build, lint, scratch checks, Verso/blueprint build and check, manifest checks,
  and placeholder scan all pass.
