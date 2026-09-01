# Workstreams

All streams are governed by `SAKAI_DESIGN_CONTRACT.md`. Reconnaissance began at `92db74d`; the
parallel implementation worktrees were cut from coordination baseline `463d37e` on `master`.

## Candidate theorem clusters

Scores are qualitative: low/medium/high.

| Candidate | Dependency level | API stability | Downstream payoff | Collision risk | Difficulty | Independent? |
| --- | --- | --- | --- | --- | --- | --- |
| Spectral-band projection/order/orthogonality lemmas | current `SpectralProjection` | GREEN→YELLOW helper API | high for sums and measures | low | medium | yes |
| Tagged spectral sums and mesh estimate | current `SpectralSum` | GREEN→YELLOW helper API | high for integral packaging | low | medium-high | yes |
| Orthogonal projection-family finite-sum net | projection lattice + strong LUB | YELLOW | high for Sakai 1.13 | low | medium | yes, if no competing sum object |
| Source normality bridge | existing normality characterization | YELLOW | high for Sakai 1.13 | low | medium | yes |
| Complete-additivity equivalence | source normality + orthogonal sums | YELLOW | high for Sakai 1.13 | medium | medium-high | reconnaissance first |
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
  stronger than Sakai's actual strong-topology/asymptotic-endpoint hypotheses and does not recover
  support. Its consolidated
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

This bounded transaction starts at `162271a`. It reconstructs and tests an ultraweak
topology-forgotten version of the fixed-projection proof in the uniqueness clause of Sakai 1.11.3.
The source topology was later corrected to strong `s(M,M_*)`. Mathlib CFC remains canonical, every
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
  under explicit topology-forgotten approximation hypotheses
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
  Radon--Stieltjes/refinement bridge. The 3,116-job theorem build, `lake lint`, and the Verso
  build/check pass; after the 1.11.1 source-faithful update the generated graph has 103 nodes and
  176 edges with 496 manifest entries.

## Radon--Stieltjes refinement-bridge transaction

This bounded transaction starts at `0e5a794`. It audits existing Riemann--Stieltjes formalizations
before local implementation, then tests a refinement-directed semantics capable of closing a
clarified ultraweak analogue under asymptotic endpoints. The source was later confirmed to use the
strong `s(M,M_*)` topology. Mathlib CFC remains canonical. No stream may publish a PVM, general
integral, or competing resolution independently.

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

### Candidate Radon--Stieltjes bridge

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

## Abstract Radon--Stieltjes source-certification transaction

This bounded transaction starts at `5a05cbf`. It audits Sakai internally and traces the historical
terminology before deciding whether the checked candidate may be promoted. No stream may infer
source semantics from implementation convenience or add an axiom/placeholder.

### Sakai internal source audit

- **Owner:** `sakai_internal_audit`
- **Scope:** all of Sakai, the local theorem, notation, index, cross-references, bibliography, and
  division/endpoint evidence
- **Status:** COMPLETE. Direct high-resolution inspection corrects the topology to strong
  `s(M,M_*)`; the book gives finite ordered cuts, endpoint sums, gap control, and the `Iio`/`Ico`
  convention, but no net/filter, refinement order, arbitrary-tag, or improper-limit definition.

### Historical terminology audit

- **Owner:** `historical_rs_audit`
- **Scope:** authoritative pre-1971 definitions, exact pages, terminology, topology, partitions,
  tags, refinement, endpoints, and citation strength
- **Status:** COMPLETE. Hille--Phillips is the closest bibliographic/contextual model, but is not
  cited in Section 1.11; other period sources use materially different Radon, Stieltjes, and
  Radon--Stieltjes constructions. Recommendation: LEVEL C.

### Lean topology bridge

- **Owner:** lead agent
- **Scope:** test only the implication justified independently of the ambiguous division semantics
- **Status:** COMPLETE in `Scratch/SakaiStrongRadonStieltjesBridge.lean`. Strong convergence of the
  same net implies the existing ultraweak candidate hypotheses, and hence the checked pointwise
  uniqueness result. This is not a source-equivalence theorem.

### Lead classification and production decision

- **Owner:** lead agent
- **Status:** LEVEL C — GENUINE AMBIGUITY. Sakai 1.11.3 remains NOT SOURCE-FORMALIZED. No
  representation predicate, arbitrary resolution, integral, PVM, or conditional uniqueness
  theorem is promoted. Active documentation is corrected; the clarified candidate stays scratch.

## Sakai 1.11.1 strong-topology transaction

- **Baseline:** `17682f5a1ff90bc01fa95ddcd969817fa3be038c`
- **Source reconstruction:** COMPLETE. Printed Lemma 1.11.1 assumes only `λₙ ≤ λ` and
  `λₙ → λ`; it does not assume monotonicity and concludes in `s(M,M_*)`.
- **Topology audit:** COMPLETE. Existing `Ultraweak.Strong` is the exact intrinsic topology;
  pinned/current Mathlib and original LeanOA have no competing implementation.
- **Production proof:** COMPLETE. General projection convergence lives in `StrongProjection`; exact
  filter-general and sequential spectral continuity live in `SpectralProjectionStrong`.
- **Section 1.12 cartography:** COMPLETE. The section contains only Theorem 1.12.1 and is now
  source-formalized, with no dependency on the RED integral/PVM boundary.

## Sakai 1.12 first production wave

- **WS-1, general $C^*$-API:** COMPLETE and accepted at checkpoint
  `6d24a2feb704cae6e4bedc00d6bc9f17c601f310`. The stable surface is
  `CFC.abs_mul_eq_zero_iff`, `CFC.mul_abs_eq_zero_iff`,
  `IsStarProjection.mul_star_mul_self`, `mul_star_mul_self_assoc`, and `mul_star_self`. It adds no
  competing absolute value or partial-isometry predicate.
- **WS-3, Sakai regularizer:** GREEN as scratch evidence at the accepted-input checkpoint and now
  transplanted privately into `Ultraweak.ElementPolarDecomposition` for its sole production
  consumer. The exact regularizer is contractive, satisfies `aReg n * h n = a`, and gives
  `aReg n * CFC.abs a -> a` in norm. It is not exposed as a parallel public API.
- **WS-2, absolute-value support bridge:** COMPLETE and independently reviewed GREEN from baseline
  `6d24a2f`. `WStarAlgebra.support_abs` and `support_abs_star` form the entire production surface;
  they reuse WS-1 and the existing support API, assume neither normality nor explicit predual data,
  and add no extra kernel corollary. The former is the canonical simp normal form; the latter is a
  named composite rewrite rather than a redundant simp lemma.
- **WS-4, existence:** COMPLETE. `WStarAlgebra.exists_element_polar_decomposition` gives
  `a = u * CFC.abs a` and the exact supports `star u * u = support |a|` and
  `u * star u = support |a*|`. The proof uses the source cutdown `q * b * p`, and
  `CFC.mul_star_eq_of_eq_mul_abs` records the source modulus-square consequence at the weaker
  abstract nonunital real-CFC generality of Mathlib's absolute value.
- **WS-5, packaging:** COMPLETE. `WStarAlgebra.element_polar_decomposition_unique` proves
  uniqueness algebraically from only the two factorizations and initial-support equations;
  `WStarAlgebra.existsUnique_element_polar_decomposition` packages the exact source predicate.
  The Verso node links the completed theorem and its direct dependencies. No `polarPart` or new
  partial-isometry predicate was introduced.

## Sakai 1.13 bounded closeout wave

The source audit finds that most of §1.13 is already supplied by Sak-AI's normality,
projection-lattice, strong-projection, and predual-uniqueness layers. Work should follow logical
dependency order, not repeat the section linearly.

- **1.13-A, source-normality bridge:** COMPLETE / GREEN in `Ultraweak.NormalOrder`. The literal
  bounded nonnegative `ScottContinuousOn` condition, full Scott continuity, projection normality,
  and specified-predual membership are equivalent. No predicate or chosen-predual parameter was
  added to the intrinsic statements.
- **1.13-B, orthogonal projection finite-sum net:** COMPLETE / GREEN in
  `Ultraweak.OrthogonalProjectionSum`. Arbitrary-index finite sums are projections, monotone, have
  LUB the existing projection `iSup`, and converge ultraweakly and strongly. There is no `tsum`
  overload or projection-family structure.
- **1.13-C, complete-additivity converse reconnaissance:** COMPLETE AS SCRATCH / DEFER PRODUCTION.
  Arbitrary-index `HasSum` is the exact scalar semantics; normality implies it, and the final
  converse reduction kernel-checks once a dominated orthogonal chain decomposition is supplied.
  The missing maximal decomposition and chain-LUB cutoff boundary are recorded precisely.
- **Sequential integration:** the source-normality and orthogonal-sum nodes are integrated into the
  existing Normality Verso chapter. The forward complete-additivity theorem remains scratch because
  publishing it alone would force a permanent predicate before the converse architecture settles.

Collision rule: A alone owns the normality bridge module, B alone owns the orthogonal-sum module,
and C is scratch-only. Shared umbrella imports, coordination documents, and Verso remain lead-owned.
