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
| Complete-additivity equivalence | source normality + orthogonal sums + projection-chain decomposition | GREEN | high for Sakai 1.13 | complete | reviewed | theorem-only API |
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
- **1.13-C, complete-additivity reconnaissance:** COMPLETE. It established arbitrary-index
  `HasSum` as the exact scalar semantics and isolated the maximal-chain decomposition as the sole
  hard blocker.
- **1.13-D, projection-chain decomposition:** COMPLETE / GREEN in
  `Ultraweak.ProjectionChain`. A maximal subtype-indexed orthogonal family has every finite sum
  dominated by a chain member and has supremum equal to the chain LUB. Maximality scaffolding is
  private.
- **1.13-E, chain-LUB normality bridge:** COMPLETE / GREEN across `ProjectionLattice`,
  `NormalCutoff`, `NormalSelection`, `NormalCharacterization`, and `NormalOrder`. The reusable
  theorem states that preservation of projection-chain LUBs already recovers canonical normality;
  no chain-normality predicate was introduced.
- **1.13-F, complete-additivity characterization:** COMPLETE / GREEN in
  `Ultraweak.CompleteAdditivity`. Normality gives `HasSum` for arbitrary index universes; the
  converse uses the chain decomposition and yields `IsNormalOnProjections`. The production API is
  theorem-only and Section 1.13 is complete.
- **Sequential integration:** all Section 1.13 mathematics is presented in the existing Normality
  Verso chapter. The public frontier has since advanced through the Section 1.14 support and
  orthogonal-Jordan waves to Sakai Theorem 1.14.4.

Collision rule: A alone owns the normality bridge module, B alone owns the orthogonal-sum module,
and C is scratch-only. Shared umbrella imports, coordination documents, and Verso remain lead-owned.

## Sakai 1.14.2 functional-support wave

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

This wave starts from `05c69abaa5a8608700a75d25b4da05d04d63a588` and uses Sakai's null-left-ideal
route. It does not construct functional support as a supremum of zero projections and does not add
a second support object.

- **WS-14A, source and architecture:** fixed the exact orientation
  `Lφ = M p₀`, `s(φ) = 1 - p₀`, and `x ∈ Lφ ↔ x * s(φ) = 0`; confirmed that functional support
  belongs in `PositiveLinearMap`, separate from element support.
- **WS-14B, null ideal and topology:** placed `PositiveLinearMap.nullIdeal` at general unital
  $C^*$-algebra level, with the paired Cauchy--Schwarz zero-coefficient helpers. Under an explicit
  `IsNormalOnProjections` proof, the topology route is exactly strong closedness followed by the
  existing convex strong-to-ultraweak closure theorem. The chosen predual appears only in those
  topology-specific proofs, and the existing closed-left-ideal classifier supplies the generator.
- **WS-14C, support consequences:** uses the intrinsic annihilator and greatest-zero interfaces for
  cutdown and faithfulness results. It reuses `IsStarProjection.Corner`; no `Faithful` predicate,
  normal-positive-functional bundle, or new corner structure is introduced.
- **Integration decision:** retain the general ring/idempotent bridge
  `Ideal.mem_span_singleton_one_sub_iff_mul_eq_zero`; expose functional support only with explicit
  normality and keep the canonical $W^*$-predual internal.
- **Downstream wave:** COMPLETE. Sakai Definition 1.14.1 and Theorem 1.14.3 consume this support API
  through the orthogonal-Jordan wave recorded below.

Collision rule: downstream Section 1.14 work may consume functional support but must not redefine
it, add a parallel faithfulness notion, or expose a predual parameter in intrinsic statements.

## Sakai 1.14.1 and 1.14.3 orthogonal-Jordan wave

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

This wave formalizes the source norm relation before using the completed functional-support API to
obtain the unique orthogonal decomposition of a self-adjoint normal functional.

- **WS-14D, source and factorization:** COMPLETE. Reconstructed Definition 1.14.1 and Theorem
  1.14.3 directly, audited Mathlib/original LeanOA/current Sak-AI, and selected
  `Ultraweak.exists_positive_comp_mulLeft_of_isSelfAdjoint` as the existing analytic engine. The
  source and overlap record is `reports/SAKAI_1_14_1_1_14_3_SOURCE.md`.
- **WS-14E, norm orthogonality and support:** COMPLETE / GREEN.
  `PositiveLinearMap.IsOrthogonal` is the exact norm relation at general nonunital $C^*$-algebra
  level. `PositiveLinearMap.isOrthogonal_of_support_mul_eq_zero` is the direct $W^*$ consequence;
  the converse and `PositiveLinearMap.isOrthogonal_iff_support_mul_eq_zero` are derived only after
  uniqueness.
- **WS-14F, construction and normality:** COMPLETE / GREEN. The existing positive factor is split
  by private complementary projections and `IsStarProjection.Corner.ultraweakCutdownP`. Pullback
  to ordinary positive maps and explicit `IsNormalOnProjections` proofs reuse the established
  predual bridge.
- **WS-14H, uniqueness:** COMPLETE / GREEN. Carrier values, component norm comparison,
  `PositiveLinearMap.support_le_iff_apply_eq_apply_one`, and support cutdowns prove uniqueness
  without assuming the later support-characterization converse.
- **Lead integration and independent review:** COMPLETE / GREEN.
  `Ultraweak.existsUnique_orthogonal_decomposition_of_isSelfAdjoint` is the exact source-facing
  `∃!` theorem. No public choice-based positive/negative parts, decomposition structure, normal-
  functional wrapper, or competing polar decomposition was introduced. The implementation report
  is `reports/SAKAI_1_14_1_1_14_3_JORDAN_DECOMPOSITION.md`.
- **Downstream outcome:** the separate Sakai 1.14.4 wave completed the general normal-functional
  polar decomposition after auditing its right-action, norm, support, uniqueness, and final-
  projection clauses. It is recorded below.

Collision rule: Theorem 1.14.4 work may reuse the self-adjoint-unitary factorization and Jordan
decomposition, but must not relabel either as the general functional polar decomposition or create
a second functional-support object.

## Sakai 1.14.4 general functional-polar-decomposition wave

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

This wave completes Section 1.14 by formalizing the polar decomposition of an arbitrary normal
functional with the exact source orientation and normalizations.

- **WS-14I, source and overlap audit:** COMPLETE / GREEN. Direct inspection of Sakai fixes
  `R_v g (x) = g (x * v)` and hence the factorization `g x = φ (x * v)`. The source requires
  normal positivity of `φ`, equality of norms, `star v * v = s(φ)`, uniqueness of the pair, and
  $v v^* = s(|g^*|)$. Pinned and audited current Mathlib, original LeanOA, and baseline Sak-AI
  contain no theorem with those clauses. The source and overlap record is
  `reports/SAKAI_1_14_4_SOURCE.md`.
- **WS-14J, shared API:** COMPLETE / GREEN. `PositiveLinearMap.conjugate` and
  `PositiveLinearMap.conjugate_apply` live at nonunital $C^*$-algebra generality.
  `PositiveLinearMap.IsNormalOnProjections.conjugate` is the ultraweak normality bridge, while
  `PositiveLinearMap.support_conjugate_eq_mul_star` transports initial support to final support.
  The normal pullback helper
  `PositiveContinuousLinearMap.comp_toUltraweakPosCLM_isNormalOnProjections` was promoted from the
  prior Jordan proof and that consumer now reuses it.
- **WS-14K, existence and uniqueness:** COMPLETE / GREEN. The private analytic engine extends the
  exposed-face argument directly from the self-adjoint unit ball to the full unit ball; it does
  not route the theorem through the Jordan decomposition or identify the earlier
  `Ultraweak.PolarDecomposition` with this result.
  `Ultraweak.existsUnique_functional_polar_decomposition_basic` packages exact right
  factorization, norm equality, initial support, and pair uniqueness.
- **WS-14L, source packaging:** COMPLETE / GREEN. `Ultraweak.functionalAbs` deliberately names the
  unique positive factor required by Sakai. Its normality, existence specification, norm, and
  uniqueness interfaces are
  `functionalAbs_isNormalOnProjections`, `functionalAbs_spec`, `norm_functionalAbs`, and
  `eq_functionalAbs_of_polar_decomposition`. The final-support bridge is
  `functional_polar_decomposition_final_projection`; the exact source endpoint is
  `Ultraweak.existsUnique_functional_polar_decomposition`. The full implementation and API record
  is `reports/SAKAI_1_14_4_FUNCTIONAL_POLAR_DECOMPOSITION.md`.
- **Architecture outcome:** no `IsPartialIsometry` predicate is introduced. The equation
  `star v * v = support φ` certifies the established partial-isometry semantics. No normal-
  functional wrapper, second support, chosen polar element, or decomposition structure is added.
  The older `Ultraweak.PolarDecomposition` remains the narrower self-adjoint/left-action engine.
- **Next bounded wave:** audit the source topology and existing Mathlib/Sak-AI APIs for Section
  1.15, then formalize Proposition 1.15.1 if the exact statement and assumptions are certifiable.

Collision rule: Section 1.15 work may consume `functionalAbs` and the exact polar theorem, but must
not create another functional absolute value, normal-functional wrapper, or topology merely to
match source notation.

## Sakai 1.15 first topology transaction

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

This transaction starts from `ce2018a780034ce3f93134a000919dcfe9f95c4f`. It certifies the source
statement and maps the existing topology APIs, but it does not claim Proposition 1.15.1.

- **WS-15A, direct source audit:** COMPLETE. Sakai's five global closedness conditions for a
  self-adjoint subalgebra of $B(H)$ are WOT, $\sigma$-WOT, SOT, the strongest/ultrastrong operator
  topology, and `σ(B(H),B(H)_*)`. The uniform topology is surrounding context rather than a sixth
  condition, and bounded-sphere topology equivalences belong to Proposition 1.15.2. The audit
  deliberately distinguishes $\sigma$-WOT from the predual weak topology and strongest operator
  topology from both intrinsic `s` and Mackey topology.
- **WS-15B, pinned/current/original topology audit and intrinsic bridge:** COMPLETE / GREEN for the
  narrow intrinsic bridge only. Pinned Mathlib `476ab284693e554a6b48c5f5210cb4fb5ae51252` supplies WOT as
  `ContinuousLinearMapWOT` and pointwise/SOT as `PointwiseConvergenceCLM`; current Mathlib still
  lacks the concrete $B(H)$ predual and double-commutant/closedness bridge. Original LeanOA
  `cb811c1006ae78a0ff1d175253200e1859843370` adds no concrete topology infrastructure.
  `Strong.isClosed_iff_image_toUltraweakEquiv` is the only new intrinsic theorem: it derives
  closedness equivalence for real-convex sets directly from the existing closure-image theorem.
- **WS-15C, general concrete comparison bridge:** COMPLETE / GREEN. The mirrored Mathlib module
  adds `PointwiseConvergenceCLM.toWOT` and
  `PointwiseConvergenceCLM.isClosed_pointwise_of_isClosed_wot`. Both reuse Mathlib's existing
  topology-bearing synonyms and are independent of Hilbert-space, algebra, predual, and Sakai
  assumptions. They establish only SOT-to-WOT continuity and WOT-closed-to-SOT-closedness.
- **Architecture outcome:** no WOT, SOT, $\sigma$-WOT, ultrastrong, ultraweak, strong, or Mackey
  topology type is introduced. The concrete and intrinsic topology families remain connected only
  by proved named bridges. A concrete $B(H)$ predual/coefficient realization, the $\sigma$-WOT and
  ultrastrong identifications, and a relative form of Kaplansky density for the WOT closure remain
  OPEN / RED under IQ-010.
- **Source and Verso status:** Proposition 1.15.1 is **not source-formalized**. There is no Verso
  theorem node for it. The public frontier remains Proposition 1.15.1 rather than advancing to
  Proposition 1.15.2.

Collision rule: further Section 1.15 work must reuse Mathlib's WOT and pointwise/SOT types and
Sak-AI's intrinsic `σ`/`s`/Mackey APIs. It must not equate concrete and intrinsic topologies by
reducibility or introduce a local substitute for the missing $B(H)$ predual.

## Sakai 1.15 second vector-functional transaction

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

This transaction starts from `2932d54c12e0f559f980b18173d290cc6695af6e`. It constructs Sakai's
finite WOT test-functional space without claiming its norm completion or Proposition 1.15.1.

- **WS-15D, vector-functional API:** COMPLETE / GREEN. The generic mirrored-Mathlib module defines
  `ContinuousLinearMap.vectorFunctional` over `RCLike`, with a seminormed domain and Hilbert
  codomain, and proves adjoint/star, composition, fixed multiplication, raw/span separation,
  intrinsic-dual-star stability, and span-level multiplier invariance. No `Nontrivial` assumption
  or competing dual-star operation is introduced.
- **WS-15E, WOT/weak-pairing identification:** COMPLETE / GREEN. Restricted evaluation gives
  `vectorFunctionalPairing`; `vectorFunctionalWeakEquiv` proves both continuous identity
  directions between its `WeakBilin` topology and Mathlib WOT. On the WOT carrier,
  `vectorFunctionalPairing_isWeak` is the exact topology certificate and
  `vectorFunctionalSpanEquivDual` identifies the span with all WOT-continuous linear
  functionals. This is the honest integration with Sak-AI's weak-pairing core.
- **WS-15F, completion/predual reconnaissance:** COMPLETE / REPORT ONLY. No production predual or
  σ-WOT object is introduced. The recommended route is the norm closure/completion of the finite
  coefficient span followed by the isometric evaluation theorem; trace-class identification is a
  later Sakai theorem. Existing relative Kaplansky machinery still assumes density in the whole
  ambient algebra.
- **Architecture outcome:** `Ultraweak.WeakTestSpace V` cannot be instantiated before a complete
  specified predual `P` and an embedding `V ≤ P` exist. The new `WeakBilin` equivalence and
  `LinearMap.IsWeak` instance reuse its semantic core without pretending the algebraic span is
  already complete. No new WOT or predual synonym is introduced.
- **Source and Verso status:** the finite coefficient/WOT layer of §1.15 is complete and may appear
  as infrastructure. Sakai Proposition 1.15.1 remains **not source-formalized**, with no theorem
  node claiming otherwise; the public frontier does not advance to Proposition 1.15.2.

Collision rule: the next transaction must extend `vectorFunctionalSpan` through a named norm
completion/embedding and prove its predual property. It must not identify the algebraic span with
`B(H)_*`, define σ-WOT by the intrinsic topology, or import trace-class conclusions from Sakai
Theorem 1.15.3 before proving them.

## Sakai 1.15 third norm-closed-predual transaction

> **Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

This transaction starts from `21332383a82bff3f2d4a217d8d86b07c92591e18`. It constructs the
canonical norm-closed coefficient predual without importing trace-class theory or claiming Sakai
Proposition 1.15.1.

- **WS-15G, coefficient norm and closed carrier:** COMPLETE / GREEN. The generic operator module
  proves the sharp formula `‖vectorFunctional ξ η‖ = ‖ξ‖ * ‖η‖`, defines
  `vectorFunctionalClosure` as the operator-dual norm closure of the finite coefficient span, and
  packages the span inclusion as a dense linear isometry. The coefficient norm theorem keeps the
  seminormed operator domain and needs no artificial completeness or nontriviality assumption.
- **WS-15H, generalized recovery:** COMPLETE / GREEN. Canonical evaluation from operators into the
  strong dual of the closed coefficient carrier is an isometry. A functional on the carrier is
  recovered as an operator by a bounded sesquilinear form and the Hilbert-space Riesz equivalence;
  equality is proved first on coefficient vectors and then on the closure by density. Domain-side
  Hilbert and completeness assumptions are absent because the mathematics does not require them.
- **WS-15I, project predual assembly:** COMPLETE / GREEN. For a normed operator domain and complete
  Hilbert codomain, `LeanOA.Ultraweak.BoundedOperator` installs the resulting equivalence as the
  existing root `Predual` structure through a short carrier canonically isometric to the closure.
  No competing predual class, operator topology, or
  trace-class synonym is introduced.
- **Source and Verso status:** this is certified infrastructure and has a dedicated Verso theorem
  node. At that checkpoint Sakai Proposition 1.15.1 remained **not source-formalized**:
  coefficient-series σ-WOT, concrete ultrastrong comparison, and the relative Kaplansky closure
  argument were open.

Collision rule recorded at that checkpoint: subsequent §1.15 work must reuse
`vectorFunctionalClosure` and its proved predual equivalence. The next transaction was required
to establish square-summable coefficient-series membership and only the one-sided topology
comparison, without trace class or definitional identification.

### Section 1.15.1 fourth coefficient-series transaction

This transaction starts from `26d5c01` and closes the source-safe coefficient-series edge without
claiming the later representation theorem.

- **WS-15J, generic series API:** COMPLETE / GREEN. Two separately square-summable families over an
  arbitrary index type give a norm-summable coefficient family in the completed predual, with the
  sharp Hölder/Cauchy--Schwarz norm bound and the exact evaluation formula. No codomain
  completeness is needed.
- **WS-15K, invariant finite core:** COMPLETE / GREEN. The canonical finite coefficient span inside
  the short predual carrier is norm dense and satisfies the existing
  `SakaiInvariantTestSpace` star and left/right multiplier conditions.
- **WS-15L, source test topology:** COMPLETE / GREEN. The source-facing span uses exactly
  $\mathbb N$-indexed, separately square-summable series. It contains the finite core and receives
  the canonical continuous identity from the full concrete-predual topology through the general
  `WeakBilin.restrictRightL` API. Series-test closed therefore implies ultraweak closed.
- **Source and Verso status:** this is certified infrastructure with a dedicated node. Sakai
  Proposition 1.15.1 remains **not source-formalized**. The converse series representation is
  deferred to Corollaries 1.15.5--1.15.6; concrete ultrastrong comparison and ambient-relative
  Kaplansky density remain open.

Collision rule: do not add a `SigmaWOT` synonym or reverse the topology map without the later
representation theorem. The next bounded transaction is ambient-relative Kaplansky density in the
test-weak closure.

### Section 1.15.1 fifth ambient-relative Kaplansky transaction

This transaction starts from `db9e2a5` and closes the relative-density edge without claiming the
remaining concrete ultrastrong comparison.

- **WS-15M, generic relative density:** COMPLETE / GREEN. `testWeakClosure` is the ordinary closure
  in the selected weak realization, transported back to the original algebra carrier. Given source
  and target nonunital star subalgebras with the target carrier equal to this closure, the source
  unit ball has the target unit ball as both its ultraweak and full-predual Mackey closure. The
  closed-source Krein--Milman proof and nonclosed norm-closure reduction are kernel-checked.
- **WS-15N, concrete WOT target:** COMPLETE / GREEN. Mathlib's `ContinuousLinearMapWOT` is given its
  canonical star-algebra equivalence with bounded operators; WOT closure is packaged as an existing
  nonunital star subalgebra; and the finite coefficient predual span's test-weak closure is proved
  equal to that WOT closure. The generic relative theorem then yields
  `Ultraweak.kaplansky_density_wotClosure`.
- **Generality review:** COMPLETE / GREEN. The geometric subtype step is proved once for an arbitrary
  real submodule of a seminormed real vector space; the C-star-algebra theorem is only a thin
  specialization. The Kaplansky transform is fixed under the reusable cubic identity
  `a * star a * a = a`, with the old extreme-point endpoint now a corollary.
- **Source and Verso status:** this is certified infrastructure with a dedicated relative-density
  node. Sakai Proposition 1.15.1 remains **not source-formalized**. The concrete
  square-summable-vector ultrastrong comparison is the next source-critical transaction.

Collision rule: reuse Mathlib WOT and the established concrete predual; do not introduce a generic
test-weak closure algebra merely to repackage the already available concrete WOT target. The next
bounded transaction is the concrete ultrastrong/intrinsic-strong interface.

### Section 1.15.1 sixth concrete-ultrastrong transaction

This transaction starts from `b0655c9` and closes exactly the strongest-operator comparison needed
by Proposition 1.15.1, without importing the later topology-equality theorem.

- **WS-15O, generic square-summable convergence:** COMPLETE / GREEN.
  `SquareSummableConvergenceCLM` is the topology-bearing synonym generated by
  $`T\mapsto\lVert(T\xi_n)_n\rVert_{\ell^2}` for $`\xi\in\ell^2(\mathbb N,E)`.
  Coordinatewise application is proved at arbitrary-index normed-space generality and reuses the
  existing local `lp.mapCLM` API. Single-support families give the continuous identity to
  Mathlib's `PointwiseConvergenceCLM`, hence concrete ultrastrong convergence implies SOT.
- **WS-15P, intrinsic-strong comparison on $`B(H)`:** COMPLETE / GREEN. Every defining concrete
  seminorm is the GNS seminorm of the positive normal diagonal coefficient series
  $`T\mapsto\sum_n\langle\xi_n,T\xi_n\rangle`. Therefore the canonical identity from
  $`s(B(H),P_H)` to the concrete square-summable carrier is continuous, and
  concrete-ultrastrong closedness implies intrinsic-strong closedness.
- **Source boundary:** COMPLETE / GREEN. Only the chain
  $`s(B(H),P_H)\to\mathrm{USOT}\to\mathrm{SOT}` is asserted. Its reverse, a homeomorphism, and
  equality of the topologies require the later representation of all positive normal functionals
  and remain deferred to Sakai Corollary 1.15.6.
- **Source and Verso status:** this is certified infrastructure with a dedicated comparison node.
  Proposition 1.15.1 remains **not source-formalized** until the five global closedness predicates
  are assembled.

Collision rule: do not replace the square-summable seminorms by sup-on-set uniform convergence,
and do not prove the converse intrinsic/concrete comparison before its later source dependency.
The next bounded transaction is the final source-faithful closedness equivalence.

### Section 1.15.1 seventh closedness-assembly transaction

This transaction starts from `79196cc` and completes Sakai Proposition 1.15.1 without importing
the later topology-equality theorems.

- **WS-15Q, nested test-space and concrete $`\sigma`-WOT bridge:** COMPLETE / GREEN.
  `Ultraweak.testWeakRestrictionL` reuses `WeakBilin.restrictRightL` for arbitrary predual test
  submodules $`V\leq W`, and `Ultraweak.isClosed_testWeak_of_le` gives the corresponding
  closed-set implication for an arbitrary ambient subset. The source coefficient-series topology
  specializes this map through the finite coefficient core to Mathlib WOT.
- **WS-15R, intrinsic closure and relative-Kaplansky endpoint:** COMPLETE / GREEN.
  `Ultraweak.Strong.isClosed_ofStrong_preimage_iff_ofUltraweak_preimage` transports closedness for
  any real-convex ambient subset. For a concrete bounded-operator star subalgebra, ultraweak
  closedness and the relative unit-ball theorem put the unit ball of its WOT closure back in the
  source; normalization and rescaling then prove equality with the full WOT closure.
- **WS-15S, source theorem assembly:** COMPLETE / GREEN.
  `NonUnitalStarSubalgebra.operatorTopologyClosedness_tfae` states the five global predicates in
  Sakai's order: WOT, coefficient-series $`\sigma`-WOT, SOT, concrete ultrastrong, and
  concrete-predual ultraweak closedness. Four named iff theorems expose the pairwise WOT
  equivalences for retrieval.
- **Generality review:** COMPLETE / GREEN. The reusable test-space theorem is independent of
  operator algebras, and the strong/ultraweak theorem assumes only real convexity. Hilbert-space,
  star-subalgebra, and Kaplansky assumptions appear only in the source-specific reverse endpoint.
- **Source and Verso status:** Sakai Proposition 1.15.1 is **SOURCE-FORMALIZED** and has a dedicated
  source proposition node. No converse coefficient-series representation, topology equality, or
  trace-class identification is claimed.

Collision rule: retain the five concrete/intrinsic predicates as distinct objects until Sakai's
later representation results justify topology equality. The next bounded transaction is a direct
source and API audit of Proposition 1.15.2, especially its induced-predual and bounded-sphere
interfaces.

### Section 1.15.2 source and API audit transaction

This audit starts from `76b84e9` and fixes the exact target before topology implementation.

- **WS-15T, direct source semantics:** COMPLETE. Proposition 1.15.2 compares WOT,
  coefficient-series $`\sigma`-WOT, and $`\sigma(N,N_*)`, then SOT, concrete ultrastrong, and
  $`s(N,N_*)`, on norm-closed balls of a WOT-closed possibly nonunital self-adjoint subalgebra.
  Sakai's “bounded spheres” means closed balls, and the net-based topology theorem must not be
  weakened to sequences.
- **WS-15U, induced-predual audit:** COMPLETE. `Ultraweak.closedSubmodulePredual` already realizes
  $`N_*` as the ambient predual modulo the preannihilator. The missing reusable seam is the
  quotient evaluation formula and the continuous equivalence with the ambient ultraweak subtype;
  it belongs at general ultraweakly-closed-submodule and `RCLike` generality.
- **WS-15V, induced-predual bridge:** COMPLETE. Quotient-representative evaluation and the
  continuous linear equivalence with the ambient ultraweak subtype are proved at general
  ultraweakly-closed-submodule and `RCLike` generality, with no competing predual or topology.
- **WS-15W, weak-family production half:** COMPLETE. Compact-to-Hausdorff gives canonical
  homeomorphisms among intrinsic $`\sigma(N,N_*)`, coefficient-series $`\sigma`-WOT, and WOT on
  every zero-centered norm-closed ball, together with arbitrary-filter convergence equivalences.
- **WS-15X, strong-family production half:** NEXT. Prove the reusable filter-general
  positive-square convergence bridge, then compare intrinsic strong, concrete ultrastrong, and
  SOT on the same balls. Trace-class representation and global topology equality remain later
  source results.
- **Source status:** Proposition 1.15.2(1) is **SOURCE-FORMALIZED**; Proposition 1.15.2(2) is
  **NOT SOURCE-FORMALIZED**; Proposition 1.15.2 is **NOT SOURCE-FORMALIZED**.

Collision rule: do not introduce another predual class or topology synonym, do not use the
choice-based W-star predual as a substitute for the explicit quotient restriction map, and do not
advertise bounded-ball equivalence as global equality.
