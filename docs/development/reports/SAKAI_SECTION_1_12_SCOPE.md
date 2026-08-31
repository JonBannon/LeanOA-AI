# Sakai Section 1.12 scope

## Source boundary

Source: Sakai, printed pp. 27–28 (local PDF pp. 39–40). Section 1.12 contains exactly one numbered
result, Theorem 1.12.1. Section 1.13 begins on printed p. 28. There is no separate numbered lemma,
corollary, or definition; the theorem introduces the name **polar decomposition**.

For a W-star algebra `M` and `a ∈ M`, Sakai asserts the existence and uniqueness of `u ∈ M`
such that

```text
a = u |a|,
|a| = (star a * a)^(1/2),
star u * u = s(|a|),
u * star u = s(|star a|).
```

Consequently `u` is a partial isometry. Sakai's earlier convention defines this by requiring
`star u * u` to be a projection; Corollary 1.1.9 supplies the final projection
`u * star u`.

## Source proof structure

Sakai indexes from `n=1`. For a Lean sequence indexed by all naturals, use
`ε n = ((n + 1 : ℝ)⁻¹)` and define

```text
hₙ = (star a * a + εₙ1)^(1/2),
aₙ = a (star a * a + εₙ1)^(-1/2).
```

He writes `star aₙ * aₙ = (star a * a)/(star a * a + n⁻¹1)`, proves `‖aₙ‖ ≤ 1`,
`aₙhₙ=a`, and proves `hₙ → |a|` in norm. In Lean, the quotient must be replaced by the exact conjugated
noncommutative product recorded in the WS-3 contract.
Ultraweak compactness of the closed unit ball gives a cluster point `b` with `a=b|a|`. With
`p=s(|a|)` and `q=s(|star a|)`, the proof cuts `b` down to the desired partial isometry and identifies
its initial and final projections. Uniqueness follows from the support of `|a|` (Sakai phrases the
last step through a closed right ideal).

The formal proof may simplify the source's cutdown `u=qbp` to `u=bp` once the support equations
justify it. This is a proof-route change, not a statement change. The source also obtains the
useful identity `a * star a = u * (star a * a) * star u`.

The compactness topology is `σ(M,M_*)`, not the strong topology from §1.11. A formal proof must use
filters or `MapClusterPt`; arbitrary ultraweak topologies are not known to be first countable, so a
subsequence argument would be unjustified.

## Theorem inventory and current status

| Item | Present library support | Status | Placement / note |
| --- | --- | --- | --- |
| `|a| = sqrt (star a * a)` | Mathlib `CFC.abs`, sqrt/rpow/order APIs | MATHLIB ALREADY HAS IT | Reuse; no local absolute value |
| supports `s(|a|)`, `s(|star a|)` | Sak-AI `WStarAlgebra.support` | ALREADY FORMALIZED | Bundle the positive self-adjoint elements |
| partial-isometry condition | expressible as `IsStarProjection (star u * u)` | ALREADY EXPRESSIBLE | Do not invent a predicate merely for the theorem |
| `star u * u` projection ⇒ `u * star u` projection and fixing identities | elementary C-star algebra | ALMOST FREE / POSSIBLE MATHLIB UPSTREAM | General nonunital C-star API |
| `CFC.abs a * x = 0 ↔ a*x=0`; `x*CFC.abs a=0 ↔ x*star a=0` | follows from `abs_mul_abs` and zero-square API | ALMOST FREE / POSSIBLE MATHLIB UPSTREAM | Exact orientations matter for nonnormal `a` |
| `support(|a|)=rightSupport a` and star analogue | support plus preceding annihilation bridge | ALMOST FREE | Narrow downstream `AbsSupport` module |
| shifted sqrt/inverse `hₙ` | Mathlib CFC primitives | MATHLIB ALREADY HAS PRIMITIVES | Construction remains local |
| regularizer identities and `‖aₙ‖≤1` | CFC order/conjugation/rpow | LOCAL THEOREM WORK | No new calculus |
| `hₙ→|a|` in norm | CFC continuity/order estimates | LOCAL THEOREM WORK | Sequence-local |
| compact cluster point `b` | `Ultraweak.isCompact_closedBall`, `MapClusterPt` | ALMOST FREE engineering | Must avoid sequential compactness |
| passage `b|a|=a` | norm→ultraweak plus fixed multiplication continuity | LOCAL THEOREM WORK | Separate continuity only |
| defect argument producing `u` | support zero-kernel/order API | LOCAL THEOREM WORK | Main mathematical step |
| `u * star u = s(|star a|)` | partial-isometry facts plus support bridge | ALMOST FREE after existence | No §1.11 dependency |
| `a * star a = u * (star a * a) * star u` | algebraic rewrite after factorization/support | ALMOST FREE | Record source consequence |
| uniqueness | support zero-kernel API | ALMOST FREE after equations | Prefer direct support proof |
| exact `∃! u` package | assembly of preceding items | LOCAL THEOREM WORK | Theorem 1.12.1 |

Overall classification: **YELLOW / LOCAL THEOREM WORK, UNBLOCKED**. No RED spectral-integral or PVM
area is involved. The only substantive work is the regularized contraction, compact cluster point,
and support-defect upgrade.

## Mathlib and LeanOA overlap

- Pinned Mathlib (`476ab284...`) has the canonical CFC absolute value, sqrt, inverse/rpow, order,
  and projection primitives, but no element polar-decomposition theorem or `IsPartialIsometry`.
- Current Mathlib audited at `be865aa50cc0364be66c3941a6dc0c845a2c2ceb` still has no element
  polar decomposition or partial-isometry predicate; `CFC.abs` remains canonical.
- Original LeanOA has no element polar decomposition or support bridge.
- `LeanOA/Ultraweak/PolarDecomposition.lean` concerns polar decomposition of ultraweakly
  continuous functionals. It is not Theorem 1.12.1. Use a distinct future module such as
  `LeanOA/Ultraweak/ElementPolarDecomposition.lean`.

## Dependency DAG

```text
Mathlib CFC.abs → exact abs-annihilation lemmas → W-star support bridges

IsStarProjection + C-star cancellation → partial-isometry fixing/final-projection facts

Mathlib CFC sqrt/rpow/order → local regularizer identities and limits

support bridges + partial-isometry facts + regularizer
    ↓
Ultraweak compact closed ball + MapClusterPt
    ↓
cluster point b with b|a|=a
    ↓
support-defect cutdown u and both support equations
    ↓
source identity + support-zero-kernel uniqueness
    ↓
Sakai Theorem 1.12.1
```

There is no dependency edge from §1.11, its PVM boundary, or its abstract integral.

## Proposed next wave

### WS-1 — general C-star API (GREEN, low collision)

- Scope: from `IsStarProjection (star u * u)`, prove the final projection and fixing identities;
  prove exactly `CFC.abs a*x=0 ↔ a*x=0` and
  `x*CFC.abs a=0 ↔ x*star a=0`.
- Dependencies: pinned Mathlib CFC and projection API only.
- API stability/reuse: high; useful beyond Sakai and plausible upstream material.
- CFC interaction: reuse `CFC.abs`; do not wrap it.
- PVM/topology interaction: none.
- Deliverable: general theorem signatures, proof, focused tests, overlap report.
- Placement: keep CFC absolute-value imports in a narrow mirrored `CStarAlgebra/Abs` module rather
  than broadening the foundational `Basic` import surface.

### WS-2 — W-star support bridge (GREEN after WS-1, low collision)

- Scope: identify support of `|a|` with `rightSupport a` and support of `|star a|` with
  `leftSupport a`.
- Dependencies: `Support` plus WS-1 annihilation lemmas.
- API stability/reuse: high; this is the translation bridge used by every later polar-decomposition
  equation.
- CFC interaction: canonical `CFC.abs` only.
- PVM interaction: none; topology only through existing support construction.
- Placement: a narrow `Ultraweak/AbsSupport` bridge downstream from `Support`; do not make
  foundational support depend on the CFC absolute-value stack.

### WS-3 — regularizer layer (YELLOW, medium collision)

- Scope: with `ε n = ((n + 1 : ℝ)⁻¹)`, define proof-local
  `c n = star a * a + ε n • 1`, `h n = CFC.sqrt (c n)`, and
  `aReg n=a*(c n)^(-(1/2 : ℝ))`; prove the exact conjugated product identity, contraction,
  `aReg n*h n=a`, norm convergence `h n→|a|`, and the norm-convergent handoff
  `aReg n*|a|→a`.
- Dependencies: Mathlib CFC only, plus stable algebraic helpers.
- API stability/reuse: local; keep scaffolding private unless a theorem has a recognizable general
  signature.
- Risk: CFC elaboration and strict positivity, not architecture.
- Handoff: production never imports `Scratch`. After review, transplant the checked local proof
  into WS-4 as private implementation or promote only independently reusable lemmas to a narrow
  production module.

### WS-4 — W-star existence (YELLOW, isolated owner)

- Scope: filter-based compact cluster extraction of `b` with `‖b‖ ≤ 1`, limit passage
  `b|a|=a`, support-defect cutdown, initial/final projection equations, and the source consequence
  `a * star a = u * (star a * a) * star u`.
- Dependencies: WS-1 through WS-3, `Ultraweak.isCompact_closedBall`, fixed multiplication, support.
- API stability/reuse: theorem-level; avoid a new bundled polar-decomposition object.
- Topology risk: medium. Do not use subsequences or joint ultraweak multiplication.

### WS-5 — exact packaging and review (GREEN after WS-4)

- Scope: direct support-based uniqueness, exact `∃!` source theorem, Verso node, axiom and build
  audit.
- Dependencies: all prior workstreams.
- API decision: add a noncomputable `polarPart` only if an immediate downstream consumer justifies
  it; do not block the source theorem on that choice.
- Collision risk: low once the theorem signature is frozen.

## Recommended implementation order

Run WS-1 and scratch WS-3 in parallel. WS-2 waits only for WS-1's annihilation signatures, not its
partial-isometry branch. WS-4 waits for all three accepted inputs; WS-5 is strictly sequential after
WS-4 because both own the element-polar-decomposition module. This order reduces Theorem 1.12.1 to
one isolated compactness construction while preserving Mathlib portability and avoiding the RED
§1.11 architecture.
