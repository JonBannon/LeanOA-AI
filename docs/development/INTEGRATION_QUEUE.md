# Integration queue

Only shared API, cross-stream, and design-contract questions belong here. Local proof problems stay
in their workstream.

## IQ-001 — spectral-resolution and integral interface

- **Status:** OPEN / RED
- **Affected streams:** architecture, Mathlib reconnaissance, spectral bands, tagged sums, Verso
- **Question:** What is the smallest canonical public object that faithfully packages Sakai 1.11.3
  without constructing a parallel measure theory beside Mathlib?
- **Constraints:** preserve `spectralProjectionIio` half-line semantics; do not claim a general
  set-indexed projection-valued measure prematurely; keep finite sums usable as rewrite tools.
- **Evidence obtained:** `reports/MATHLIB_SPECTRAL_AUDIT.md` shows that Mathlib's vector-measure
  integral is norm/variation based, neither pinned nor current Mathlib has a general PVM, and the
  current archived Riemann--Stieltjes API is norm-topological. D002's scratch comparison proves the
  generic and spectral-specific predicates equivalent for every real integrand, not just the
  identity. Atom counterexamples rule out unrestricted mesh-only semantics for discontinuous
  weights, and the canonical-specific predicate cannot state Sakai's arbitrary competing
  resolution `e'`.
- **Decision so far:** publish neither experimental predicate. The question remains OPEN / RED;
  this is a source-driven deferral, not acceptance of a canonical-family integral.
- **Next bounded action:** prove a partial-interval tagged norm estimate and aligned weighted-sum
  convergence for `(lambda_0 - lambda)^+` to the existing spectral positive part. Then extract the
  minimum explicit laws needed to state the corresponding theorem for an arbitrary competing
  resolution.

## IQ-002 — spectral helper generality

- **Status:** RESOLVED for the first wave
- **Affected streams:** spectral bands and tagged sums
- **Question:** Which interval-projection and tagged-sum facts are naturally generic for any
  monotone projection family, and which should remain specialized to `spectralProjectionIio`?
- **Default:** prove generic theorem-level facts where the assumptions stay recognizable; do not
  introduce a generic bundled spectral-family structure merely to share one proof.
- **Decision:** extract only the four-projection orthogonality fact to the nonunital Mathlib-staging
  layer. Keep spectral-band and tagged-sum declarations specialized to `spectralProjectionIio`,
  with named bridges showing that the existing lower and upper sums are endpoint-tag cases.

## IQ-003 — `TwoSidedIdeal` representation

- **Status:** HUMAN REVIEW; inherited from root `REVIEW_QUEUE.md`
- **Affected streams:** ideals, future upstreaming
- **Default:** preserve the existing native Mathlib object and its completed API. Do not implement
  the alternative representation in parallel.

## IQ-004 — orchestration versus theorem-status source

- **Status:** RESOLVED
- **Decision:** coordination files may track ownership, interface stability, and architectural
  dependencies, but Verso remains the only theorem-status/dependency registry.
