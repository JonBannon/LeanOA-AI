# Integration queue

Only shared API, cross-stream, and design-contract questions belong here. Local proof problems stay
in their workstream.

## IQ-001 — spectral-resolution and integral interface

- **Status:** DEFERRED / RED — LEVEL C source ambiguity
- **Affected streams:** architecture, Mathlib reconnaissance, spectral bands, tagged sums, Verso
- **Question:** What future coherent PVM/integral construction, or new primary evidence, can fix a
  public representation object without assigning semantics to Sakai's undefined phrase by fiat?
- **Constraints:** preserve `spectralProjectionIio` half-line semantics; do not claim a general
  set-indexed projection-valued measure prematurely; keep finite sums usable as rewrite tools.
- **Evidence obtained:** `reports/MATHLIB_SPECTRAL_AUDIT.md` shows that Mathlib's vector-measure
  integral is norm/variation based, neither pinned nor current Mathlib has a general PVM, and the
  current archived Riemann--Stieltjes API is norm-topological. D002's scratch comparison proves the
  generic and spectral-specific predicates equivalent for every real integrand, not just the
  identity. Atom counterexamples rule out unrestricted mesh-only semantics for discontinuous
  weights, and the canonical-specific predicate cannot state Sakai's arbitrary competing
  resolution `e'`. The truncated-affine transaction now adds a sharp canonical theorem with an
  interior cutoff and the exact existing CFC target. An arbitrary monotone projection family also
  satisfies the corresponding finite positive-part identity under exact endpoint normalization,
  but passing to the target through `Filter.Tendsto.cfc` requires norm moment convergence, which is
  stronger than the topology-forgotten ultraweak representation used by the checked conditional
  argument. Support recovery additionally needs lower
  bounds, an upper-support identity, and continuity from below; support is not continuous under
  norm limits. The fixed-projection transaction now kernel-checks the exact finite cutoff algebra,
  the total-moment-only positive/negative decomposition, both support inequalities, the `Iio` LUB
  recovery, and pointwise/family uniqueness under explicit inserted-cut approximation data. The
  refinement transaction now proves the generic prescribed-cut restriction, a nontrivial concrete
  finite-cut filter combining inclusion refinement with shrinking adjacent mesh, asymptotic
  endpoint escape, and the full finite-set-to-support-to-family-uniqueness assembly. The remaining
  source audit then established that the printed topology is the stronger `s(M,M_*)` topology, not
  `σ(M,M_*)`. It also found no source or uniform period convention fixing the undefined integral's
  division/refinement/improper-limit semantics. The same-net strong-to-ultraweak implication is
  kernel-checked, but the overall source relation is LEVEL C / UNCLEAR.
- **Decision so far:** publish the canonical theorem layer only. Publish neither experimental
  integral predicate nor a lower-family, resolution, or PVM structure. Publish the general
  fixed-projection decomposition and coherent support helpers under D004. The architecture remains
  OPEN / RED at a documented historical ambiguity. The concrete filter and uniqueness theorem
  remain scratch-only and are labeled `TRANSLATED_CANDIDATE`, not `SOURCE_EQUIVALENCE_CHECKED`.
- **Next bounded action:** do not manufacture source equivalence. The canonical continuity layer is
  now corrected and source-formalized in Sakai's strong topology. Proceed into Section 1.12 through
  the independent CFC-absolute-value/support/compactness chain. Revisit a public representation
  predicate only when a coherent PVM/integral construction or new primary evidence fixes its
  semantics.

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

## IQ-005 — element polar-decomposition packaging

- **Status:** ACTIVE / YELLOW; foundational wave reviewed
- **Affected streams:** general C-star API, support, CFC regularizer, ultraweak compactness, Verso
- **Question:** Which reusable helper surface is needed before packaging Sakai 1.12.1?
- **Decision so far:** keep Mathlib `CFC.abs` canonical. The stable annihilator bridges are
  `CFC.abs_mul_eq_zero_iff` and `CFC.mul_abs_eq_zero_iff`; the stable partial-isometry consequences
  are `IsStarProjection.mul_star_mul_self`, `mul_star_mul_self_assoc`, and `mul_star_self`. Continue
  to express partial-isometry semantics through `IsStarProjection (star u * u)` initially; use a
  distinct future `Ultraweak.ElementPolarDecomposition` module so the existing functional-polar-
  decomposition module remains unambiguous. Do not add a `polarPart` object until a consumer needs
  one.
- **Evidence:** checkpoint `6d24a2feb704cae6e4bedc00d6bc9f17c601f310` accepts the general
  $C^*$-API and a source-faithful scratch regularizer. The latter is contractive, satisfies the
  exact product identity, and converges after multiplication by `CFC.abs a`; the cluster-point
  handoff reuses the existing ultraweak compact closed ball and fixed-right-multiplication API.
  The independently reviewed bridge `WStarAlgebra.support_abs` / `support_abs_star` supplies the
  exact initial/final support orientations without a new support object or normality assumption.
- **Next bounded action:** begin WS-4 existence using only these accepted inputs. Keep packaging
  sequential and isolated after existence.
