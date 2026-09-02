# Sakai Proposition 1.15.1 — operator-topology interface audit

## Status

This is an interface and blocker audit. It does **not** claim that Sakai,
Proposition 1.15.1 has been formalized, translated into Lean, or proved from
the APIs listed below.

Source semantics and page references are recorded in
`SAKAI_1_15_1_SOURCE.md`. The comparison here is against:

- pinned Mathlib commit `476ab284693e554a6b48c5f5210cb4fb5ae51252`;
- original LeanOA commit `cb811c1006ae78a0ff1d175253200e1859843370`;
- the current Sak-AI tree.

The definitions and statement are on printed pages 33--34 (PDF pages 45--46)
of the inspected 1971 scan; the proof is on printed page 35 (PDF page 47). The
source statement is global: for a self-adjoint subalgebra
\(N\subseteq B(H)\), the following are equivalent: \(N\) is closed in WOT,
the \(\sigma\)-weak operator topology, SOT, the strongest operator topology,
or \(\sigma(B(H),B(H)_*)\). It is not merely an equivalence on norm-bounded
sets. The latter is the subject of the next result, Proposition 1.15.2.

## Exact source dictionary

Sakai fixes a complex Hilbert space \(H\), and \(B(H)\) is represented on the
Lean side by continuous linear endomorphisms, schematically
`H →L[ℂ] H`.

| Sakai topology | Source definition | Closest present Lean object | Match status |
|---|---|---|---|
| Weak operator topology (WOT) | Seminorms \(a\mapsto |(a\xi,\eta)|\) | Mathlib `ContinuousLinearMapWOT`; the local bridge uses `E →WOT[𝕜] F` | Exact for continuous linear maps once the scalar/dual pairing is instantiated |
| Strong operator topology (SOT) | Seminorms \(a\mapsto\lVert a\xi\rVert\) | Mathlib `PointwiseConvergenceCLM`; the local notation is `E →Lₚₜ[𝕜] F` | Exact pointwise-convergence model for the source SOT |
| “Strongest operator topology” | Seminorms \(a\mapsto(\sum_i\lVert a\xi_i\rVert^2)^{1/2}\) for square-summable \((\xi_i)\) | Current Sak-AI `Ultraweak.Strong`, written `s(M,P)` | Not yet an exact concrete match: `s(M,P)` is an intrinsic compatible-dual strong topology, and no theorem currently identifies it with Sakai's square-summable-vector topology on `B(H)` |
| \(\sigma\)-weak operator topology | Seminorms \(a\mapsto|\sum_i(a\xi_i,\eta_i)|\) for two square-summable vector sequences | `WeakBilin` for the pairing against `ContinuousLinearMap.vectorFunctionalSeriesSpan` | The concrete source test topology is represented without a new synonym, and the full predual topology maps continuously to it. The converse/equality remains the later representation theorem |
| \(\sigma(B(H),B(H)_*)\) | Weak topology induced by the predual | Sak-AI intrinsic `σ(M,P)`, instantiated with `ContinuousLinearMap.VectorFunctionalPredual` | The short carrier is canonically isometric to `vectorFunctionalClosure`; the concrete completion model and predual equivalence are proved, while identification with Sakai's later trace-class realization is not yet claimed |

The source's fifth condition and its second condition must remain distinct in
the formalization plan. Condition (2) is defined concretely from
square-summable coefficient series. Condition (5) uses the predual. Sakai first
proves that they give the same closed self-adjoint subalgebras in Proposition
1.15.1; their equality as topologies is only concluded in Corollary 1.15.6.
Using `σ(M,P)` for both before proving the concrete identification would assume
part of the later result.

Likewise, Sakai's named **strongest operator topology** is the modern
ultrastrong operator topology, not the Mackey topology. Current
`Ultraweak.Strong` is an appropriate abstract endpoint only after a concrete
identification theorem. Current `SakaiMackey` models the relevant Mackey
construction and must not be substituted definitionally for the named
strongest operator topology.

## What pinned Mathlib supplies

Pinned Mathlib supplies two of the concrete operator-topology carriers needed
at the beginning of the statement:

- `ContinuousLinearMapWOT` for WOT;
- `PointwiseConvergenceCLM` for pointwise convergence, hence SOT on `B(H)`.

It also supplies compatible-dual/locally-convex closure machinery that can
transport closure of convex sets when the two topologies have been proved to
have the same continuous dual. This is a useful proof engine, but it does not
itself construct the coefficient-completion predual of `B(H)` or identify the
operator topologies in Sakai's statement. The former has now been supplied by
the local bridge described below; the latter comparisons remain open.

| Finding | Classification | Decision |
|---|---|---|
| `ContinuousLinearMapWOT` and its Hilbert coefficient API | `PINNED VERSION ALREADY HAS IT` | Reuse it as WOT |
| `PointwiseConvergenceCLM` | `PINNED VERSION ALREADY HAS IT` | Reuse it as pointwise/SOT |
| Compatible-dual convex closure transport | `PINNED VERSION ALREADY HAS IT` | Reuse through the established Sak-AI intrinsic bridge |
| Continuous identity from pointwise/SOT to WOT | `LOCAL BRIDGE NEEDED` | Added without a new topology type |
| Concrete coefficient-completion predual and relative closure theorem | `LOCAL BRIDGE ADDED` | Reuse the completed predual, explicit-target relative theorem, and Mathlib-WOT instantiation |
| Current-Mathlib API renamings not changing the available mathematics | `NOT RELEVANT` | Do not update the dependency for naming alone |
| Upstream replacement for the local pointwise-to-WOT bridge | `FUTURE MATHLIB MIGRATION CANDIDATE` | None found now; remove the local declaration if one appears upstream |

The official Mathlib `master` tree inspected on 2026-09-01 still does not
supply the missing end-to-end concrete bridge: there is no ready-made `B(H)`
predual identification, no
complete concrete double-commutant/Kaplansky route that proves the required
closedness equivalence here, and no theorem identifying the square-summable
operator topologies with the intrinsic predual topologies.

## What original LeanOA and current Sak-AI supply

Original LeanOA at commit `cb811c1006ae78a0ff1d175253200e1859843370`
does not contain the concrete `B(H)` operator-topology/predual bridge needed for
Proposition 1.15.1.

Current Sak-AI has substantially more of the abstract proof architecture:

- intrinsic `Ultraweak`, written `σ(M,P)`;
- intrinsic `Ultraweak.Strong`, written `s(M,P)`;
- `SakaiMackey` and `WeakTestSpace`;
- invariant test-space and Kaplansky-density machinery;
- compatible-dual closure transport between the intrinsic strong and
  ultraweak models.

These are reusable dependencies for a proof. The coefficient-completion
predual is now connected to the intrinsic construction by a local `Predual`
instance, but this is not by itself a formalization of the source proposition:
the required one-sided concrete coefficient-series comparison is proved, while
the relative Mathlib-WOT closure argument is also proved. The concrete
strongest-operator topology remains unconnected.

## Present public APIs and their exact force

### WOT to pointwise/SOT

`PointwiseConvergenceCLM.toWOT` is the canonical continuous linear identity
map

```lean
(E →Lₚₜ[𝕜] F) →L[𝕜] (E →WOT[𝕜] F).
```

Thus the identity from pointwise/SOT to WOT is continuous. The simplification
lemma

```lean
PointwiseConvergenceCLM.toWOT_apply
```

says that this map does not change the underlying continuous linear map or its
value at a vector.

The consequence

```lean
PointwiseConvergenceCLM.isClosed_pointwise_of_isClosed_wot
```

proves that a WOT-closed set of continuous linear maps is pointwise/SOT closed
on the same underlying set. This is one expected implication in Proposition
1.15.1, and it is more general than the source in not requiring a self-adjoint
subalgebra. It does **not** prove the converse. In particular, it does not prove
that an SOT-closed self-adjoint subalgebra is WOT closed.

### Intrinsic strong to intrinsic ultraweak

For complete `P`, current Sak-AI proves that `s(M,P)` and `σ(M,P)` have the
compatible continuous-dual structure needed for convex closure transport. The
public theorem

```lean
Ultraweak.Strong.isClosed_iff_image_toUltraweakEquiv
```

states, for a real-convex set `S : Set s(M,P)`,

```lean
IsClosed S ↔
  IsClosed (Ultraweak.Strong.toUltraweakEquiv '' S).
```

A subalgebra carrier is real-convex, so this theorem is architecturally close
to the intrinsic strong/ultraweak part of Sakai's argument. Nevertheless, it
compares the abstract topologies `s(M,P)` and `σ(M,P)`. Until concrete
homeomorphism/identity results identify those carriers with Sakai's strongest
and predual weak topologies on `B(H)`, it proves no operator-topology clause of
Proposition 1.15.1 by itself.

The four APIs

- `PointwiseConvergenceCLM.toWOT`;
- `PointwiseConvergenceCLM.toWOT_apply`;
- `PointwiseConvergenceCLM.isClosed_pointwise_of_isClosed_wot`;
- `Ultraweak.Strong.isClosed_iff_image_toUltraweakEquiv`

therefore provide genuine reusable implications or transports, but they do
**not** prove Proposition 1.15.1.

## Source proof topology

Sakai's proof on printed page 35 (PDF page 47) uses

\[
\mathrm{WOT}
\leq \sigma\text{-}\mathrm{WOT}
\leq \sigma(B(H),B(H)_*)
\leq \tau(B(H),B(H)_*)
\]

and

\[
\mathrm{WOT}
\leq \mathrm{SOT}
\leq \text{strongest operator topology}
\leq s(B(H),B(H)_*)
\leq \tau(B(H),B(H)_*).
\]

The first nontrivial comparison uses the Cauchy–Schwarz tail estimate to show
that a square-summable coefficient-series functional is the operator-norm
limit of finite WOT coefficient functionals. For the reverse closedness
direction, Sakai takes the WOT closure of a Mackey-closed self-adjoint
subalgebra and applies Kaplansky density, using the norm-dense, self-adjoint,
invariant WOT test-functional space `V` inside the predual.

This explains why mere continuity arrows among WOT and SOT cannot close the
proof: the difficult direction is algebraic and uses self-adjointness,
invariance, predual density, and Kaplansky density.

## Global and bounded scopes

Proposition 1.15.1 compares **global closedness** in five topologies. No norm
bound appears in its statement.

Proposition 1.15.2 instead proves topology equivalence on bounded spheres for a
weakly closed self-adjoint subalgebra:

- WOT, σ-WOT, and `σ(N,N_*)` on bounded spheres;
- SOT, strongest operator topology, and `s(N,N_*)` on bounded spheres.

Consequently, a theorem that proves equality or convergence only on bounded
sets cannot be advertised as Proposition 1.15.1 without an additional argument
showing that it suffices for global closedness of the subalgebra.

## Precise blockers

1. **Concrete predual — RESOLVED at the completion-model level.**
   `ContinuousLinearMap.VectorFunctionalPredual` is the short carrier
   canonically isometric to the complete `vectorFunctionalClosure`; its canonical
   evaluation is isometrically equivalent to the operator space, and the root
   `Predual` structure is instantiated. Identification of this model with the
   trace-class realization used later by Sakai remains a later theorem, not an
   assumption here.

2. **WOT test-space integration — RESOLVED.** The concrete finite
   vector-coefficient span embeds densely and isometrically in the chosen
   predual, and `vectorFunctionalPredualSpan_sakaiInvariant` packages the
   proved involution and fixed left/right multiplier formulas in the exact
   invariant-test-space form required by the current Kaplansky API.

3. **Concrete σ-WOT bridge — RESOLVED in the source-required direction.**
   The weak topology generated by Sakai's `ℕ`-indexed, separately
   square-summable coefficient series is represented by the existing
   `WeakBilin` carrier. The full concrete-predual topology maps continuously
   to it, so series-test closedness implies ultraweak closedness. The
   converse/equality belongs to the trace-class/predual analysis later in
   §1.15 and must not be assumed early.

4. **Concrete strongest-operator bridge.** The topology generated by
   `(Σ ‖a ξ_i‖²)^(1/2)` must be defined and related to intrinsic
   `s(B(H),B(H)_*)`. Again, global equality is Corollary 1.15.6, later than the
   proposition currently targeted.

5. **Relative Kaplansky closure — RESOLVED.**
   `kaplansky_density_of_testWeakClosure_eq` accepts the closure target
   explicitly, `testWeakClosure_vectorFunctionalPredualSpan_eq_wotClosure`
   identifies the finite-core test-weak closure with Mathlib WOT closure, and
   `kaplansky_density_wotClosure` gives the concrete Mackey-density endpoint.
   This is a bounded unit-ball closure theorem, not yet the proposition's
   five-way global closedness equivalence.

6. **Carrier transport.** Closedness statements must be transported across
   the synonym/equivalence carriers without silently changing the underlying
   self-adjoint subalgebra or replacing global closedness by bounded closure.

7. **Reverse WOT/SOT direction.** Existing
   `isClosed_pointwise_of_isClosed_wot` supplies only WOT-closed implies
   SOT-closed. The converse for self-adjoint subalgebras still requires the
   source's Kaplansky/Mackey argument or a separately formalized concrete
   double-commutant theorem.

## Shortest honest route

The shortest route should reuse the current intrinsic infrastructure without
prematurely proving all of the later trace-class theory.

1. **Complete.** Define the concrete WOT coefficient test space `V` on
   `H →L[ℂ] H`, reusing `ContinuousLinearMapWOT` rather than introducing a
   second WOT.

2. **Complete for the required direction.** Separation, involution stability,
   left/right invariance, the sharp coefficient norm formula, norm convergence
   of square-summable coefficient-series partial sums, exact evaluation, and
   the full-predual-to-series-test continuous identity are proved. No converse
   series representation or topology equality is claimed.

3. **Complete as a completion model.** `vectorFunctionalClosure` supplies the
   complete predual object `P` needed by the current intrinsic `σ(M,P)`,
   `s(M,P)`, `WeakTestSpace`, and `SakaiMackey` APIs. It has deliberately not
   been identified with trace class.

4. **Complete.** The relative Kaplansky/Mackey closure theorem accepts an
   explicit test-weak-closure target and is instantiated for the concrete
   self-adjoint subalgebra inside its Mathlib-WOT closure. This is the central
   relative-density step in the reverse implication and genuinely uses the
   source hypotheses.

5. Connect the already exact concrete endpoints: Mathlib WOT and
   pointwise/SOT, using `toWOT` and
   `isClosed_pointwise_of_isClosed_wot` for the easy implication and the
   Kaplansky closure result for the reverse implication.

6. **Complete for concrete σ-WOT in the required direction.** Its source test
   family is represented by the existing weak-bilinear machinery without a
   topology synonym. Represent the strongest-operator topology with existing
   induced/seminorm machinery if possible and prove only the comparison needed
   for Proposition 1.15.1. Do not claim global equality with `σ(B(H),P)` or
   `s(B(H),P)` until the later Corollary 1.15.6 infrastructure is proved.

7. Package the final theorem as equivalence of five global closedness
   predicates for a self-adjoint subalgebra, preserving the source's lack of an
   explicit unital assumption. Only then should Proposition 1.15.1 be marked
   formalized.

This route uses the current Sak-AI semantic core and avoids duplicating WOT,
SOT, compatible-dual closure, or Kaplansky machinery. The coefficient/predual
instantiation and the source-required one-sided coefficient-series comparison
are now complete, as is the ambient-relative WOT-closure density argument. The
irreducible remaining work is the concrete ultrastrong predicate and its
required comparison, followed by the final source-faithful closedness assembly.
