# Sakai Theorem 1.12.1: element polar decomposition

Date: 2026-08-31

Workstream: WS-5 closeout, Sakai Section 1.12

Baseline: `9ef19a9f13080503ee16951d32889e74ce32a53b`

## Source and exact statement

The source is Sakai, *C*-Algebras and *W*-Algebras, Section 1.12, printed pp. 27--28
(local PDF pp. 39--40).  The section contains one numbered result, Theorem 1.12.1.

For an element `a` of a $W^*$-algebra, Sakai defines

```text
|a| = (star a * a)^(1/2)
```

and asserts that there is a unique `u` such that

```text
a = u * |a|,
star u * u = s(|a|),
u * star u = s(|star a|).
```

Sakai calls `u` a partial isometry and calls this factorization the polar decomposition of `a`.
The formal statement retains both support equations.  Mathlib's `CFC.abs` is the canonical
realization of `|a|`; Sak-AI introduces neither a second absolute value nor a new partial-isometry
predicate.

## Public production declarations

All three source-facing declarations live in
`LeanOA.Ultraweak.ElementPolarDecomposition` under the ordinary intrinsic assumptions

```lean
{M : Type*}
[CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M].
```

The WS-4 existence theorem remains public:

```lean
WStarAlgebra.exists_element_polar_decomposition (a : M) :
  ∃ u : M,
    a = u * CFC.abs a ∧
    star u * u =
      (WStarAlgebra.support
        ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩).1 ∧
    u * star u =
      (WStarAlgebra.support
        ⟨CFC.abs (star a),
          (CFC.abs_nonneg (star a)).isSelfAdjoint⟩).1
```

WS-5 adds the weaker natural uniqueness interface:

```lean
WStarAlgebra.element_polar_decomposition_unique
    (a u v : M)
    (hu : a = u * CFC.abs a)
    (hu_initial : star u * u =
      (WStarAlgebra.support
        ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩).1)
    (hv : a = v * CFC.abs a)
    (hv_initial : star v * v =
      (WStarAlgebra.support
        ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩).1) :
    u = v
```

and packages the exact source theorem as:

```lean
WStarAlgebra.existsUnique_element_polar_decomposition (a : M) :
  ∃! u : M,
    a = u * CFC.abs a ∧
    star u * u =
      (WStarAlgebra.support
        ⟨CFC.abs a, (CFC.abs_nonneg a).isSelfAdjoint⟩).1 ∧
    u * star u =
      (WStarAlgebra.support
        ⟨CFC.abs (star a),
          (CFC.abs_nonneg (star a)).isSelfAdjoint⟩).1
```

The `existsUnique_...` spelling follows the existing Sak-AI naming convention.  The separate
existence theorem is retained because it is a useful witness-producing API in its own right.

## Existence route

The production existence proof follows Sakai's argument rather than obtaining the theorem from a
stronger imported polar-decomposition package.

For positive integers, reindexed by `n : ℕ` through `n + 1`, it privately constructs

```text
h_n = (star a * a + (n + 1)^-1 • 1)^(1/2),
a_n = a * (star a * a + (n + 1)^-1 • 1)^(-1/2).
```

Canonical CFC and order results prove that `‖a_n‖ ≤ 1`, that `a_n * h_n = a`, and that
`h_n → CFC.abs a` in norm.  Hence `a_n * CFC.abs a → a` in norm.  Ultraweak compactness of
the closed unit ball supplies a filter cluster point `b`.  Fixed-right-multiplication continuity,
not joint ultraweak continuity, then gives

```text
b * CFC.abs a = a.
```

Writing

```text
p = support |a|,
q = support |star a|,
u = q * b * p,
```

the support-defect argument proves `star u * u = p`; the final-projection and left-support APIs
then prove `u * star u = q`.  The regularizer, chosen predual, cluster filter, and cutdown
scaffolding remain private.  Production imports no `Scratch` module and uses no PVM, spectral
integral, sequential compactness, strong topology, or joint ultraweak multiplication.

The source consequence

```lean
CFC.mul_star_eq_of_eq_mul_abs
```

records `a * star a = u * (star a * a) * star u` separately at abstract nonunital real-CFC
generality.

## Sakai's uniqueness argument

On printed p. 28, Sakai lets `p = s(|a|)` and assumes that

```text
a = u * |a| = u' * |a|
```

are two polar decompositions.  He obtains

```text
star u' * a = |a| = star u' * u * |a|
```

and hence

```text
(p - star u' * u) * |a| = 0.
```

He considers the ultraweakly closed right ideal annihilated by `p - star u' * u`, represents it as
`eM`, and uses the leastness of the support to get `p ≤ e`.  Thus
`(p - star u' * u) * p = 0`.  Since both polar factors have initial projection `p`, he also has
`p * star u' * u * p = star u' * u`, and concludes first `p = star u' * u` and then `u' = u`.

## Algebraic uniqueness in Lean

The production proof is a shorter formulation of the same support argument through Sak-AI's
established support-kernel API.  From the two factorizations it obtains

```text
(u - v) * CFC.abs a = 0.
```

`WStarAlgebra.mul_support_eq_zero_iff` is precisely the reusable abstraction of Sakai's
closed-right-ideal step and gives

```text
(u - v) * support |a| = 0.
```

Each initial-support equation makes the corresponding factor fixed on the right:

```text
u * support |a| = u,
v * support |a| = v.
```

These are direct applications of `IsStarProjection.mul_star_mul_self_assoc`.  Expanding the last
zero product therefore gives `u - v = 0`, hence `u = v`.  No topology, compactness, regularizer,
norm estimate, final support, or reconstruction of a closed ideal enters the uniqueness proof.

Both initial-support equations are genuinely used: one is needed to show that `u` is fixed by the
support and the other to show the same for `v`.  The final-support equations are unnecessary as
*hypotheses of the uniqueness lemma*.  They are nevertheless retained in the exact `ExistsUnique`
predicate because they are part of Sakai's stated polar decomposition and are substantive output
of the existence theorem.  Their redundancy for this algebraic comparison is not a license to
weaken the source theorem.

## Duplicate and generality audit

The uniqueness theorem and its immediate helper requirements were searched in:

- Sak-AI at baseline `9ef19a9f13080503ee16951d32889e74ce32a53b`;
- pinned Mathlib at `476ab284693e554a6b48c5f5210cb4fb5ae51252`;
- the available read-only current-Mathlib checkout at
  `be865aa50cc0364be66c3941a6dc0c845a2c2ceb`;
- the read-only original LeanOA checkout at
  `cb811c1006ae78a0ff1d175253200e1859843370`.

No element-polar-decomposition uniqueness theorem, canonical polar factor, or partial-isometry
predicate was found in those trees.  The existing Sak-AI declarations

```text
WStarAlgebra.mul_support_eq_zero_iff
IsStarProjection.mul_star_mul_self_assoc
```

already provide the optimal proof interface, so WS-5 adds no general C*-algebra helper.

It would be possible to state a more abstract theorem for an arbitrary self-adjoint element, an
arbitrary projection, and an explicit kernel-detection hypothesis.  That statement would expose
proof machinery rather than a recognizable current consumer.  The chosen public theorem is
therefore the weakest natural *polar-decomposition* statement: it omits the unused final supports
but retains the canonical `CFC.abs` and intrinsic W-star support object.  No `polarPart` choice
function, bundled polar decomposition, or `IsPartialIsometry` predicate is introduced.

## Source-fidelity classification

The source statement has been checked directly against Sakai's scan.  The final `ExistsUnique`
predicate contains the factorization and both support equations with the same orientations as the
book.  The formal proof changes only the implementation of uniqueness by invoking the already
proved support-kernel equivalence in place of reconstructing its closed right ideal.

```text
Statement fidelity: SOURCE_EQUIVALENCE_CHECKED
Existence: PROOF_CHECKED
Uniqueness: PROOF_CHECKED
Exact ExistsUnique packaging: PROOF_CHECKED
Sakai Theorem 1.12.1: SOURCE-FORMALIZED
Section 1.12: COMPLETE
```

This classification applies to Theorem 1.12.1 itself.  It makes no claim about the unresolved
Radon--Stieltjes semantics in Section 1.11.

## Proof integrity and validation status

A focused production elaboration passed while drafting this report:

```text
lake env lean LeanOA/Ultraweak/ElementPolarDecomposition.lean
```

Independent signature tests of the uniqueness and exact `ExistsUnique` declarations also passed.
`#print axioms` reports, for each of

```text
WStarAlgebra.element_polar_decomposition_unique
WStarAlgebra.existsUnique_element_polar_decomposition
```

exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The focused diff has no added `axiom`, `sorry`, or `admit`, and passes `git diff --check`.

```text
CUSTOM AXIOMS ADDED: 0
SORRY/ADMIT ADDED: 0
OTHER MATHEMATICAL PLACEHOLDERS ADDED: 0
```

The integration closeout suite passed:

```text
lake build                                      -- 3119 jobs, success
lake lint                                       -- linting passed for LeanOA
cd docs
lake build SakAIDocs                            -- 3480 jobs, success
lake exe vbp build                              -- success
lake exe vbp check                              -- ok: true, zero errors, 503 entries
cd ..
./scripts/build-verso-site.sh                   -- success, including vbp check
```

The generated site contains its root, graph, summary, search, index, theorem chapter, manifest,
and HTML cache.  Direct inspection of the graph gives 105 nodes and 182 statement-dependency
edges.  Both new nodes are formalized with complete ancestors, all six intended new edges are
present, and neither node has a missing-declaration or unknown-reference warning.  The generated
theorem page resolves `WStarAlgebra.existsUnique_element_polar_decomposition` as complete.

Repository-wide production-Lean scans find no `sorry`, `admit`, custom `axiom`, or `Scratch`
import.  The final diff passes `git diff --check`.  The only documentation-build warnings are
pre-existing warnings replayed from three pinned SubVerso/Verso Blueprint modules; no Sak-AI
module emits a warning.

Assessment: **IMPROVED -- SOURCE THEOREM / SECTION COMPLETION / MATHLIB REUSE / COMBINATION**.
