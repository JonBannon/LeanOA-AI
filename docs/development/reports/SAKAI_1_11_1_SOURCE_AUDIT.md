# Sakai Lemma 1.11.1 source audit

## Primary source

- Source: Sakai, *C*-algebras and W*-algebras* (1971).
- Local scan: `/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.
- Lemma 1.11.1: printed p. 26, PDF p. 38.
- Definition of `s(M,M_*)`: Definition 1.8.6, printed p. 20, PDF p. 32.

The surrounding section fixes a W-star algebra `M`, a self-adjoint element `h : M`, and

```text
e(λ) = s((λ 1 - h)⁺).
```

The printed lemma says that, for a real sequence `(λₙ)`,

```text
(∀ n, λₙ ≤ λ)  and  λₙ → λ
  ⇒
e(λₙ) → e(λ) in s(M,M_*).
```

There is **no monotonicity hypothesis**. This is not an editorial omission that may safely be
filled in: immediately below it, Theorem 1.11.3(2) separately specifies a monotone increasing
sequence. Lean's zero-based `ℕ` is only a harmless reindexing of Sakai's `n = 1, 2, ...`.

## Topology and hypotheses

| Coordinate | Source content |
| --- | --- |
| Algebra | W-star algebra `M` with Banach predual `M_*` |
| Element | self-adjoint `h ∈ M` |
| Parameters | real sequence `λₙ` and real `λ` |
| Side condition | `λₙ ≤ λ` for every `n` |
| Scalar limit | ordinary real convergence `λₙ → λ` |
| Operator limit | intrinsic strong topology `s(M,M_*)` |
| Monotonicity | none |
| Finite sums, mesh, endpoints | none; those belong to the following results |

Definition 1.8.6 generates `s(M,M_*)` from all positive
`σ(M,M_*)`-continuous functionals `φ` and the seminorms

```text
αφ(x) = φ(x* x)^(1/2).
```

It is not norm topology and should not be identified definitionally with the strong operator
topology of an arbitrary concrete representation. Sakai proves a bounded-set comparison with a
concrete representation only later, in Proposition 1.15.2.

## Source proof and the formal completion

Sakai lets `p` be the least upper bound of the projections `e(λₙ)`. Norm continuity of positive
cutoffs and

```text
0 ≤ (λ1-h)⁺ - (λₙ1-h)⁺ ≤ (λ-λₙ)1
```

show that `(λ1-h)⁺(1-p)=0`. Support leastness gives `e(λ) ≤ p`, while monotonicity and
`λₙ ≤ λ` give the reverse inequality.

The printed proof suppresses one point that matters in Lean: identifying the supremum does not by
itself prove convergence of a nonmonotone sequence. The formal proof completes the argument by:

1. choosing a strictly increasing auxiliary sequence `μₖ → λ`;
2. proving strong convergence of `e(μₖ)` from the existing ultraweak monotone theorem and the
   projection identity
   `αφ(q-p)² = ‖φ(q-p)‖` for `p ≤ q` (the value is nonnegative);
3. observing that, for every fixed `k`, eventually
   `e(μₖ) ≤ e(λₙ) ≤ e(λ)`;
4. squeezing each defining strong seminorm.

This preserves the exact source hypotheses and supplies the omitted topological detail without
adding monotonicity.

## Earlier source dependencies

| Source result | Printed/PDF page | Role |
| --- | ---: | --- |
| Definition 1.1.2 | 1 / 13 | W-star algebra and predual |
| Definition 1.1.3 | 2 / 14 | “uniform” means norm topology |
| Definition 1.4.3 | 8 / 20 | positive part |
| Lemma 1.7.4 | 15–16 / 27–28 | weak convergence of bounded increasing directed sets to their LUB |
| Corollary 1.7.9 | 18 / 30 | generated W-star subalgebra and commutativity preservation |
| Definition 1.8.6 | 20 / 32 | intrinsic strong topology |
| Theorem 1.8.9 | 20 / 32 | topology-comparison context `σ ≤ s ≤ s* ≤ τ` |
| Proposition 1.10.2 | 24–25 / 36–37 | complete projection lattice |
| Definition 1.10.3 | 25 / 37 | support projection |
| Proposition 1.10.4 | 25 / 37 | support belongs to the generated W-star algebra |

Only Proposition 1.10.4 is cited explicitly in the immediate §1.11 setup; the other uses are
structural or contextual. Theorem 1.8.9 records the topology hierarchy but is not needed by the
new direct strong-seminorm proof.

## Search boundary and negative evidence

The remainder of §1.11 contains no local reference list, exercise, footnote, or concluding remark
that adds a monotonicity hypothesis to Lemma 1.11.1. The subject index (printed p. 253, PDF p. 265)
points “Spectral resolution” to p. 26, “s-topology” to p. 20, and support to p. 25; these lead back
to the statement and definitions audited above and supply no alternate version of the lemma.

## Downstream role

- The lemma supplies the canonical family with the continuity law appearing in Theorem 1.11.3(2).
- The uniqueness paragraph on printed p. 27 uses the analogous left-continuity law for a competing
  resolution.
- The exact canonical theorem does not fix the undefined division/refinement/improper-limit
  semantics of Sakai's “abstract Radon--Stieltjes integral.” The Level C decision for 1.11.3 is
  unchanged.
- Section 1.12 does not depend on Lemma 1.11.1.

## Certification

The statement is **LEVEL A / source unambiguous**. It is represented by
`WStarAlgebra.tendsto_spectralProjectionIio_strong`; the filter-general version is
`WStarAlgebra.tendsto_spectralProjectionIio_strong_of_tendsto_of_eventually_le`.
