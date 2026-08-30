# Sakai Radon--Stieltjes bridge worker report

Status: **kernel-checked scratch result; source semantics still explicit; no production API**

Workstream: `rs_bridge`

Baseline: `1cd3a6552cb3866d1f7cbfc01a06c27e174355a5`

Scratch file: `Scratch/SakaiRadonStieltjesBridge.lean`

## Result

The analytic bridge missing from the fixed-projection support proof can be stated without defining
a public spectral resolution, PVM, or operator-valued integral.  The source division system and
its filter remain parameters.  Once its identity moments and asymptotic endpoints are supplied,
cofinal restriction to divisions carrying prescribed cuts gives both limits required downstream:

```text
translated total:
  Σ (r - left_i) (e(right_i) - e(left_i))  →  r • 1 - a

varying lower comparison:
  (r - s)e(s) - (r - s)e(left_endpoint)         →  (r - s)e(s).
```

The residual is not deleted at any finite stage.  It vanishes only after the left endpoint tends
to `-∞` and the family tends ultraweakly to `0` there.

## Source check

I re-read Sakai, Theorem 1.11.3, printed pages 26--27 (PDF pages 38--39), including the four
conditions on the competing family and the uniqueness paragraph.  The relevant displayed input is
the abstract relation

```text
a = ∫ λ de(λ)
```

in the `σ(M, M_*)` topology.  The proof translates it to

```text
r1 - a = ∫ (r - λ) de(λ)
```

and splits at `r`.  The book does not give, at that point, a formal Moore--Smith index type,
refinement order, tag convention, or finite endpoint convention for the Radon--Stieltjes symbol.
It also does not restate a topology beside each endpoint arrow.  The scratch theorem makes the
topology the specified ultraweak topology used by the representation and records this as an
interpretive choice, not as a source-proved equivalence.

The half-open convention remains the one verified in the finite/source lane:

```text
e(t) - e(q)  corresponds to  [q,t).
```

Thus an atom at a prescribed cut belongs to the band above the cut, as required for the eventual
`Iio` support.

## Exact finite convention

For an unbundled finite cut sequence `cut : ℕ → ℝ`, the scratch file defines

```text
identityMomentSum e cut n
  = Σ i<n, cut(i) • (e(cut(i+1)) - e(cut(i)))

translatedMomentSum e r cut n
  = Σ i<n, (r-cut(i)) • (e(cut(i+1)) - e(cut(i))).
```

`translatedMomentSum_eq_smul_endpoint_sub_identity` proves the exact algebraic identity

```text
translatedMomentSum
  = r • (e(right_endpoint) - e(left_endpoint)) - identityMomentSum.
```

This theorem uses no order, topology, monotonicity, projection property, exact endpoint, or limit.
In particular, it exposes the unweighted endpoint band rather than silently replacing it by `1`.

## Kernel-checked bridge declarations

The scratch file contains the following checked implications.

### Minimal translation theorem

`tendsto_translatedMomentSum_of_cofinal` assumes:

```lean
hrefine : Tendsto refine lJ lD

hmoment : Tendsto
  (fun d ↦ toUltraweak ℂ P (identityMomentSum e (cut d) (bands d))) lD
  (𝒩 (toUltraweak ℂ P a))

hband : Tendsto
  (fun d ↦ toUltraweak ℂ P
    (e (cut d (bands d)) - e (cut d 0))) lD
  (𝒩 (toUltraweak ℂ P 1)).
```

It concludes convergence of the translated sums along `lJ` to `r • 1 - a`.  This is the smallest
signature for translation itself: separate endpoint limits are not logically needed once the
unweighted total band is known to converge to `1`.

### Separate endpoint corollary

`tendsto_translatedMomentSum_of_cofinal_of_endpoint_limits` replaces `hband` by

```lean
e(left_endpoint d)  → 0,
e(right_endpoint d) → 1,
```

and derives `hband` by ultraweak subtraction.

### Residual conclusions

`tendsto_leftEndpointResidual_of_cofinal` proves

```text
c • e(left_endpoint(refine j)) → 0.
```

`tendsto_projection_sub_leftEndpointResidual_of_cofinal` then proves the varying lower-bound
limit used by two-sided order closedness.  No stronger finite inequality
`(r-s)e(s) ≤ u_j` is assumed.

`tendsto_translated_and_lowerResidual_of_cofinal` packages the translated and residual conclusions
from identity moments plus the two endpoint-projection limits.

### Family-level asymptotic endpoint formulation

`tendsto_translated_and_lowerResidual_of_cofinal_of_endpoint_escape` separates the source and
division inputs:

```lean
Tendsto (fun t ↦ toUltraweak ℂ P (e t)) atBot (𝒩 (toUltraweak ℂ P 0))
Tendsto (fun t ↦ toUltraweak ℂ P (e t)) atTop (𝒩 (toUltraweak ℂ P 1))

Tendsto (fun d ↦ cut d 0) lD atBot
Tendsto (fun d ↦ cut d (bands d)) lD atTop.
```

Composition yields the endpoint-projection nets and hence both required conclusions.  This is the
closest explicit formulation to Sakai's endpoint clauses without choosing integral semantics.

All ultraweak results require only a C-star algebra with the repository's order instances and a
specified complete predual; no `WStarAlgebra` instance is used.  The order instances enter through
the current separately-continuous-ultraweak-multiplication API used to scale by a real scalar as
left multiplication by a scalar element.  They are not used by the finite translation identity.

## Exact use of cofinality

The bridge uses cofinality only as

```lean
Tendsto refine lJ lD
```

and composes each source limit with it.  It assumes neither equality of filters nor that inserted
divisions are exact endpoints.

The parallel refinement scratch at commit `12da4c2730e799c400896d227f24c71afa9467ef`
kernel-checks two concrete ways to discharge this hypothesis if finite cut sets are chosen:

- for bare `Finset ℝ` refinement at `atTop`, Mathlib's
  `Filter.tendsto_comp_val_Ici_atTop` handles the subsystem containing a prescribed finite set;
- for a richer source filter `L` with `Tendsto id L atTop`, adjoining prescribed cuts by union is
  eventually literally the identity, so it preserves and reflects every target-filter limit.

This is especially useful because endpoint, mesh, admissibility, or other conditions may stay in
`L`; cut insertion does not need a new filter theorem for each such condition.

The follow-up parallel enumeration scratch at commit
`8291f21b1b8b30d56674862a153874055620bc3f` also kernel-checks the concrete adapter from
`Finset ℝ` to the unbundled inputs used here:

- `bandCount d = d.card - 1`;
- `orderedCut d` uses Mathlib's canonical increasing `orderEmbOfFin` in range and is max-tailed;
- genuine adjacent bands are strictly ordered;
- every prescribed cut has an in-range index;
- the selected minimum and maximum tend to `atBot` and `atTop` along Finset `atTop`.

Thus sorted enumeration and endpoint escape are no longer mathematical blockers if that concrete
filter is selected.  The source-equivalence decision remains separate.

## Interface with the checked finite/support layers

For fixed `s < r`, the remaining finite data on the prescribed subsystem are explicit:

- every selected cut sequence is monotone;
- indices `j_s ≤ j_r` satisfy `cut j_s = s` and `cut j_r = r`;
- the total band count is split at `j_r`.

The prior finite scratch at commit `6e349da` then supplies, without new analytic assumptions:

- translated total = below part - above magnitude;
- positivity of both pieces;
- fixed-projection extraction/annihilation by `e(r)`;
- the exact lower inequality
  `(r-s)(e(s)-e(left_endpoint)) ≤ below`.

The production `Ultraweak.ProjectionDecomposition` layer and the support-recovery scratch consume
exactly the translated limit and varying lower net proved here.  Positivity, localization, CFC
positive/negative-part identification, continuity from below, and support equality therefore do
not need to be reproved in this bridge.

## Remaining semantic blocker

The source representation is **not yet source-equivalent to a Lean predicate**.  The smallest
honest unresolved choice is to specify data

```text
D, lD, cut, bands
```

and certify that Sakai's Radon--Stieltjes clause means `hmoment` for the left-endpoint convention
above.  Choosing `Finset ℝ` with inclusion/`atTop` is attractive and the cofinality mechanics are
already checked.  The parallel enumeration scratch also checks a total sorted evaluator and
endpoint escape.  Making this concrete model *the source semantics* still requires:

1. proof that the source's abstract integral entails convergence of these left-endpoint sums;
2. if the intended integral instead ranges over tagged partitions, a tag-independence/refinement
   theorem connecting that semantics to left endpoints;
3. for a richer filter than bare Finset `atTop`, verification that its admissibility conditions
   still force endpoint escape;
4. routine positional glue showing that the recovered indices of prescribed `s < r` occur in the
   required order and split `bandCount` in the form consumed by the finite lane.

These are not support-theoretic blockers.  They are primarily statement-translation uncertainty
plus finite-division engineering.  Assuming `hmoment` is the smallest noncircular explicit
approximation hypothesis; assuming the desired translated limit or support equality would be
circular and was not done.

## Future PVM compatibility

A future PVM can instantiate

```text
e(t) = E(Iio t),
e(t) - e(q) = E(Ico q t)
```

after its finite additivity/order API is available.  Its simple-integral approximants can then
discharge `hmoment` and the endpoint limits without changing any bridge conclusion.  For that
reason this scratch does not introduce a competing public resolution or integral structure.

## Validation

Commands run in the isolated worktree
`/private/tmp/sakai-rs-bridge-1cd3a65` on branch `agent/rs-bridge`:

```text
lake build LeanOA.Ultraweak.ProjectionDecomposition
lake env lean Scratch/SakaiRadonStieltjesBridge.lean
git diff --check
```

The focused build passed 3,047 jobs.  The final scratch elaboration is warning-free.  The scratch
contains no `sorry`, `admit`, or added axiom.  No production source, shared coordination document,
Verso source, dependency checkout, remote, or master worktree was changed.

## Recommendation

Keep both the moment definitions and bridge scratch-only for now.  The algebraic identity and
generic cofinal-map theorem are stable, but publishing a named Radon--Stieltjes predicate before
the source division semantics is settled would hide rather than solve the fidelity question.
