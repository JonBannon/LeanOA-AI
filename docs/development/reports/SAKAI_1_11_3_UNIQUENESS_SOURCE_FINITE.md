# Sakai 1.11.3 uniqueness: source reconstruction and finite decomposition

Status: **worker evidence; scratch Lean only; no public spectral-family or integral API**

## Source location and method

The source is Sakai, *C\*-Algebras and W\*-Algebras* (1971), Section 1.11,
Theorem 1.11.3.

- Read-only scan: `/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.
- The theorem begins on printed page 26, PDF page 38.
- The existence calculation and the complete uniqueness paragraph are on printed page 27, PDF
  page 39.
- The pages were checked both by 300-dpi OCR and directly against rendered page images.  The
  mathematical reconstruction below follows the images where OCR confused `s`, `e`, `σ`, and
  integral endpoints.

## Exact source theorem relevant to uniqueness

For a self-adjoint `x` in a W\*-algebra `M`, Sakai calls a real-indexed system of projections
`e(λ)` a resolution of the identity when it has the following properties:

1. `λ ≤ μ` implies `e(λ) ≤ e(μ)`.
2. If `λ_n` is monotone increasing, `λ_n ≤ λ`, and `λ_n → λ`, then
   `e(λ_n) → e(λ)` in the `σ(M,M_*)` topology.
3. `e(λ) → 1` as `λ → +∞` and `e(λ) → 0` as `λ → -∞`.
4. `x` is represented by the abstract Radon--Stieltjes integral
   `∫_{-∞}^{∞} λ de(λ)`, taken with respect to the `σ(M,M_*)` topology.  For the canonical family,
   Sakai also localizes that integral to the norm-bounded interval used in the existence proof.

The theorem says that such a resolution exists and is unique.  In the uniqueness paragraph Sakai
assumes that `e'` is another system of projections satisfying clauses 1--3 and the same integral
representation of `x`.  He does **not** assume exact values `e'(L)=0`, `e'(R)=1` at finite cuts, nor
norm convergence of moment sums.

Clause 3 does not repeat a topology after each displayed limit.  The surrounding theorem uses the
`σ(M,M_*)` topology in clause 2 and for the integral, so the natural formal reading is the same
ultraweak topology (or its equivalent order-limit content for monotone projections).  This should
be made explicit, rather than silently chosen, in any eventual source theorem.

## Source uniqueness calculation

For an arbitrary real cutoff `λ₀`, Sakai writes the following chain.

1. Translate the represented operator:

   ```text
   λ₀ 1 - x = ∫ (λ₀-λ) de'(λ).
   ```

2. Split that integral at `λ₀` into a below-cut and an above-cut integral.
3. Conclude that the positive part is the below-cut truncated-affine integral:

   ```text
   (λ₀ 1-x)⁺ = ∫_{-∞}^{λ₀} (λ₀-λ) de'(λ).
   ```

4. Take support and identify it with all spectral mass strictly below the cutoff:

   ```text
   support ((λ₀ 1-x)⁺)
     = ∫_{-∞}^{λ₀-0} de'(λ)
     = e'(λ₀-0)
     = e'(λ₀).
   ```

5. The canonical family was defined by
   `e(λ₀)=support ((λ₀ 1-x)⁺)`, so `e'(λ₀)=e(λ₀)` for every `λ₀`.

The last equality `e'(λ₀-0)=e'(λ₀)` is precisely the one-sided continuity in clause 2.  It fixes
the convention as

```text
e'(r) = E(Iio r),             e'(s)-e'(q) = E(Ico q s).
```

An atom at `r` is excluded from `e'(r)` and belongs to the band `[r,s)` above `r`.  The coefficient
`r-λ` is zero at `λ=r`, so the element-valued integral may be displayed with upper endpoint `r`
without changing its value; the support projection must nevertheless use the left limit `r-0`.

## Source ambiguity and implicit steps

There are three points which a formal proof must not hide.

1. The scan's final displayed line literally prints an `e`-shaped symbol applied to the positive
   algebra element, although Section 1.10 and the opening of Section 1.11 use `s(a)` for support and
   define `e(λ)=s((λ1-x)⁺)`.  Typing makes the displayed application impossible as the scalar-indexed
   family.  It must be read as `s((λ₀1-x)⁺)` (a typographical/notation slip), after which the next
   equality is the defining equation for the canonical `e(λ₀)`.
2. The uniqueness paragraph performs the split at `λ₀` directly at the abstract-integral level.
   It does not display the cofinal refinement argument which inserts `λ₀` into each finite
   division.  A Lean proof from finite approximants must establish that refinement/cofinality.
3. The assertions that the below and above pieces are the positive and negative parts, and that
   the support of the below weighted integral is all of `e'(λ₀-0)`, are compressed into one line.
   They require positivity, orthogonality, fixed-projection limit passage, positive lower bounds on
   every earlier cut, and continuity from below.  These are consequences to prove, not additional
   resolution axioms.

## Kernel-checked finite model

`Scratch/SakaiUniquenessFinite.lean` uses an explicit term

```lean
e : ℝ → {p : A // IsStarProjection p}
he : Monotone e
```

over a nonunital C\*-algebra with the standard projection order.  It introduces no structure,
typeclass, PVM, integral, W\*-algebra assumption, or topology.  Its band is

```lean
band e q s = (e s).1 - (e q).1.
```

The following facts are kernel-checked.

### Bands and cutoff insertion

- `isStarProjection_band`: an ordered band is a star projection.
- `band_add_band`: `[q,r)+[r,s)=[q,s)` algebraically.
- `mul_band_eq_self_of_le` and `band_mul_eq_self_of_le`: `e(r)` fixes a band below `r` on both
  sides.
- `mul_band_eq_zero_of_le` and `band_mul_eq_zero_of_le`: `e(r)` kills a band starting at or above
  `r` on both sides.
- `mul_band_eq_lower_band` and `band_mul_eq_lower_band`: multiplying a crossing band `[q,s)` by
  `e(r)` extracts `[q,r)`.
- `lower_band_mul_upper_band_eq_zero` and its reverse: the two pieces created by insertion are
  orthogonal.
- `insertCut` inserts an arbitrary `r` after a specified finite cut.
- `band_at_insertCut_add_succ`: the old crossing band is the sum of the two inserted bands.
- `sum_band_insertCut`: the full unweighted band sum is unchanged by insertion.

The one-atom scratch family checks the convention rather than relying on prose:

- `singleAtomLowerFamily p atom r` is `p` exactly when `atom < r`;
- `singleAtomLowerFamily_at` says the atom is absent at its own cut;
- `band_singleAtom_at_of_lt` says `[atom,s)` contains it;
- `band_singleAtom_to_atom_of_le` says `[q,atom)` does not.

### Exact translated-moment split

For a monotone finite division `cut`, suppose `cut k=r`.  Define

```text
w = Σ_{i<k+n} (r-cut i) (e(cut(i+1))-e(cut i)),
u = Σ_{i<k}   (r-cut i) (e(cut(i+1))-e(cut i)),
v = Σ_{i<n}   (cut(k+i)-r) (e(cut(k+i+1))-e(cut(k+i))).
```

Lean represents the division by a globally monotone `cut : ℕ → ℝ`, but every theorem in this
paragraph reads only the displayed finite prefix.  Any finite monotone division has such an
extension (for example, constant after its right endpoint), so this encoding adds no mathematical
hypothesis to Sakai's finite calculation.

Then the scratch file proves:

```text
w = u-v;
0 ≤ u;
0 ≤ v;
e(r)u=u=u e(r);
e(r)v=0=v e(r);
uv=0;
w⁺=u;
e(r)w=u=w e(r).
```

The corresponding Lean declarations are
`translatedMomentSum_eq_below_sub_above`, `belowTranslatedSum_nonneg`,
`aboveTranslatedMagnitude_nonneg`, `mul_belowTranslatedSum_eq_self`,
`belowTranslatedSum_mul_eq_self`, `mul_aboveTranslatedMagnitude_eq_zero`,
`aboveTranslatedMagnitude_mul_eq_zero`,
`belowTranslatedSum_mul_aboveTranslatedMagnitude_eq_zero`,
`posPart_translatedMomentSum_eq_below`, `mul_translatedMomentSum_eq_below`, and
`translatedMomentSum_mul_eq_below`.

The positive-part theorem reuses Mathlib's `CFC.posPart_negPart_unique`; it does not create a
parallel functional calculus.

### The indispensable left-endpoint residual

If the same division contains `cut j=s`, with `j≤k` and `cut k=r`, then

```text
(r-s) • (e(s)-e(cut 0)) ≤ u.
```

This is `smul_band_le_belowTranslatedSum`.  Its expanded form is
`smul_projection_sub_residual_le_belowTranslatedSum`:

```text
(r-s) • e(s) - (r-s) • e(cut 0) ≤ u.
```

The residual cannot be deleted at the finite level.  Sakai's endpoint condition
`e(L) → 0` as `L → -∞`, plus ultraweak closedness of the order relation, is exactly what must
remove it in the limit.  A theorem asserting `(r-s)e(s)≤u` for a general finite left endpoint
would silently assume the stronger condition `e(cut 0)=0` and would not be source-faithful.

## Assumption ledger for the finite results

| Property | Source status | Used by scratch | Intrinsic family | Resolution of `x` | Future PVM-derived | Derived |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| each `e(r)` is a projection | explicit: “system of projections” | yes | yes | no | yes | no |
| monotonicity | clause 1 | yes | yes | no | yes from `Iio` inclusion | no |
| one-sided sequential ultraweak continuity | clause 2 | no, finite only | yes | no | yes | `e(r)=sup_{s<r}e(s)` should follow |
| endpoint limits | clause 3 | no, residual retained | yes | no | yes | finite exact endpoints do **not** follow |
| self-adjoint `x` | theorem input | no | no | yes | no | no |
| ultraweak identity-moment representation | clause 4 | no | no | yes | supplied by future spectral integral | no |
| monotone finite division | source approximants | yes | no | no | no | division data |
| insertion `cut k=r` | implicit refinement in uniqueness proof | yes | no | no | compatible with any PVM | finite construction |
| exact finite endpoint values | not assumed by competing source family | no | no | no | only after separate localization | must not be added |
| norm convergence of moments | not assumed | no | no | no | no | must not be added |
| band projection/additivity/orthogonality | implicit finite calculus | proved | no | no | yes | yes from projection + monotonicity |
| `w=u-v`, `u,v≥0`, `uv=0`, `w⁺=u` | implicit in positive-part line | proved finitely | no | no | yes | yes |
| fixed-projection extraction | implicit in support line | proved finitely | no | becomes a limit consequence | yes | yes finitely |
| residual lower bound | implicit in support line | proved finitely | no | becomes a limit consequence | yes | yes finitely |
| support recovery | uniqueness conclusion | not proved in this lane | no | yes | compatible | expected derived theorem |

## What remains after the finite proof

The finite algebra closes without stronger hypotheses.  The remaining work is topological/order
work, not another finite identity:

1. choose a source-faithful directed family of finite divisions whose endpoints tend to both
   infinities and which contains the fixed cut `r` (and, for the lower bound, `s`);
2. show its moment sums tend ultraweakly to `x` and hence the translated sums tend to `r1-x`;
3. use fixed left/right multiplication to pass `e(r)w=u` to the limit;
4. retain positivity of `u` and `v` through ultraweak limits, then identify the limit's positive
   part without assuming positive-part continuity;
5. pass the residual lower bound to the limit while using `e(cut 0)→0`;
6. use clause 2 to identify `e(r)` with the supremum/limit of all `e(s)`, `s<r`;
7. apply the existing support criterion and compare with the canonical CFC-defined family.

The source proof therefore supports the planned architecture: projection-valuedness, monotonicity,
one-sided continuity, and endpoint limits are intrinsic; the moment representation relates the
family to `x`; support recovery and uniqueness are derived.  Nothing in this evidence justifies
publishing a lower-family structure or integral predicate yet.

## Validation boundary

The scratch file was checked with:

```text
lake build LeanOA.Mathlib.Analysis.CStarAlgebra.Projection
lake env lean Scratch/SakaiUniquenessFinite.lean
```

It contains no `sorry`, `admit`, or axioms.  It is intentionally outside `LeanOA.lean` and the
production build graph.
