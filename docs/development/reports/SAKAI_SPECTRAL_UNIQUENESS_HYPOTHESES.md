# Sakai spectral-uniqueness hypothesis ledger

Status: **consolidated development ledger; no public lower-family, resolution, PVM, or integral
abstraction is authorized by this report**

> **Source correction (2026-08-30).** Direct visual comparison with Sakai's notation definitions
> shows that Theorem 1.11.3 uses Latin `s(M,M_*)`, the strong topology, not Greek
> `σ(M,M_*)`. Rows below distinguish the literal strong source hypotheses from the checked
> ultraweak consequence used by the conditional uniqueness proof.

## Evidence boundary

This ledger separates the hypotheses printed or used implicitly in Sakai, Theorem 1.11.3 from
the finite and limit theorems which have actually been checked in Lean.

- Source: Sakai, Section 1.11, Theorem 1.11.3, printed pages 26--27, PDF pages 38--39 of
  `/Users/jonbannon/Desktop/ClaudeMath/SakaiBook_1971.pdf`.
- Canonical CFC/truncated-affine production layer: integrated baseline `162271a`.
- Fixed-projection/order audit and production support bridge: worker `c637cb7`, integrated as
  `370486b`.
- Source reconstruction and finite cutoff algebra: scratch commit `6e349da`.
- Conditional support recovery and uniqueness: scratch commit `b25d751`.

The status words in **Actually used** have the following meanings:

- **SOURCE INPUT**: Sakai states the property or the uniqueness paragraph uses it as part of the
  abstract Radon--Stieltjes semantics.
- **FINITE CHECKED**: the projection/division calculation has a kernel-checked scratch theorem.
- **LIMIT CHECKED**: the ultraweak/order/support implication has a kernel-checked scratch theorem,
  conditional on explicit approximation data.
- **PRODUCTION**: the required stable Sak-AI/Mathlib API is already public.
- **MISSING BRIDGE**: the consequence has not been derived in Lean from Sakai's abstract
  Radon--Stieltjes representation clause.
- **FORBIDDEN STRENGTHENING**: the property is not in Sakai and must not be inserted to make the
  proof easier.

In the classification columns, “spectral PVM” means a PVM together with the theorem that it
resolves the particular self-adjoint element. A bare PVM supplies set/projection laws, but not a
moment representation of an operator.

## Consolidated ledger

| Property | Sakai source | Actually used | Intrinsic family | Resolution-of-a | PVM-derived | Derived | Existing Lean API |
| --- | --- | --- | ---: | ---: | ---: | ---: | --- |
| `M` is a W\*-algebra and `a=a*` | Theorem 1.11.3 opening, p. 26 | **SOURCE INPUT** for the represented operator and support | no | yes | no | no | Production `selfAdjoint M`, `WStarAlgebra M` |
| `e : ℝ →` star projections | “system of projections,” p. 26 | **SOURCE INPUT**; **FINITE CHECKED** | yes | no | yes, from projection-valuedness | no | Scratch codomain `ℝ → {p // IsStarProjection p}`; production star-projection subtype |
| `λ ≤ μ → e λ ≤ e μ` | Clause 1, p. 26 | **SOURCE INPUT**; **FINITE CHECKED** for every band/localization theorem | yes | no | yes, from `Iio λ ⊆ Iio μ` | no | Explicit `Monotone e`; finite scratch `isStarProjection_band` and multiplication lemmas |
| Sequential continuity from below | Clause 2, p. 26: increasing `λₙ→λ` gives strong `e(λₙ)→e(λ)` in `s(M,M_*)` | **SOURCE INPUT** for arbitrary resolutions; the exact public theorem now certifies the canonical family only, while the conditional competing-resolution proof still assumes this law | yes | no | yes, by PVM continuity from below | no | `tendsto_spectralProjectionIio_strong`; arbitrary-resolution bridge remains conditional |
| `IsLUB (e '' Iio r) (e r)` | Used as `e(r-0)=e(r)`, p. 27 | **LIMIT CHECKED** consequence of clause 2 | no; theorem form of continuity | no | yes | yes | Scratch `isLUB_image_Iio_of_tendsto_below`, `isLUB_image_Iio_of_monotone_of_continuousBelow` |
| `e(λ)→0` as `λ→-∞` | Clause 3, p. 26; topology not repeated in print | **SOURCE INPUT**; needed to remove the finite left residual | yes, after making topology explicit | no | yes, from exhausting empty lower half-lines | no | No competing-family production API; canonical `tendsto_spectralProjectionIio_atBot` only |
| `e(λ)→1` as `λ→+∞` | Clause 3, p. 26; topology not repeated in print | **SOURCE INPUT**; needed when translating the total moment to `r1-a` | yes, after making topology explicit | no | yes, from exhausting all of `ℝ` | no | No competing-family production API; canonical `tendsto_spectralProjectionIio_atTop` only |
| Endpoint-limit topology | Clause 3 is unqualified; the surrounding clauses 2 and 4 use `s(M,M_*)` | **SOURCE CLARIFICATION REQUIRED** for the unqualified display; strong is the coherent local reading | candidate intrinsic law | no | yes | no | No competing-family declaration; the checked ultraweak limit is only a consequence |
| `a = ∫ λ de(λ)` | Clause 4, pp. 26--27 | **SOURCE INPUT**; central relation to `a` | no | yes | only for a spectral PVM with compatibility | no | **MISSING BRIDGE**: no operator-valued Radon--Stieltjes semantics or stable relation predicate |
| The representation uses the `s(M,M_*)` topology | Text immediately following clause 4, p. 26 | **SOURCE INPUT** | no | yes | spectral-PVM integration theorem | no | Specified strong topology exists; the source integral semantics do not |
| Integral linearity gives `r1-a = ∫(r-λ)de(λ)` | First line of uniqueness paragraph, p. 27 | **SOURCE INPUT**, implicit integral law | no | yes | spectral-integral linearity | yes from a genuine integral | **MISSING BRIDGE**; support scratch instead assumes total translated-moment convergence |
| Arbitrary `r` may be inserted into/refine every division | Integral is split at arbitrary `λ₀`, p. 27 | **SOURCE INPUT**, implicit refinement invariance | no | yes | yes for simple-integral refinements | should be derived | Finite `insertCut`, `band_at_insertCut_add_succ`, `sum_band_insertCut`; cofinal/refinement theorem **missing** |
| A second arbitrary `s<r` may also be inserted | Implicit in proving support of the lower weighted integral | Needed for the positive lower bound; **FINITE CHECKED**, source-to-net bridge missing | no | yes | yes | should be derived | Finite `smul_band_le_belowTranslatedSum`; no RS/refinement bridge |
| Additivity splits the translated integral below and above `r` | Displayed split at `λ₀`, p. 27 | **SOURCE INPUT**; **FINITE CHECKED** algebraically | no | yes | yes from measure/integral additivity | yes | Scratch `translatedMomentSum_eq_below_sub_above`; integral-level theorem **missing** |
| Integral of `1` over a lower interval is its projection increment | Final support line `∫_{-∞}^{r-0}de'=e'(r-0)`, p. 27 | **SOURCE INPUT**, implicit constant-integral law | no | yes | yes from PVM integration | yes | Finite `Finset.sum_range_sub`/band telescoping; infinite/source bridge **missing** |
| Positivity/order preservation for nonnegative scalar integrands | Used when the below and above pieces are treated as positive, p. 27 | **SOURCE INPUT**, implicit integral law; **FINITE CHECKED** | no | yes | yes | yes | Finite `belowTranslatedSum_nonneg`, `aboveTranslatedMagnitude_nonneg`; limit positivity via order closure |
| Lower-family convention is `e(r)=E(Iio r)` | Final `r-0` line, p. 27 | **SOURCE INPUT** and endpoint sanity check | convention of the lower-family view | no | yes | no | Production name `spectralProjectionIio`; scratch `singleAtomLowerFamily_at` |
| Band convention is `e(s)-e(q)=E(Ico q s)` | Difference of strict lower half-lines | **FINITE CHECKED** | no | no | yes | yes | Scratch `band`; production canonical band differences |
| An atom at `r` is excluded from `e(r)` | `e'(r-0)=e'(r)`, p. 27 | **SOURCE INPUT**; **FINITE CHECKED** by one-atom test | consequence of convention | no | yes | yes | Scratch `singleAtomLowerFamily_at`, `band_singleAtom_at_of_lt`, `band_singleAtom_to_atom_of_le` |
| An atom at `r` belongs to `[r,s)`, not `[q,r)` | Same strict-left convention | **FINITE CHECKED** | no | no | yes | yes | Same one-atom scratch theorems |
| Ordered band `e(s)-e(q)` is a projection | Implicit finite Stieltjes calculus | **FINITE CHECKED** | no | no | yes | yes from projection-valuedness + monotonicity | `isStarProjection_band` at `6e349da`; canonical production analogue exists |
| Insertion splits `[q,s)` into `[q,r)+[r,s)` | Implicit in the integral split | **FINITE CHECKED** | no | no | yes | yes | `band_add_band`, `band_at_insertCut_add_succ` |
| Inserted bands are orthogonal | Implicit in positive/negative decomposition | **FINITE CHECKED** | no | no | yes | yes | `lower_band_mul_upper_band_eq_zero` and reverse |
| `e(r)` fixes every below-cut band on both sides | Implicit localization of the lower integral | **FINITE CHECKED** | no | no | yes | yes | `mul_band_eq_self_of_le`, `band_mul_eq_self_of_le` |
| `e(r)` kills every at/above-cut band on both sides | Implicit localization of the upper integral | **FINITE CHECKED** | no | no | yes | yes | `mul_band_eq_zero_of_le`, `band_mul_eq_zero_of_le` |
| Multiplication by `e(r)` extracts `[q,r)` from a crossing band | Needed before or instead of inserting the cut | **FINITE CHECKED** | no | no | yes | yes | `mul_band_eq_lower_band`, `band_mul_eq_lower_band` |
| A finite division is monotone | Sakai's division on pp. 26--27 is strictly increasing | **FINITE INPUT** | no | no | no | division data | Scratch uses a monotone extension `cut : ℕ→ℝ`; only finite prefixes are read |
| Total translated left sum decomposes as `w=u-v` | Finite form of the displayed integral split | **FINITE CHECKED** | no | no | yes | yes | `translatedMomentSum_eq_below_sub_above` |
| `u≥0` and `v≥0` | Implicit before identifying positive/negative parts | **FINITE CHECKED** | no | no | yes | yes | `belowTranslatedSum_nonneg`, `aboveTranslatedMagnitude_nonneg` |
| `e(r)u=u=ue(r)` | Implicit localization below `r` | **FINITE CHECKED** | no | no | yes | yes | `mul_belowTranslatedSum_eq_self`, `belowTranslatedSum_mul_eq_self` |
| `e(r)v=0=ve(r)` | Implicit orthogonality above `r` | **FINITE CHECKED** | no | no | yes | yes | `mul_aboveTranslatedMagnitude_eq_zero`, `aboveTranslatedMagnitude_mul_eq_zero` |
| `uv=0` | Needed to identify the positive and negative parts | **FINITE CHECKED** | no | no | yes | yes | `belowTranslatedSum_mul_aboveTranslatedMagnitude_eq_zero` |
| `w⁺=u` and `w⁻=v` | Sakai states the positive-part equality, p. 27 | **FINITE CHECKED** for `w⁺=u`; negative equality follows through the reused uniqueness theorem | no | no | yes | yes | `posPart_translatedMomentSum_eq_below`; Mathlib `CFC.posPart_negPart_unique` |
| `e(r)w=u=we(r)` | Finite fixed-projection extraction | **FINITE CHECKED** | no | no | yes | yes | `mul_translatedMomentSum_eq_below`, `translatedMomentSum_mul_eq_below` |
| Finite lower bound retains `(r-s)(e(s)-e(left))` | Implicit support argument below `s<r` | **FINITE CHECKED** and indispensable | no | no | yes | yes | `smul_band_le_belowTranslatedSum` |
| Expanded residual `(r-s)e(s)-(r-s)e(left)≤u` | Same source step before `left→-∞` | **FINITE CHECKED** | no | no | yes | yes | `smul_projection_sub_residual_le_belowTranslatedSum` |
| Exact finite `e(left)=0`, `e(right)=1` | **Not** assumed for the competitor | **FORBIDDEN STRENGTHENING** | no | no | not from bare PVM/end limits | no | Deliberately absent from both finite and support scratch interfaces |
| Norm convergence of competing moment sums | **Not** in Sakai; representation is strong-topological | **FORBIDDEN STRENGTHENING** | no | no | not automatic | no | Deliberately absent; Mathlib norm-CFC continuity is not used |
| A chosen inserted-cut total net satisfies `uᵢ-vᵢ→r1-a` ultraweakly | Intended finite meaning of representation plus endpoints | **MISSING BRIDGE** from clause 4; explicit hypothesis in support scratch | no | yes | spectral-PVM simple-integration theorem | should be derived | Hypothesis `hmoment` in `tendsto_split_of_fixedProjection_moment` and support theorems |
| The approximation filter is nontrivial | Needed for uniqueness/order of limits | Technical **LIMIT INPUT** | no | no | no | approximation data | `[NeBot l]` in support scratch; standard Mathlib requirement |
| Fixed left/right/two-sided multiplication preserves ultraweak limits | Used to extract below/above limits | **PRODUCTION** and **LIMIT CHECKED** | no | no | no | general topology | `Ultraweak.mulLeftL`, `mulRightL`, separate multiplication continuity; audit `c637cb7` |
| Eventual equalities may replace approximants | Used with finite localization identities | **PRODUCTION** | no | no | no | general filter theory | `Filter.Tendsto.congr'` |
| Eventual inequalities pass to ultraweak limits | Used for positivity and lower estimates | **PRODUCTION** and **LIMIT CHECKED** | no | no | no | general order topology | Production `OrderClosedTopology` for `σ(M,P)`; scratch `le_of_tendsto_of_tendsto_ultraweak` |
| Total moment convergence forces separate `uᵢ` and `vᵢ` limits | Not an extra source axiom | **LIMIT CHECKED** | no | no | no | yes | `tendsto_split_of_fixedProjection_moment`: limits are `e(r)y` and `e(r)y-y` |
| Limit decomposition is the positive/negative-part decomposition | Sakai's “Hence” line, p. 27 | **LIMIT CHECKED**, conditional on `hmoment` and finite sign/localization facts | no | no | compatible | yes | `posPart_negPart_eq_of_fixedProjection_moment`; Mathlib `CFC.posPart_negPart_unique` |
| `e(r)` fixes `(r1-a)⁺` | First support inequality mechanism | **LIMIT CHECKED** | no | no | compatible | yes | `fixedProjection_mul_posPart_of_moment` |
| `support ((r1-a)⁺) ≤ e(r)` | First half of support recovery | **LIMIT CHECKED** | no | no | compatible | yes | `support_spectralPositivePart_le_of_fixedProjection_moment`; production `WStarAlgebra.support_le_iff` |
| `(r-s)(e(s)-e(leftᵢ)) → (r-s)e(s)` | Uses `e(leftᵢ)→0` from clause 3 | **LIMIT CHECKED** once the endpoint net is supplied; selecting it from RS divisions is part of the missing bridge | no | yes | yes | yes | `tendsto_real_smul_sub_of_tendsto_zero` |
| `(r-s)e(s)≤(r1-a)⁺` for every `s<r` | Implicit support-of-weighted-integral step | **LIMIT CHECKED**, conditional on varying lower nets | no | no | compatible | yes | Order limit inside `competing_le_support_spectralPositivePart_of_fixedProjection_moment` |
| `e(s)≤support ((r1-a)⁺)` for every `s<r` | Same step, using `r-s>0` | **LIMIT CHECKED** | no | no | compatible | yes | `competing_le_support_spectralPositivePart_of_fixedProjection_moment`, `isStarProjection_le_support_of_smul_le` |
| `support ((r1-a)⁺)=e(r)` | Final support line, p. 27 | **LIMIT CHECKED**, conditional on explicit approximation hypotheses and continuity below | no | no | compatible | yes | `support_spectralPositivePart_eq_of_fixedProjection_moment` |
| The common element is Mathlib CFC `cfc (λ↦(r-λ)⁺) a` | Modern canonical interpretation of Sakai's `(r1-a)⁺` | **PRODUCTION**; common target, never an integral axiom | no | no | continuous-function compatibility for spectral PVM | yes | `CStarAlgebra.spectralPositivePart_eq_cfc`, `spectralPositivePart_eq_posPart` |
| Canonical support is `spectralProjectionIio a r` | Definition of Sak-AI canonical family | **PRODUCTION** | no | canonical construction | future spectral PVM should reproduce it | yes | `WStarAlgebra.spectralProjectionIio` and support bridge |
| `e(r)=spectralProjectionIio a r` | Sakai uniqueness at one cut | **LIMIT CHECKED**, conditional on explicit approximation data; **not yet source theorem** | no | no | compatible | yes | `competing_eq_spectralProjectionIio_of_fixedProjection_moment`, `_of_continuousBelow` |
| Pointwise recovery implies equality of families | Last sentence “Such a resolution is unique” | **LIMIT CHECKED** once recovery is available at every cut | no | no | compatible | yes | `competing_family_unique_of_pointwise_recovery` |
| Support is continuous under norm or ultraweak convergence | Not used by Sakai and false in the required generality | **FORBIDDEN** | no | no | no | no | No API; prior scratch counterexample rules out this route |
| A public `LowerSpectralFamily` or `IsSpectralResolutionOf` structure | Not a source object with fixed Lean semantics | **NOT USED / DEFERRED** | undecided | undecided | future view/compatibility | no | No declaration; explicit terms and hypotheses only |

## Exact closed portion

The following implication chain is now kernel-checked, but remains scratch where indicated:

```text
explicit monotone projection family + finite divisions containing r and s
  -> finite bands, positivity, orthogonality, and w = u-v
  -> e(r)u=u, e(r)v=0, w⁺=u
  -> residual lower bound (r-s)(e(s)-e(left)) ≤ u

explicit ultraweak total-moment limit + those eventual finite facts
  -> separate limits of u and v by fixed multiplication
  -> positive/negative-part identification without positive-part continuity
  -> support ≤ e(r)

left endpoint tends to zero + residual inequality
  -> (r-s)e(s) ≤ (r1-a)⁺
  -> e(s) ≤ support for every s<r

sequential continuity from below
  -> IsLUB (e '' Iio r) (e r)
  -> support = e(r)
  -> e(r) = spectralProjectionIio a r
  -> pointwise/family uniqueness.
```

Every arrow after the explicit total-moment and lower-net hypotheses has a kernel-checked theorem
in `b25d751`. The general fixed-multiplication, order-closedness, CFC, and support leastness
interfaces are already production mathematics. The finite arrows have kernel-checked theorems in
`6e349da`.

## Exact open bridge

Sakai's abstract formula

```text
a = ∫ λ de(λ)  in the s(M,M_*) topology
```

has not yet been given a Lean semantics. Consequently, Sak-AI has not proved from clause 4 that
there is one directed/cofinal family of finite divisions which:

1. has endpoints tending to `-∞` and `+∞`;
2. represents `a` by identity-weighted sums strongly, hence by the same sums ultraweakly;
3. remains cofinal and has the same limit after inserting any fixed `r` and `s<r`;
4. yields translated sums `uᵢ-vᵢ→r1-a` despite nonexact finite endpoint projections;
5. supplies the varying residual nets
   `(r-s)(e(s)-e(leftᵢ))→(r-s)e(s)`.

The finite and limit lanes prove that these are sufficient and that no further CFC or support
obstruction remains. They do **not** prove that a single arbitrarily chosen moment net has the
required refinement invariance. Until the five items above are formalized, the conditional
pointwise theorem must not be labeled the fully formalized uniqueness clause of Sakai 1.11.3.

## API decision

No public spectral-resolution abstraction is introduced. The source representation still lacks a
stable Lean meaning, so bundling it now would hide the only remaining semantic choice. Mathlib CFC
remains the sole continuous functional calculus, and the common support target remains
`CStarAlgebra.spectralPositivePart`/`WStarAlgebra.spectralProjectionIio`.

A future PVM can enter below this theorem stack:

```text
PVM E
  -> e(r)=E(Iio r)
  -> intrinsic projection/monotonicity/continuity/endpoint laws
  -> simple-integral refinement and spectral representation of a
  -> discharge the explicit finite and limit hypotheses above
  -> reuse support recovery and uniqueness unchanged.
```

The natural next bounded target is therefore the division-independent Radon--Stieltjes/refinement
bridge, not another support lemma and not a public structure declaration.
