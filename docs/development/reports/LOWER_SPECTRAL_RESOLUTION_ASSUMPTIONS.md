# Lower spectral-resolution assumption ledger

Status: **integration ledger; no structure or new public axiom is authorized by this report**

## Evidence boundary

This ledger consolidates three independent, kernel-checked experiments:

- canonical truncated-affine convergence, commit `18ddb9a`;
- arbitrary competing-family finite/CFC calculation, commit `de8e2bb`;
- CFC support-recovery and endpoint audit, commit `f5daad0`.

It separates four questions which must not be conflated:

1. what the canonical family already proves from its CFC/support construction;
2. what any monotone projection family proves at the finite algebraic level;
3. what follows by the stronger, non-source-faithful norm representation route;
4. what support recovery actually requires under Sakai's ultraweak hypotheses.

In the final column:

- **candidate intrinsic law** means the property could eventually be a field or clause of a small
  lower-family predicate, after architecture review;
- **candidate relation clause** means it concerns the relation between a family and `a`, but its
  exact source-faithful formulation is still RED;
- **no** means it is division data, CFC data, a theorem, or an assumption that must not be promoted;
- **defer** means the current proof evidence is insufficient to choose an axiom-level formulation.

## Consolidated ledger

| Property | Used where | CFC-native | Intrinsic family | PVM-derived | Resolution-of-a | Derived | Public axiom? |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- |
| `[canonical]` `a` is self-adjoint | all canonical CFC and band theorems in `18ddb9a` | predicate expected by real CFC | no | no | input operator | no | no; ordinary theorem input |
| `[canonical]` target `cfc (fun t : ℝ ↦ (r-t)⁺) a` | target of canonical finite estimate and convergence | **yes** | no | no | no | selected by Mathlib CFC | no |
| `[canonical]` `spectralPositivePart a r` equals that `cfc` value and `(r • 1-a)⁺` | target identification in `18ddb9a`; support audit in `f5daad0` | **yes**, via `cfc_comp`, affine CFC, and positive part | no | no | no | existing bridge theorem | no |
| `[canonical]` `spectralProjectionIio a r` is the support of the CFC cutoff | all canonical band estimates; exact support bridge in `f5daad0` | CFC supplies the cutoff, not support | canonical construction only | future spectral PVM should reproduce it | tied to canonical `a` | **yes**, existing definition/bridge | no new axiom |
| `[canonical]` tags lie in adjacent cut intervals | finite mesh estimate in `18ddb9a` | no | no | no | no | division admissibility | no |
| `[canonical]` adjacent cuts are ordered | inferred from in-band tags; used by every band theorem | no | no | no | no | division admissibility | no |
| `[canonical]` every band width is at most `δ` | sharp finite estimate in `18ddb9a` | no | no | no | no | mesh data | no |
| `[canonical]` `0 ≤ δ` in the partial-interval theorem | honest zero-band case in `norm_taggedSpectralSum_sub_mul_spectralProjectionIio_sub_le` | no | no | no | no | scalar side condition | no |
| `[canonical]` left cut is at most `-‖a‖` and right cut is greater than `‖a‖` | converts the canonical endpoint projection difference to `1` | no | no | no | uses localization already proved for canonical family | existing canonical endpoint theorems | no |
| `[canonical]` mesh tends to zero | filter-general norm convergence in `18ddb9a` | no | no | no | no | approximation-family data | no |
| `[canonical]` canonical band bound `qΔE ≤ aΔE ≤ sΔE` | partial estimate and cutoff-band sandwich | no | not an arbitrary-family law | would follow from a spectral measure resolving `a`, not from a bare PVM | **yes** | existing theorem for canonical family | no; must be derived for a competing family |
| `[canonical]` crossing-band split through `E(r)` | proves the cutoff estimate when `q ≤ r ≤ s` without inserting a cut | no | no | compatible with PVM band splitting | uses canonical resolution of `a` | **yes** from order/support API | no |
| `[canonical]` 1-Lipschitz scalar positive part | compares truncated endpoint gaps with ordinary spectral-sum gaps | **yes/scalar library** | no | no | no | library theorem | no |
| `[canonical]` norm convergence of truncated-affine sums | `tendsto_truncated_affine_taggedSpectralSum` | target remains CFC-native | no | no | canonical resolution already fixed | **yes** from sharp mesh estimate | no |
| `[canonical]` specified-ultraweak convergence | `tendsto_truncated_affine_taggedSpectralSum_ultraweak` | CFC construction remains norm-topological | no | no | no | norm limit composed with `continuous_toUltraweak` | no |
| `[arbitrary finite]` every `e(r)` is a star projection | makes ordered differences projections and makes finite pieces positive/orthogonal in `de8e2bb` | no | **yes** | **yes**, from projection-valuedness of `E(Iio r)` | no | encoded by scratch codomain | candidate intrinsic law, or inherited from future PVM view |
| `[arbitrary finite]` `Monotone e` | projection bands and pairwise orthogonality in `de8e2bb` | no | **yes** | **yes**, from `Iio r ⊆ Iio s` | no | no | candidate intrinsic law |
| `[arbitrary finite]` finite cut sequence is monotone | orders the sampled projection bands | no | no | no | no | division data | no |
| `[arbitrary finite]` sampled endpoints satisfy `e(cut 0)=0`, `e(cut n)=1` | telescopes the constant coefficient to `r • 1` | no | stronger than asymptotic endpoint laws | not from bare PVM axioms; follows from compact support only when known | may follow after localization relative to `a` | no in scratch theorem | **no in this exact finite form** |
| `[arbitrary finite]` tags are arbitrary real numbers | exact positive-part identity in `de8e2bb`; no cutoff alignment needed | no | no | no | no | finite sampling data | no |
| `[arbitrary finite]` bands are projections, nonnegative, and mutually orthogonal | positive/negative step decomposition | no | no | **yes** from nested/disjoint PVM sets | no | **yes** from projection-valuedness and monotonicity | no |
| `[arbitrary finite]` `(r-t)⁺` and `(t-r)⁺` are nonnegative, orthogonal coefficients | finite positive/negative decomposition | **yes/scalar order** | no | no | no | scalar theorem | no |
| `[arbitrary finite]` positive and negative operator sums are the CFC positive/negative parts | exact theorem `weightedSum_truncatedAffine_eq_posPart` | **yes**, `CFC.posPart_negPart_unique` | no | no | no | **yes** from finite orthogonal bands | no |
| `[arbitrary finite]` no cut equals `r` | stress test passed by exact finite positive-part identity | no | no | no | no | absence of an assumption | no |
| `[strong norm route]` exact finite endpoint normalization holds eventually | filtered theorem in `de8e2bb` | no | not supplied by Sakai's endpoint limits | only after a compact-support theorem | potentially tied to `a` | no | **no; non-source-faithful strengthening** |
| `[strong norm route]` identity-weighted step operators `Sₖ` converge to `a` in norm | transports the finite identity to the common target | no | no | a PVM spectral theorem may prove it for the canonical bounded measure | **yes** | no | defer; not a source-faithful relation clause as stated |
| `[strong norm route]` translated steps have a common compact real spectral bound | application of `Filter.Tendsto.cfc` | CFC continuity consumes it | no | no | no | **yes** from norm convergence and self-adjointness | no |
| `[strong norm route]` CFC is continuous in the operator argument on that bound | sends `(r • 1-Sₖ)` to `(r • 1-a)` under positive part | **yes**, pinned `Filter.Tendsto.cfc` | no | no | no | library theorem | no |
| `[strong norm route]` truncated sums converge to `spectralPositivePart a r` | `tendsto_weightedSum_truncatedAffine` | target is CFC-native | no | no | follows from the stronger norm representation | **yes** | no |
| `[strong norm route]` norm result passes to specified ultraweak topology | ultraweak corollary in `de8e2bb` | does not change CFC topology | no | no | no | `continuous_toUltraweak` | no |
| `[source]` `e(λ)` tends ultraweakly to `0` and `1` at the two infinities | Sakai resolution axiom; required to control expanding intervals | no | **yes**, as endpoint limits | **yes**, from continuity of a PVM on exhausting sets | no | no | candidate intrinsic law, with exact topology/convention reviewed |
| `[source]` identity moments represent `a` in the ultraweak topology | Sakai's abstract Radon--Stieltjes clause | no | no | future spectral-integral/CFC compatibility can supply it | **yes** | no | candidate relation clause; exact division-independent formulation remains RED |
| `[source]` representation is stable when an arbitrary cut `r` is inserted | needed to split the moment into below- and above-`r` pieces | no | no | natural for a genuine PVM integral | **yes** | should follow from the eventual integral/approximation API | **no as a separate axiom if derivable; otherwise defer** |
| `[support]` target `x_r = cfc (fun t ↦ (r-t)⁺) a` is nonnegative | support criterion in `f5daad0` | **yes** | no | no | no | CFC theorem | no |
| `[support]` `(e r).1 * x_r = x_r` | upper-support half of `support_eq_family_at_of_below` | no | no | not from a bare PVM | **yes** | expected consequence of representation/localization | **no; prove it** |
| `[support]` for every `s<r`, some `c>0` has `c • e(s) ≤ x_r` | lower-support half of `support_eq_family_at_of_below` | no | no | not from a bare PVM | **yes** | expected from truncated-affine lower bounds | **no; prove it** |
| `[support]` `IsLUB (e '' Iio r) (e r)` | exact endpoint recovery in `f5daad0` | no | **yes**, continuity from below | **yes**, from PVM continuity on increasing `Iio` sets | no | equivalent theorem-level form of the continuity law | candidate intrinsic law |
| `[support]` `support x_r = e r` | conclusion of `support_eq_family_at_of_below` | no | no | future PVM should satisfy via preceding facts | relates `e` to `a` | **yes** from upper support, lower bounds, and LUB | **no; this is the recovery theorem, not an axiom** |
| `[support]` canonical `support x_r = spectralProjectionIio a r` | identifies the same support on the canonical side | CFC supplies `x_r` | no | future canonical PVM compatibility should reproduce it | canonical relation | **yes**, definitionally checked in `f5daad0` | no |
| `[support]` strict half-line convention `e(r)=E(Iio r)` | atom and endpoint convention | no | convention of lower-family view | **yes** | no | forced by scalar-atom test | no field; governing definition/convention |
| `[support]` band convention is `Ico r s=[r,s)` | difference `e(s)-e(r)` | no | follows from strict half-lines | **yes**, set difference identity | no | derived | no |
| `[support]` fixed left/right multiplication is ultraweakly continuous | source-faithful passage from moment limits to compressed pieces | no | no | no | no | existing Sak-AI $W^*$-topology API | no |
| `[support]` positive cone is ultraweakly closed | retaining positivity in source-faithful limiting decomposition | no | no | no | no | existing $W^*$-order/topology theorem | no |
| `[support obstruction]` support is not norm-continuous at zero | rules out taking support through either norm or ultraweak convergence | no | no | no | no | kernel-checked counterexample in `f5daad0` | no |

## What the canonical theorem actually assumes

The production theorem from `18ddb9a` is already at the right canonical abstraction boundary. It
assumes only ordinary tagged-division data:

- tags lie in their bands;
- band widths are bounded by the mesh;
- the endpoint cuts contain the spectrum;
- the mesh tends to zero for the convergence theorem.

The cutoff `r` need not be a cut. Canonical projection-valuedness, monotonicity, endpoint
localization, support, band bounds, and the crossing-band split are theorems about
`spectralProjectionIio a`; none should be repeated as public axioms.

## What the arbitrary finite theorem actually assumes

The finite theorem from `de8e2bb` is independent of `a` and of any topology. It requires:

- projection-valuedness, encoded by the codomain of `e`;
- monotonicity of `e`;
- a monotone finite cut sequence;
- exact sampled endpoint values `0` and `1`.

It then derives every band fact and proves

```text
Σᵢ (r-tagᵢ)⁺ • Δeᵢ = (r • 1-Σᵢ tagᵢ • Δeᵢ)⁺
```

using Mathlib's positive/negative-part uniqueness. This is genuine PVM-compatible theorem-level
evidence. Exact endpoint normalization belongs to the chosen finite approximation, however, and
is not justified for Sakai's arbitrary competitor merely from its limits at infinity.

## Why the norm route is not the source route

Adding norm convergence of the identity sums to the arbitrary finite theorem yields a short and
fully CFC-native convergence proof: `Filter.Tendsto.cfc` transports the translated step operators
through positive part. This is mathematically correct and useful for a compactly supported PVM
whose norm approximation theorem is already known.

It is not a formalization of Sakai's uniqueness hypothesis. Sakai gives ultraweak representation
and asymptotic endpoints. In particular:

- ultraweak endpoint convergence does not give exact finite endpoint values;
- ultraweak moment convergence cannot be fed to norm-topological `Filter.Tendsto.cfc`;
- positive part is not asserted to be ultraweakly continuous.

Neither exact finite normalization nor norm moment convergence may enter a public
`IsSpectralResolutionOf e a` relation while claiming source equivalence.

## Minimum support-recovery package

The support audit `f5daad0` proves that convergence alone is insufficient, even in norm. For

```text
x_r = cfc (fun t : ℝ ↦ (r-t)⁺) a,
```

the topology-free recovery theorem needs exactly:

1. `0 ≤ x_r`, supplied by CFC;
2. `(e r).1 * x_r = x_r`, a resolution-of-`a` consequence;
3. for every `s<r`, a positive scalar lower bound `c • (e s).1 ≤ x_r`, another
   resolution-of-`a` consequence;
4. `IsLUB (e '' Iio r) (e r)`, the intrinsic continuity-from-below law.

Items 2 and 3 must be proved from source-faithful approximation/order information. Storing either
support equality or truncated-affine convergence to the desired CFC target as an axiom would make
the uniqueness proof circular. The LUB law is the exact reason the endpoint is `Iio`; the scalar
atom test rules out `Iic`.

## Public-interface decision from the combined evidence

No experimental structure is ready for publication.

The evidence supports the following eventual separation:

```text
intrinsic lower family
  projection-valuedness
  monotonicity
  continuity from below
  endpoint limits at ±∞

resolution of a
  source-faithful, division-independent ultraweak representation/compatibility
  from which upper-support and positive lower-bound theorems are derived
```

Mathlib CFC remains outside both layers and supplies the canonical continuous-function target.
A future PVM should induce the intrinsic layer by `e(r)=E(Iio r)`. Its spectral integral should
prove the resolution relation and agree with `cfc` on continuous functions. The finite algebra,
canonical estimate, and support-recovery criterion should then survive unchanged.

The next bounded theorem is not another structure definition. It is the fixed-projection
ultraweak decomposition: starting from Sakai's actual moment representation, retain enough order
information after inserting `r` to prove the upper-support identity and the strictly-below positive
lower bounds required by `support_eq_family_at_of_below`.
