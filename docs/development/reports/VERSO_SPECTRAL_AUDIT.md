# Verso spectral-frontier audit

## Scope and status

This audit covers `docs/SakAIDocs/Chapters/SpectralResolution.lean`, `Overview.lean`, and
`Library.lean` against the first-wave spectral-band and tagged-sum APIs. It does not alter public
Verso sources. The baseline graph has 98 active nodes and 162 statement edges.

At audit time, the seven `WStarAlgebra` spectral-band declarations are committed at HEAD
`c9e18f8`, while the refactor through the generic
`IsStarProjection.sub_mul_sub_eq_zero_of_le` is an uncommitted lead change.
`LeanOA/Ultraweak/TaggedSpectralSum.lean` and its twelve declarations are present and focused-build
clean but are not yet committed. The umbrella exports and public Verso edits are likewise
integration work in the shared tree. The documentation must not call the tagged work integrated
until these changes are committed together and the full build passes.

## Existing spectral-node audit

The chapter contains eleven pre-wave mathematical nodes. Their labels and linked declaration
counts are:

| Node | Existing Lean links | Result |
| --- | ---: | --- |
| `def:spectral_positive_part` | 4 | all elaborate |
| `def:lower_spectral_projection_Sak_1_11` | 7 | all elaborate |
| `prop:lower_spectral_projection_mono_Sak_1_11` | 1 | elaborates |
| `lem:lower_spectral_projection_continuity_Sak_1_11_1` | 2 | both elaborate |
| `prop:lower_spectral_projection_cut_recovery` | 5 | all elaborate |
| `lem:lower_spectral_projection_increment_bounds_Sak_1_11_2` | 2 | both elaborate |
| `prop:lower_spectral_projection_endpoints_Sak_1_11_3` | 4 | all elaborate |
| `def:finite_spectral_sums_Sak_1_11_3` | 5 | all elaborate |
| `prop:finite_spectral_sum_estimate_Sak_1_11_3` | 12 | all elaborate |
| `def:dyadic_spectral_divisions_Sak_1_11_3` | 10 | all elaborate |
| `prop:finite_spectral_sum_convergence_Sak_1_11_3` | 4 | all elaborate |

`SakAIDocs.Chapters.SpectralResolution` elaborated successfully during the audit, so all 56
existing links were rechecked by Verso. The later aggregate Blueprint target failed only because
the shared build tree changed concurrently and its freshly built `.olean` disappeared before
assembly; this is a build-directory race, not a declaration error. A stable-tree rerun is
required.

## New declaration audit

The exact proposed links all exist and were checked after importing
`LeanOA.Ultraweak.SpectralBand` and `LeanOA.Ultraweak.TaggedSpectralSum`:

- General projection fact: `IsStarProjection.sub_mul_sub_eq_zero_of_le`.
- Spectral bands: `WStarAlgebra.isStarProjection_spectralProjectionIio_sub`,
  `WStarAlgebra.commute_spectralProjectionIio_spectralProjectionIio`,
  `WStarAlgebra.commute_spectralProjectionIio_sub`,
  `WStarAlgebra.commute_spectralProjectionIio_sub_spectralProjectionIio`,
  `WStarAlgebra.commute_spectralProjectionIio_sub_spectralProjectionIio_sub`,
  `WStarAlgebra.spectralProjectionIio_sub_add_sub`, and
  `WStarAlgebra.spectralProjectionIio_sub_mul_spectralProjectionIio_sub_eq_zero`.
- Tagged sums: `WStarAlgebra.taggedSpectralSum`,
  `WStarAlgebra.taggedSpectralSum_eq_lowerSpectralSum`,
  `WStarAlgebra.taggedSpectralSum_eq_upperSpectralSum`,
  `WStarAlgebra.isSelfAdjoint_taggedSpectralSum`,
  `WStarAlgebra.lowerSpectralSum_le_taggedSpectralSum`,
  `WStarAlgebra.taggedSpectralSum_le_upperSpectralSum`,
  `WStarAlgebra.lowerSpectralSum_le_taggedSpectralSum_and_taggedSpectralSum_le_upperSpectralSum`,
  `WStarAlgebra.norm_taggedSpectralSum_sub_self_le_norm_upperSpectralSum_sub_lowerSpectralSum`,
  `WStarAlgebra.norm_taggedSpectralSum_sub_self_le`,
  `WStarAlgebra.tendsto_taggedSpectralSum`,
  `WStarAlgebra.tendsto_taggedSpectralSum_ultraweak`, and
  `WStarAlgebra.tendsto_taggedSpectralSum_dyadic`.

`lake build LeanOA.Ultraweak.SpectralBand LeanOA.Ultraweak.TaggedSpectralSum` succeeded (3072
jobs). A scratch `#check` file verified the original nineteen exact names and signatures; the two
endpoint-tag bridge declarations are definitional equalities and are linked from the tagged-sum
definition node. Integration then added the theorem-level ultraweak convergence corollary
recommended by the Mathlib audit; its signature is checked by the public Verso link and final
stable build.

## Recommended mathematical graph update

The smallest coherent graph presentation is the three-node split drafted by the lead, rather than
treating twenty public declarations as an undifferentiated addition to existing Sakai nodes:

1. `prop:spectral_band_calculus`, linked to the general orthogonality fact and all seven band
   declarations, with
   `uses := "prop:lower_spectral_projection_mono_Sak_1_11, prop:lower_spectral_projection_cut_recovery"`.
2. `def:tagged_spectral_sums`, linked to the tagged definition, both endpoint-tag bridge lemmas,
   self-adjointness, and three sandwich declarations, with
   `uses := "def:finite_spectral_sums_Sak_1_11_3, prop:spectral_band_calculus"`.
3. `prop:tagged_spectral_sum_convergence`, linked to the two error bounds and the three convergence
   declarations, with
   `uses := "def:tagged_spectral_sums, prop:finite_spectral_sum_estimate_Sak_1_11_3, def:dyadic_spectral_divisions_Sak_1_11_3"`.

These dependencies match the mathematical proofs. They add 3 nodes and 7 edges, so the expected
graph counts are 101 nodes and 169 statement edges. The generated manifest entry count should be
measured after the stable build rather than guessed. Final integration measured 471 manifest/cache
entries.

The drafted wording is faithful: it states projection, commutation, adjacent additivity,
ordered-band orthogonality, the tagged sandwich, the sharp gap/mesh error, filter-general
convergence, and dyadic convergence. It explicitly says that no operator-valued measure or
ultraweak Radon--Stieltjes integral has been defined. That caveat must remain: norm convergence of
tagged sums is stronger convergence of approximants, but it is not by itself a definition or
source-equivalence proof for Sakai's spectral integral.

Later source correction: Sakai's literal topology is strong `s(M,M_*)`, not ultraweak. The
ultraweak limit remains a valid consequence, and the caveat is stronger: neither the source
topology nor its undefined division semantics may be attributed to this theorem.

## Library path versus mathematical graph

The three mathematical assertions above belong in the graph because they form a genuine
algebraic/analytic bridge toward the integral checkpoint. The Library page should remain the
retrieval surface for theorem names and design boundaries: the general nonunital projection lemma,
the no-bundled-family decision, the principal band declarations, and the tagged-sum
estimate/convergence entry points. It should not gain a second theorem-status table.

All twenty new public declarations are covered either by the new graph nodes or by the Library
path. Both `Library.lean` and `SpectralResolution.lean` must directly import
`LeanOA.Ultraweak.SpectralBand` and `LeanOA.Ultraweak.TaggedSpectralSum` before their links are
checked; sibling chapter imports do not make names visible.

The Overview should add one completed-frontier bullet for arbitrary admissible tags and retain the
next frontier as documenting the LEVEL C source ambiguity and, separately, proving the canonical
strong-topology conclusion. Its statement that ordinary norm-valued vector-measure integration
does not automatically model the required interface is an important anti-overclaim.

## Typography audit

New prose correctly uses `$`C^*`$` and `$`W^*`$`. Because the final Overview paragraph was
substantially revised, `C-star foundations` there must become `$`C^*`$-algebra foundations` (now
corrected in the live diff). Untouched legacy `C-star`/`W-star` prose should remain untouched until
the planned systematic migration.

## Integration gates and validation

Before accepting the public update:

1. Export both new modules through `LeanOA.lean`.
2. Commit/integrate the generic projection helper, refactored spectral-band theorem, and tagged
   module.
3. Ensure direct chapter imports as above.
4. Run from the repository root:
   `lake build LeanOA.Ultraweak.SpectralBand LeanOA.Ultraweak.TaggedSpectralSum`, `lake build`, and
   `lake lint`.
5. Run from `docs/` on a stable build tree: `lake build SakAIDocs`, `lake exe vbp build`, and the
   three generated-file checks from the design contract.
6. Inspect the manifest for 101 active nodes, 169 edges, no unknown dependency references, and no
   missing external declarations; inspect graph, summary, search, and index.
7. Update `VERSO_STATUS.md` only with measured counts.

The earlier aggregate docs failure should not be accepted as final evidence either way; rerun after
concurrent source/build activity stops.

Final stable-tree validation satisfied the gates above. The focused and full Lean builds and
`lake lint` passed. `lake build SakAIDocs` and `lake exe vbp build` passed, while
`lake exe vbp check` reported `ok: true`, zero errors, 101 graph nodes, 169 statement edges, and 471
manifest/cache entries. Only the three recorded warnings from pinned upstream Verso/SubVerso code
were replayed.

## Design questions

IQ-003 is unaffected: no ideal representation changes occur. IQ-004 remains satisfied: Verso nodes
and `uses` edges are the theorem-status/dependency source, while this report records only audit and
integration guidance. IQ-001 remains open: the update must not imply that a set-indexed spectral
measure or Sakai's integral representation exists.
