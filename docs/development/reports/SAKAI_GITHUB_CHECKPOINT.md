# Sak-AI GitHub checkpoint

Date: 2026-09-02

## Repository state

- Branch: `master`.
- Starting HEAD: `8e745be2eaf6cbe14d779e2cf40e56d3f0336d38`.
- Starting `origin/master`: `0b096f308d0fecc60193c98f6b82ad8f35815250`.
- Outgoing range before this checkpoint: 69 commits, all coherent Sak-AI development.
- The worktree was clean at the start. This report and the corrected continuation counts form the
  single checkpoint commit.
- The immutable final HEAD, push range, and post-push `HEAD = origin/master` certificate belong in
  the transaction report because a commit cannot record its own object ID.

The outgoing audit found no dependency-pin, toolchain, manifest, remote, secret, credential,
machine-session, or generated-site damage. The committed `Scratch/` files are intentional checked
research artifacts with matching contracts and reports; none is imported by production Lean or
Verso.

## Sakai coverage

- Section 1.11: Lemma 1.11.1 is source-formalized in the intrinsic strong topology, and the
  production library contains the lower spectral-projection, spectral-band, tagged finite-sum,
  and truncated-affine CFC recovery APIs. Theorem 1.11.3 is **not source-formalized** because the
  source's abstract Radon--Stieltjes integral semantics remain LEVEL C ambiguous. Conditional
  scratch uniqueness results do not count as source coverage.
- Section 1.12: Theorem 1.12.1, including exact existence, support equations, algebraic
  uniqueness, and `ExistsUnique` packaging, is source-formalized.
- Section 1.13: bounded directed-positive normality, arbitrary orthogonal projection sums,
  projection-chain decomposition, complete additivity, and predual uniqueness are
  source-formalized.
- Section 1.14: functional support, norm orthogonality, orthogonal Jordan decomposition, and the
  general normal-functional polar decomposition through Theorem 1.14.4 are source-formalized.
- Section 1.15: Propositions 1.15.1 and 1.15.2 are source-formalized. Theorem 1.15.3 is
  statement-checked and prerequisite-mapped only. The arbitrary-index, basis-independent extended
  operator-energy layer is kernel-proved infrastructure, not a trace-class theorem.

## Current frontier

The active boundary is the permanent positive-trace/trace-class semantic core required by Sakai
Theorem 1.15.3. The next bounded transaction is to resolve escalation E3 by selecting either the
Hilbert--Schmidt-first design or the source-faithful predual-range hybrid. After that decision, the
first implementation transaction should define basis-independent positive trace and prove its
basic basis-invariance and positive-cone API before introducing the selected trace-class carrier.
No result should be labeled as Theorem 1.15.3 until the independent carrier, isometric
identification, and two-way positivity statement are all production theorems under the source
hypotheses.

## Stable architecture

- Mathlib continuous functional calculus remains canonical.
- Public source theorems use the ordinary `WStarAlgebra` context when a chosen predual is not part
  of the mathematical statement.
- Existing normality, support, polar-decomposition, coefficient-predual, and bounded-topology APIs
  remain the required reuse surfaces.
- Verso blocks, declaration links, and `uses` edges are the public mathematical status and
  dependency source of truth.
- Sak-AI adds no custom mathematical axioms or proof placeholders.

## Validation

- `lake build`: passed, 3,205 jobs.
- `lake lint`: passed.
- `lake exe mk_all --lib LeanOA --check`: passed with no update required.
- `cd docs && lake build SakAIDocs`: passed, 3,567 jobs.
- `cd docs && lake exe vbp build`: passed.
- `cd docs && lake exe vbp check`: `ok: true`, zero errors.
- `./scripts/build-verso-site.sh`: passed and regenerated the canonical site.
- Generated graph: 132 active nodes and 242 statement-dependency edges.
- Generated declaration/site data: 396 unique linked Lean declarations and 642 entries in both
  the manifest and HTML cache.
- Principal axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Production custom axioms, `sorry`, `admit`, tactic holes, and Scratch imports: zero.
- `git diff --check`: passed.
- The only documentation warnings are the three known pinned Verso/SubVerso warnings.

## GitHub synchronization

The authorized operation is one ordinary, non-force `git push origin master`; no tag or upstream
push is part of this checkpoint. The transaction is complete only after a fresh post-push check
certifies a clean worktree and equality of local `HEAD` with `origin/master`. The accompanying
end-of-run report records the actual Git output and immutable final object ID.
