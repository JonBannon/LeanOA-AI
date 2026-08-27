import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Design and contribution guide" =>

Sak-AI treats Mathlib and Jireh Loreaux's LeanOA as read-only design and reuse
references.  Before a substantial proof, development searches the current
local Mathlib checkout, current Mathlib master and relevant review history,
the current upstream LeanOA repository, and this repository.

# Decision rule

Routine generalization, naming cleanup, proof shortening, and replacement by
an established upstream declaration may proceed with normal review.  A change
to a foundational representation, canonical structure, instance strategy, or
public abstraction boundary is recorded as a design-review request before it
is propagated broadly.

# Generality

The target is useful generality, not maximum abstraction in isolation.
Assumptions should be removed when doing so produces a recognizable reusable
interface and does not obscure the operator-algebra application.  Book
statements do not determine API boundaries.

# Validation

The theorem package must pass `lake build` and `lake lint`.  The documentation
package must build its Lean library and generate a multi-page HTML site with a
Blueprint manifest.  Declaration references in this document are elaborated
against the local theorem package, so stale names fail the documentation
build.  `lake exe vbp check` validates the generated preview data.  CI then
combines the Verso root site with doc-gen4 API documentation under `/docs/`;
generated HTML is not a checked-in source of truth.
