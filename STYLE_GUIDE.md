# LeanOA implementation and proof guide

This document records the conventions visible in the repository as of 2026-08-24. It is intended
to guide further implementation of the blueprint while keeping the code both locally consistent
and suitable for eventual use in, or upstreaming to, Mathlib.

It is descriptive of the best current patterns, not a requirement to preserve every historical
choice. When this guide and current Mathlib practice differ, prefer current Mathlib practice unless
doing so would make the surrounding LeanOA API inconsistent.

## Repository map

- `blueprint/src/` is the source of the mathematical roadmap. Its `\uses`, `\lean`, `\leanok`, and
  `\mathlibok` annotations describe dependencies and formalization status. Treat the prose proof as
  mathematical guidance, not as a prescribed Lean proof architecture.
- `blueprint/print/`, `blueprint/web/`, and `blueprint/lean_decls` are generated artifacts. Change the
  sources and regenerate them rather than editing generated files directly.
- `LeanOA/Mathlib/` is the staging layer for generally reusable results and missing APIs. Its file
  hierarchy and declaration namespaces mirror the Mathlib locations where those results naturally
  belong.
- The other `LeanOA/` modules contain the operator-algebra and functional-analysis development.
  Major clusters are `Ultraweak`, `CStarAlgebra`, `CStarModule`, `Lp`, `TendstoZero`, and the locally
  convex/duality files.
- `LeanOA.lean` is the public umbrella import. A new public module must be reachable from it.
- `LeanOA/BlueprintImports.lean` contains imports needed for blueprint declaration checking; it is
  validation plumbing rather than the place for mathematical APIs.

At the time of the initial survey, the library had 58 Lean files and about 7,800 lines. The root
build and Mathlib-standard linter passed. The one `sorry` present during that survey has since been
removed. Do not add new `sorry`s.

## File and module conventions

New files should normally begin in the same shape as the existing module-system files:

```lean
module

public import Mathlib.Some.Narrow.Dependency
public import LeanOA.Some.Local.Dependency

@[expose] public section
```

Use public imports for dependencies that form part of the exported module. Keep imports as narrow as
is reasonably practical. Put scoped notation and frequently used namespaces near the top, followed
by grouped variables and named sections. Existing files commonly use:

```lean
open scoped ComplexOrder Ultraweak Topology
open Filter Set

variable {M P : Type*} ...

namespace Ultraweak
section SomeFeature
```

Prefer local scoping over global changes:

- `open ... in` and `open scoped ... in` for a declaration or small block;
- `variable (...) in` when parameters should be explicit on one declaration;
- `include ... in` and `omit ... in` to state dependency precisely;
- `set_option ... in` around only the declaration or proof that needs it.

In particular, do not set `backward.isDefEq.respectTransparency` globally merely because one
construction needs the compatibility mode. The repository consistently narrows this option to the
affected declaration where possible.

Substantial files should have a `/-! ... -/` module docstring with a short purpose statement and,
when useful, a list of main declarations. Public definitions, structures, classes, and non-obvious
theorems should have docstrings. Small API lemmas whose names and types are self-explanatory need not
be documented individually.

## API placement and naming

Place a declaration in the namespace of the principal object it describes. The repository favors
names such as:

- `Memℓp.holder`, `KreinSmulianProperty.translate`, and `DirectedOn.exists_isLUB` for properties;
- `lp.mapCLM`, `lp.holderL`, and `PositiveContinuousLinearMap.comp` for constructions;
- `lp.norm_holderL_le`, `..._apply`, `..._iff`, `..._eq`, and `..._mem` for theorems exposing an API.

Use Mathlib's snake-case theorem naming and standard suffix vocabulary. Names should describe the
mathematical interface, not the blueprint label, book theorem number, proof technique, or temporary
implementation. Source references belong in docstrings or comments.

General reusable facts should go in the corresponding `LeanOA/Mathlib/...` file and the namespace in
which Mathlib would place them. Domain-specific assembly belongs in the ordinary `LeanOA/...` tree.
Before adding a helper:

1. Search Mathlib and LeanOA for the fact and nearby APIs.
2. Decide whether the missing result is genuinely general.
3. If general, state it without LeanOA-specific types or excess hypotheses and put it in the mirrored
   Mathlib location.
4. If it is only proof scaffolding, keep it private or local to the domain module.

Use `_root_.` only when deliberately adding a declaration to a namespace while currently inside a
different namespace. Use `private` for implementation details that should not constrain later API
design. Avoid public `_aux` lemmas unless they are independently useful; the existing
`separationSeq_induction_step_aux` is a useful model of an exposed helper only because it isolates a
substantial mathematical step.

## Design principles visible in the code

### State the reusable theorem before bundling it

The clearest example is `LeanOA/Lp/Holder.lean`:

1. Prove raw `Memℓp` closure lemmas and finite-sum estimates.
2. Define the pointwise bundled map `lp.holder`.
3. Bundle it as a bilinear map `lp.holderₗ`.
4. Add continuity to obtain `lp.holderL`.
5. Prove the operator-norm bound `lp.norm_holderL_le`.
6. Build the specialized `lp.dualPairing` and its application and norm lemmas.

Follow this progression when a blueprint theorem needs new infrastructure:

```text
mathematical predicate/estimate
        -> unbundled operation
        -> algebraic bundled map
        -> continuous bundled map
        -> simp/application lemmas
        -> norm or order bounds
        -> specialized construction
```

Do not put the entire mathematical argument inside a bundled constructor if a useful unbundled lemma
can carry it.

### Prefer canonical structures and transfer maps

Use standard bundled maps (`LinearMap`, `ContinuousLinearMap`, `LinearEquiv`,
`ContinuousLinearEquiv`, `OrderHom`, positive maps, and so on) rather than bespoke functions plus
separate proof fields. Build a structure from an already bundled weaker structure when possible.

For type synonyms carrying another topology or norm, provide explicit canonical maps and their API.
`Ultraweak.toUltraweak`/`ofUltraweak`, `Ultraweak.linearEquiv`, and
`Ultraweak.weakDualCLE` are the main model. Establish coercion, inverse, algebraic, `@[simp]`, and
continuity lemmas early so later proofs can work at the appropriate abstraction level.

When a construction has a natural symmetric version, prove one orientation and derive the other via
`.symm`, `.flip`, `star`, or an equivalence. For example,
`Memℓp.of_bilin_of_top_right` and `Memℓp.holder_top_right_bound` are obtained from their left-hand
counterparts by flipping the bilinear map.

### Generalize along natural mathematical boundaries

The repository usually works over `RCLike` or a minimal normed-field/ring hierarchy until a genuinely
complex argument is needed. It also treats non-unital C-star algebras first where the proof does not
need a unit. Preserve that discipline, but do not accumulate typeclasses merely to make a theorem
look maximally general. Generality is valuable when it produces a recognizable reusable API.

Keep algebraic and topological assumptions separate and introduce stronger assumptions only in the
section or declaration that uses them. Use `Fact (1 ≤ p)` for the established `lp` APIs where that is
the surrounding convention.

### Optimize public design for downstream reuse

Design each public declaration by imagining its likely Mathlib consumers, including consumers later
in the blueprint, rather than merely finding a statement sufficient for the proof currently in
front of us. In particular:

- state a result at the strongest *natural* generality supported by its proof and mathematical
  meaning, while avoiding ornamental typeclass abstraction;
- separate reusable algebraic, order-theoretic, analytic, and topological components before
  specializing them to a W-star-algebra application;
- prefer APIs that expose canonical objects and composable bundled maps over one-off existential
  statements tailored to a single dependency edge;
- keep genuinely technical proof scaffolding private even when its statement can be generalized;
  being provable is not by itself a reason to enlarge the public API;
- derive symmetric and complementary cases through equivalences, `star`, `flip`, or an existing
  construction whenever that preserves the mathematical interface.

Scalar generality should follow the same rule. Weak duality, weak topologies, and general functional
analysis normally belong over `RCLike`. C-star-algebraic arguments remain over `ℂ` when the ambient
Mathlib structure or the mathematics is intrinsically complex; do not force an `RCLike` wrapper
around an argument that uses complex scalar multiplication essentially.

Treat reference proofs, including Sakai's, as fallback arguments rather than implementation
templates. Before formalizing one, look for a shorter proof or a more reusable statement through
the current Mathlib and LeanOA APIs, and compare the natural generality of the alternatives. Retain
the reference proof when it remains the clearest robust route, but do not inherit its auxiliary
constructions or level of generality merely because they suffice on paper.

For commutative reductions, first use Mathlib's continuous functional calculus at the level actually
needed by the argument. In particular, nonunital CFC and quasispectrum APIs can often transport
finite-spectrum, positivity, and approximation facts directly. The blueprint deliberately follows
this route and has no separate full nonunital Gelfand equivalence with `C₀(X)`. Add such a
representation theorem only if its equivalence data later becomes a genuine consumer requirement.

For uniqueness of specified preduals, first compare their explicitly represented closed subspaces
of the norm dual. Derive the equivalence of the preduals by composing their canonical isometric
identifications with that common image, and expose preservation of the original dual pairing as its
characterizing theorem. This keeps equality of representations, transport of data, and uniqueness
as separate reusable interfaces; it also prevents the proof from relying on definitional equality
between independently transported dual structures.

When two materially different public designs are both mathematically plausible—especially choices
about the principal object, maximal generality, instance ownership, or future enrichment—treat that
as a design checkpoint and ask for human judgment before committing the API. Routine proof and
implementation choices do not require such a pause.

### Treat definitional equality as an implementation detail

Constructors are often written with `where` blocks so their basic application lemmas can be proved
by `rfl`. That is a useful local optimization, not a public interface. Immediately expose the
intended behavior through named maps and `@[simp]`, `@[simps]`, `@[simps!]`, or `_apply` lemmas, and
make downstream proofs use those declarations. In particular:

- give type synonyms explicit forward maps, inverse maps, equivalences, inclusions, and coercion
  lemmas at the strongest natural bundled level;
- do not make clients unfold a synonym, topology, norm, or transported instance merely to cross a
  representation boundary;
- do not use accidental reducibility to make separately constructed structures interoperate;
- keep unavoidable `change`/`rfl` arguments that establish a bridge inside the bridge's
  implementation, then reason through the bridge thereafter;
- when many theorems depend on the compatibility of an existing structure with mathematical data,
  package that compatibility as a proposition-valued class. `LinearMap.IsWeak` is the model: it
  records that an ambient topology is induced by a pairing, provides transport across explicit
  equivalences, and lets downstream results depend on the class API instead of the topology's
  definition.

This is a global anti-definitional-equality-abuse rule, not merely advice for type synonyms. If two
structures, topologies, scalar actions, pairings, or transported instances must agree for a theorem
to make mathematical sense, represent that agreement explicitly. Use a named map or equivalence for
data, and use a proposition-valued compatibility class when the same coherence condition recurs
throughout an API. `LinearMap.IsWeak` is the preferred model: the class records the mathematical
compatibility, while explicit equivalences perform transport. Do not make instance search succeed
only because two independently meaningful constructions happen to reduce to the same term today.

An opaque or semantically meaningful type synonym should therefore be treated as opaque by client
code even if Lean can unfold it. Confine any `rfl`, `change`, transparency option, or reducibility
argument needed to establish its bridge lemmas; all later code should cross the boundary through
those named bridges. If this makes a downstream proof awkward, improve the bridge API or introduce
the appropriate compatibility class instead of unfolding the representation.

Add `@[ext]` when a new bundled function-like structure needs an extensionality principle. Use
automation attributes such as `@[fun_prop]` and carefully scoped `@[aesop]` rules only when they
express a stable API fact.

Do not add simp lemmas speculatively. A simp lemma should have a clear normal-form direction and should
make downstream expressions more canonical.

## Proof style

The dominant proof style is compact, structured tactic mode backed by strong library lemmas. The most
common tools are `simp`/`simpa`, `rw`, `have`, `exact`, `refine`, and `obtain`; specialized automation
such as `positivity`, `gcongr`, `grind`, `fun_prop`, `filter_upwards`, and `cfc_tac` is used where it
matches the mathematical domain.

Use the smallest proof form that remains readable:

- `rfl`, a direct term, or `simpa using ...` for wrappers and definitional facts;
- `by ext; simp` for pointwise equality of bundled maps;
- method/dot notation to emphasize that a theorem transforms an existing fact;
- `obtain` for existential data and explicit mathematical case splits;
- `calc` for chains of equalities and inequalities;
- `gcongr` and `positivity` for routine monotonicity and side conditions;
- `filter_upwards` for eventual statements rather than manually unpacking filters;
- `fun_prop` for continuity once the relevant API instances and lemmas exist;
- `cfc_tac` for routine continuous-functional-calculus side conditions.

In estimate proofs, expose the mathematical chain. A typical local pattern is:

```lean
calc
  complicatedTerm ≤ intermediateBound := by
    ...
  _ ≤ finalBound := by
    gcongr
```

Handle degenerate cases before the generic argument. `Memℓp.holder` first splits empty index types
and the `0`/`∞` exponent cases, then invokes the finite positive-exponent estimate. This keeps the
generic proof's hypotheses honest and avoids forcing edge cases through real-exponent algebra.

Use `simpa using` and `convert` to cross small representation boundaries. If a proof repeatedly fights
coercions, type synonyms, or bundled-map projections, pause and add the missing API lemma instead of
building a large brittle simplifier invocation.

Long proofs should contain comments describing the mathematical step about to be formalized. Good
examples occur in `Ultraweak/LUB.lean`, `Ultraweak/OrderClosed.lean`, and `KreinSmulian.lean`. Comments
should explain why the step works or why a reduction is chosen; they should not narrate obvious tactic
syntax. Short proofs are generally left uncommented.

Do not leave exploratory proof scaffolding as the final proof. A long sequence of local `have`
statements is appropriate only when those facts are the successive mathematical steps of a genuinely
one-off argument, as in the longer order/topology proofs already in the repository. If several local
facts describe a reusable construction, a recurring coercion calculation, a symmetric case, or a
recognizable theorem, extract and name them first; the final assembly theorem should then read as a
short composition of those lemmas. In particular, prefer a small family of reusable Peirce,
compactness, convergence, or norm lemmas to one monolithic proof containing all of those arguments
as anonymous local facts.

Proof golf is welcome after the statement and API are right. Prefer replacing duplicated arguments
with a reusable lemma, symmetry, a standard constructor, or a sharper abstraction. Do not golf away a
mathematically meaningful intermediate statement merely to reduce line count.

## Blueprint workflow

For each unfinished blueprint node:

1. Read its incoming `\uses` edges and the surrounding prose, then independently sanity-check the
   statement before designing its Lean API. In particular, do not confuse equality of topologies
   with equality of their continuous linear functionals, even after restricting to a bounded set;
   test topology claims against standard operator-algebra examples such as shift powers.
2. Search the current repository and Mathlib; blueprint metadata can lag behind the code, and one Lean
   declaration may cover several prose nodes.
3. Identify missing general infrastructure before formalizing the final theorem.
4. Design the intended public statement and namespace first. Check that it composes with existing
   order, topology, CFC, duality, and bundled-map APIs.
5. Prove small general lemmas in the Mathlib-staging layer, then assemble the domain theorem.
6. Add application, coercion, simp, extensionality, monotonicity, and norm lemmas needed by downstream
   nodes.
7. Update `\lean{...}` and `\leanok` only when the named declarations really establish the blueprint
   statement. Use `\mathlibok` only for declarations already in Mathlib.
8. Regenerate/check the blueprint outputs and declaration list through the project workflow.
9. Build and lint the whole project.

The blueprint currently mixes completed Mathlib facts and completed LeanOA declarations. The
W-star-subalgebra, projection-lattice, Stonean/real-rank-zero, strong/Mackey comparison, normality,
and predual-uniqueness branches have been formalized and linked to their public declarations. Treat
the dependency graph as a planning aid, then verify every dependency against actual Lean APIs and
the full validation workflow.

## Mathlib-facing quality bar

All code should respect the settings in `lakefile.toml`:

- `autoImplicit := false` and `relaxedAutoImplicit := false`;
- Mathlib's standard linter set;
- Mathlib's typeclass synthesis depth;
- the flexible-tactic linter;
- local compatibility workarounds rather than broad option changes.

Before considering a change complete:

```sh
lake build
lake lint
```

Also check the following manually:

- no new `sorry`, `admit`, accidental axioms, or unexplained high heartbeat limits;
- no unnecessary imports or duplicated Mathlib results;
- public declarations live in a natural namespace and have Mathlib-style names;
- definitions and important theorems have useful docstrings;
- assumptions are no stronger than the natural statement requires;
- helper results are private unless they form a coherent reusable API;
- symmetric cases reuse existing proofs;
- bundled constructions have application/coercion lemmas and quantitative bounds where appropriate;
- simp and automation attributes are intentional and terminating;
- local options and instances have the narrowest reasonable scope;
- the new module is exported through the appropriate imports and, if public, through `LeanOA.lean`;
- blueprint annotations match the declarations that actually prove the node.

## Existing rough edges are not conventions

Several source comments explicitly flag temporary compromises: a result that “should move,” a poorly
named lemma, missing `WeakBilin` API, and localized definitional-equality workarounds. These are
maintenance notes, not patterns to copy. New work should improve the abstraction boundary when it
encounters one of these areas, provided the change remains focused and preserves the public API or
includes a deliberate migration.

The target style is therefore: mathematically direct, compact after the right lemmas exist, explicit
about edge cases, rich enough in API to support the next blueprint node, and organized so reusable
pieces already look at home in Mathlib.
