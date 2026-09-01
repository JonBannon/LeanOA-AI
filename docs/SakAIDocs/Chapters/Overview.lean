import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Project overview" =>

Sak-AI has two complementary reading paths.

* The *mathematical path* follows Sakai.  The current formal development
  completes Section 1.10 and constructs the lower spectral family through
  norm convergence of its finite sums and the canonical truncated-affine
  recovery theorem in Sakai 1.11.3.  It also completes the element polar
  decomposition of Theorem 1.12.1 and the source normality characterization
  of Theorem 1.13.2, together with arbitrary orthogonal projection sums and
  the complete-additivity characterization in Definition 1.13.4.  This
  completes Section 1.13.
* The *library path* follows reusable Lean concepts: weak topologies and
  preduals, ultraweak continuity, closed ideals, projection lattices, and
  support constructions.  Names and assumptions are chosen for Mathlib
  portability rather than to mirror book numbering.

This Verso document is the sole mathematical-documentation source.  All
active legacy nodes, proof sketches, declaration links, and dependency edges
moved here before the old LeanBlueprint machinery was retired.  Git history
preserves that migration baseline.

The deployed site is accompanied by the
[Lean API documentation](https://jonbannon.github.io/Sak-AI/docs/) and the
[upstreaming dashboard](https://jonbannon.github.io/Sak-AI/upstreaming.html).

# Current frontier
%%%
tag := "current-frontier"
%%%

The connected frontier targets completed so far are:

1. the scalar cutoff $`b_h(\lambda)=(\lambda 1-h)^+` is developed at the
   C-star-algebra level and shown norm-continuous in $`\lambda`;
2. the lower spectral projection
   $`e_h(\lambda)=s((\lambda 1-h)^+)` is defined without a retained predual;
3. the family $`e_h` is monotone;
4. whenever $`\lambda_n\leq\lambda` for every $`n` and
   $`\lambda_n\to\lambda`, the projections
   $`e_h(\lambda_n)` converge to $`e_h(\lambda)` in the intrinsic strong
   topology $`s(M,M_*)`, with no monotonicity assumption.  This is the exact
   statement of Sakai 1.11.1; a filter-general left-continuity theorem and a
   reusable strong-convergence theorem for directed projection suprema are
   also available;
5. the cutoff recovery identities give the two-sided spectral-band
   increment estimate (Sakai 1.11.2);
6. the sharp norm bounds give $`e_h(\lambda)=0` for
   $`\lambda\leq-\lVert h\rVert`, $`e_h(\lambda)=1` for
   $`\lVert h\rVert<\lambda`.  These eventual equalities imply the endpoint
   limits in every topology, including Sakai's $`s(M,M_*)` topology;
7. lower and upper finite spectral sums bracket $`h`, while their order and
   norm gaps are controlled by the partition mesh, as in the existence proof
   of Sakai 1.11.3;
8. for any filtered family of spectral divisions whose mesh tends to zero,
   both finite sums converge in norm to $`h`; in particular this holds for
   an explicit nested sequence of uniform dyadic divisions;
9. arbitrary tags chosen inside those spectral bands give self-adjoint sums
   between the lower and upper sums, with the same mesh error bound and norm
   convergence;
10. weighting those tags by $`x\mapsto(r-x)^+` gives a sharp mesh
    approximation to
    $`b_h(r)=\operatorname{cfc}_h(x\mapsto(r-x)^+)`, in norm and in every
    specified ultraweak topology, without requiring $`r` to be a partition
    cut.
11. a fixed projection which extracts the positive finite piece from an
    ultraweakly convergent difference forces the two pieces to converge to
    the Mathlib positive and negative parts of the limit; this supplies the
    analytic decomposition used in the uniqueness paragraph of Sakai
    1.11.3;
12. every element $`a` of a $`W^*`-algebra has a unique polar factor $`u`
    satisfying $`a=u|a|`, $`u^*u=s(|a|)`, and
    $`uu^*=s(|a^*|)`, completing Sakai 1.12.1;
13. Sakai's uniformly bounded directed-positive definition of a normal
    functional is equivalent to the established projection-normality
    predicate, full Scott continuity, and membership in every specified
    ultraweak continuous dual.  This completes the exact printed statement
    of Theorem 1.13.2;
14. for an arbitrary pairwise orthogonal projection family, all finite
    partial sums are projections, their least upper bound is the canonical
    projection supremum, and the finite-subset net converges to it both
    ultraweakly and strongly, giving the geometric content of Sakai 1.13.4;
15. a positive functional is normal exactly when it is completely additive
    on every arbitrary pairwise orthogonal projection family.  The scalar
    sum is the finite-subset-net `HasSum`, with no countability assumption.
    The converse uses a maximal orthogonal decomposition of each projection
    chain, whose finite partial sums are dominated inside the chain and whose
    supremum recovers the chain least upper bound.

The source audit found an important correction and a genuine ambiguity.
Sakai prints the strong $`s(M,M_*)` topology, not the ultraweak
$`\sigma(M,M_*)` topology, in both the continuity and abstract
Radon--Stieltjes clauses.  The book does not define the integral's directed
division, tag, refinement, or improper-endpoint semantics, and period sources
use materially different meanings.  Sak-AI therefore does not claim that
Theorem 1.11.3 is source-formalized.  In scratch, convergence of the same
finite-cut net in $`s(M,M_*)` is kernel-checked to imply the ultraweak
hypotheses of the complete conditional uniqueness argument.  This preserves
the useful modern analogue without asserting that its refinement-plus-mesh
filter is Sakai's undefined integral.

Section 1.12 is complete.  Its proof uses Mathlib's
continuous-functional-calculus absolute value, the existing support API, and
ultraweak compactness of the closed unit ball; it does not depend on the
unresolved integral semantics.  Section 1.13 is also complete: Definitions
1.13.1, 1.13.4, and 1.13.5, Theorem 1.13.2, and Corollary 1.13.3 are all
represented with their arbitrary directed-set or arbitrary-family
quantifiers.  The current bounded checkpoint is Section 1.14.2: construct the
support of a normal positive functional from its null left ideal, prove the
greatest-zero-projection and cutdown identities, and recover faithfulness on
the support corner before attempting the later Jordan and functional polar
decompositions.

# Migration parity

The generated legacy graph contains 87 active mathematical nodes, all now
formalized and represented in this Verso document.  Its source contains one
additional label inside a fully commented-out proposal about recovering the
norm from states; because that proposal had neither an active graph node nor
a Lean declaration, it is recorded as future work rather than counted as a
completed theorem.

The lower-spectral-projection, element-polar-decomposition, source-normality,
arbitrary orthogonal-sum, and complete-additivity nodes are new work after that migration baseline;
they extend rather than replace the 87 historical nodes.

The dependency graph below therefore represents the whole completed Sak-AI
development through canonical truncated-affine recovery, the general
fixed-projection ultraweak decomposition used in Sakai 1.11.3, and the
element polar decomposition of Sakai 1.12.1, the exact normality theorem of
Sakai 1.13.2, arbitrary orthogonal projection sums, and the complete-additivity
characterization closing Sakai 1.13, together with $`C^*`-algebra foundations, operator
topologies, positive separation, Stonean spectra and real rank zero,
normality and predual uniqueness, Kaplansky density, projection lattices, and
support, central-support, and lower-spectral-projection theory.
