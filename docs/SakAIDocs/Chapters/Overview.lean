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
  recovery theorem in Sakai 1.11.3.
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

The connected Section 1.11 targets completed so far are:

1. the scalar cutoff $`b_h(\lambda)=(\lambda 1-h)^+` is developed at the
   C-star-algebra level and shown norm-continuous in $`\lambda`;
2. the lower spectral projection
   $`e_h(\lambda)=s((\lambda 1-h)^+)` is defined without a retained predual;
3. the family $`e_h` is monotone;
4. an increasing directed net $`\lambda_i\to\lambda` gives
   $`e_h(\lambda_i)\to e_h(\lambda)` ultraweakly (Sakai 1.11.1);
5. the cutoff recovery identities give the two-sided spectral-band
   increment estimate (Sakai 1.11.2);
6. the sharp norm bounds give $`e_h(\lambda)=0` for
   $`\lambda\leq-\lVert h\rVert`, $`e_h(\lambda)=1` for
   $`\lVert h\rVert<\lambda`, and the ultraweak endpoint limits in
   Sakai 1.11.3;
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
    1.11.3.

The next bounded checkpoint inside Sakai 1.11.3 is now sharply isolated: give
the abstract ultraweak Radon--Stieltjes representation a division-independent
Lean meaning and prove that its refinement filter remains cofinal after any
prescribed cuts $`s<r` are inserted.  The kernel-checked finite calculation
retains the necessary left-endpoint residual, and the kernel-checked limit
argument then gives both support inequalities and uniqueness.  Those two
pieces are not yet a formalization of the source theorem until this
representation-to-approximants bridge is proved.  Ordinary norm-valued
vector-measure integration does not by itself model the required topology.

# Migration parity

The generated legacy graph contains 87 active mathematical nodes, all now
formalized and represented in this Verso document.  Its source contains one
additional label inside a fully commented-out proposal about recovering the
norm from states; because that proposal had neither an active graph node nor
a Lean declaration, it is recorded as future work rather than counted as a
completed theorem.

The lower-spectral-projection nodes are new work after that migration
baseline; they extend rather than replace the 87 historical nodes.

The dependency graph below therefore represents the whole completed Sak-AI
development through canonical truncated-affine recovery and the general
fixed-projection ultraweak decomposition used in Sakai 1.11.3, including
$`C^*`$-algebra foundations, operator
topologies, positive separation, Stonean spectra and real rank zero,
normality and predual uniqueness, Kaplansky density, projection lattices, and
support, central-support, and lower-spectral-projection theory.
