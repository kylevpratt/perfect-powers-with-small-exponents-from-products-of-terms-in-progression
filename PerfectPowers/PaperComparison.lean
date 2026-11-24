module

/-!
# Comparison with the paper (reviewed 2026-11-19)

This is a guide to the mathematical statements and the substantive proof
changes in the formalization. Numbering refers to the paper draft identified
in `README.md`. This comment is documentation, not another mathematical
input. `PerfectPowers.mainResults_of_external_inputs` is the final entry
point; `PerfectPowers.Audit` checks its proof dependencies.

## Main statements and the agreed scope

`Theorem12At`, `Theorem14At`, and `Theorem15At` in `Main.Statements` encode
Theorems 1.2, 1.4, and 1.5, respectively. In particular, the three endpoint
ranges in (1.4), the density losses `1/5` and `1/(log k)^3`, the bound
`3 * (log k)^(3/2)`, and the two signed square cases in Theorem 1.2 are
retained. The exponent is arbitrary, not assumed prime. Positive integral
`d` is represented by a natural number with `0 < d`; nonzero signed
`n`, `b`, and `y` remain integers. `Smooth k z` includes `z != 0`.

`SmallExponent` uses `ell^5 <= log (log k)` in place of the fifth root.
`PerfectPowers.smallExponent_iff_paper_range` proves the equivalence
on the relevant domain. The additional requirement `3 <= k` is harmless
because `MainResults` supplies an absolute threshold at least three.
Every eventual main assertion quantifies over the exponent *after* the
eventual quantifier on `k`; the threshold is uniform in the allowed exponent.

The paper asserts effective computability of its threshold. Within the
project scope, `MainResults` asserts existence of one absolute `k_0`
only. Neither effectivity nor a proof of the genus lower bound is a project
goal. The following four statements are explicit theorem hypotheses:
affine Faltings, the superelliptic genus lower bound, Remond, and prime-AP.
They are proposition definitions, not globally declared mathematical axioms.

## Lemmas 3.1--3.3 and Theorem 1.5

`Arithmetic.Decomposition` follows Lemma 3.1, using positive natural `x_i`
and putting the sign into the integer `a_i`, as allowed by the draft's sign
convention. `Arithmetic.Deletion` and `Arithmetic.GoodIndices` strengthen
Lemma 3.2: the retained absolute product divides `(k-1)!`, rather than merely
being at most `k!`. The deletion lemma also permits an empty retained set;
the main applications prove the needed cardinality bounds separately.

`External.PrimeAP` is the uniform error estimate of Lemma 3.3, with its
constant depending only on `A`. Its existence is retained without an
effectivity claim. `Main.StepRestriction` uses `A = 5`. The deduction of
Theorem 1.5 from Proposition 3.5, including the subsequent smoothness
bootstrap and the step restriction, follows the paper's structure.

## Theorems 1.4 and 1.2; Lemma 3.6

`Main.FullClassification` uses the eventual prime interval `(x, 5*x/4]`
from `Analytic.ShortPrimeIntervals`, rather than the paper's particular
prime-counting error estimates in the proof of Theorem 1.4. This consequence
of mathlib's proved ordinary PNT is sufficient for the same exact endpoint
ranges and adds no external hypothesis.

For the step-one square obstruction in the proof of Theorem 1.2,
`Main.StepOneObstruction` first uses the admissible-pair classification and
Bertrand to reduce the positive start to `1 <= a <= k`; it then applies the
restricted elementary result in `Squares.Consecutive` (and reflection for
negative terms). The draft instead invokes Erdos--Selfridge. No unrestricted
consecutive-perfect-power theorem is asserted or needed here.

For Lemma 3.6 the draft cites Saradha for lengths at least three and handles
length two separately. `Squares.OddNonsquare` supplies an elementary proof
for every length at least two. Short starts use Bertrand. Long starts use
odd-prime maximal-valuation deletion, an odd-factorial estimate from
Legendre's binary formula, and elementary Chebyshev estimates to find a
prime greater than the length. Under a square-product assumption that prime
forces a sufficiently large start; distinct squarefree parts then give
incompatible upper and lower odd-prefix product bounds. This longer proof
replaces the Saradha citation without adding another number-theoretic input.
The remaining odd-prefix pairing classification follows the paper.

## Lemma 4.1 and the geometric boundary

`Curves.SuperellipticGeometry` proves absolute irreducibility by Eisenstein
at a simple root and proves geometric affine nonsingularity by the Jacobian
criterion. These checks are internal. In contrast with the draft's direct
use of the genus formula, `External.Genus` assumes only the required lower
bound for `m = branchCount ell`: six for exponents two or three, and `ell`
otherwise, exactly (4.1). The more general range of `m` in Lemma 4.1 and its
exact genus formula are not claimed as Lean theorems.

The two geometric inputs share the concrete regular-differential genus of
the actual coordinate function field (`Curves.GeometricGenus`). Regularity
is imposed at all discrete valuation subrings containing the constants,
including places at infinity. The standard comparison with the smooth
projective model and the passage from projective to affine Faltings are
included in the accepted external formulation, not proved internally.
`Curves.AffineFiniteness` then derives the exact finiteness premise used in
both curve-counting applications. No fifth finiteness input remains.

The Remond input is only the finite branch of his Theoreme 1.1. Its bound
is `exp (5^(D^4) * log M * log (log M))`, with a nested exponent on five;
the cached original theorem was checked visually during this review.
`Curves.Counting` uses the paper's degree bound `max ell m`, a proved
coefficient bound `(L+1)^m`, and `M = 3*(L+1)^m >= 3`. Restricting the input's
coefficient bound `M` to natural numbers suffices for these applications.

## Lemma 4.4 and Proposition 3.5

`Combinatorics.ElementaryTuples` replaces Lemma 4.4, rather than claiming its
full statement. For `u = m/c`, it requires the stronger size condition
`12*u*2^(exp (4*u)) <= k` and replaces the common-divisor lower bound's
exponential constant `2.77` by `5`. The conclusion still supplies at least
`c*k/(6*(m+1))` disjoint tuples. Its proof uses finite inclusion-exclusion
and a harmonic Euler-product bound in place of the fundamental lemma of
sieve theory and the Rosser--Schoenfeld estimate cited by the draft.

`Analytic.TupleThreshold` proves that this stronger condition holds with
one absolute threshold for the needed `c = 1/(2000*m*log m)` and every
allowed exponent. In particular, `m^5 <= 243*log(log k)` gives the uniform
fourth-power estimate needed for this stronger threshold. Subsequent curve
side lengths use the revised constant `5` consistently.

The curve construction is the same multiplication-and-division argument
as (4.2). Finite-family counting bounds all the points by the number of
descriptors times the Remond bound, instead of pigeonholing first to one
curve as in (4.3)--(4.4). Overcounting descriptors (even zero coefficients
or repeated shifts) is harmless: finiteness is used only for the actual
constructed equations, with nonzero coefficient and distinct shifts.

## Lemmas 5.3--5.5 and Proposition 4.5

`Fibers.InitialMass` proves Lemma 5.3 via explicit logarithmic factorial
inequalities in `Analytic.FactorialDeficit`, replacing the draft's
asymptotic Stirling calculation. `Fibers.MassIncrement` proves Lemma 5.5
using the bounded-multiplicity inequality `N! <= m^N * product`, proved
by maximum deletion, in place of a sorted product with floor factorials.
The entropy allowance is `0.01`, rather than the draft's `0.007`; a uniform
weighted factorial deficit with constant `1.35`, the prime-counting upper
bound `1.05*k/log k`, and density loss `0.2` still yield the same `0.1`
mass increment. These replacements remove floor and asymptotic error terms.

`Combinatorics.BlockTuples` and `Fibers.HeavyMass` replace the dyadic split
and the two size cases in the proof of Lemma 5.4. Group each entire absolute
coefficient fiber by blocks `floor(i/(alpha*L))`, with `L` approximately
`(log k)^3`. A harmonic sum bounds the extra blocks. Every numerator support
of at least three indices contains a nontrivial `x_i`, since at most two
entries in a fiber have `x_i = 1`. Disjoint tuples therefore give distinct
points without discarding all fibers containing trivial parts. This proves
the stronger bound `0.02*k/log k`, without the draft's hypothesis on the
total number of trivial parts, and hence implies its `0.049` bound.

In this equal-fiber argument the formalization takes signed
`X = (a_i/alpha)*x_i^ell/d` and positive shifts `(i_j-i)/alpha`. The draft's
(5.4)--(5.5) instead keeps `X` positive and allows shifts of either common
sign. Absorbing that sign into `X` and the signed coefficient is an
equivalent coordinate choice. Thus the positive-shift genus hypothesis
covers both this application and Proposition 3.5. The final mass expansion
and the deduction of Proposition 4.5 follow the paper's strategy.
-/
