# Perfect powers with small exponents from products of terms in progression

A Lean 4 formalization of Theorems 1.2, 1.4, and 1.5 of Kyle Pratt's paper
*Perfect powers with small exponents from products of terms in progression*,
**conditional on four explicit external mathematical hypotheses**.

The main theorem proves existence of one absolute threshold, uniform in all
allowed exponents and progression parameters. Effective computability of that
threshold and proofs of the four external inputs are outside the project scope.

## Main results

The central equation is

```math
\prod_{i\in S}(n+id)=b y^\ell.
```

The [basic definitions](PerfectPowers/Basic/Definitions.lean) require
$k,\ell,d\in\mathbb{N}$, $k\geq 3$, $d>0$, nonzero signed integers $n,b,y$,
$\gcd(|n|,d)=1$, $S\subseteq\lbrace 0,\ldots,k-1\rbrace$, and every prime divisor of $|b|$
to be at most $k$. The exponent satisfies
$2\leq\ell\leq(\log\log k)^{1/5}$ and need not be prime. All logarithms are natural.

The three [result specifications](PerfectPowers/Main/Statements.lean) are in
namespace `PerfectPowers`:

| Paper result | Lean specification | Conclusion under these hypotheses |
| --- | --- | --- |
| Theorem 1.5 | `Theorem15At k` | For a dense index set, the product is $k$-smooth, $d\leq 3(\log k)^{3/2}$, and $\lvert n\rvert\leq k(d+1)$. For a very dense set, also $d=1$ or $d=2$. |
| Theorem 1.4 | `Theorem14At k` | For the full index set, the product is $k$-smooth, $d=1$ or $d=2$, $\lvert n\rvert\leq k(d+1)$, and $(n,d)$ lies in the three ranges of (1.4), encoded by `AdmissiblePair` using the least prime greater than $k$. |
| Theorem 1.2 | `Theorem12At k` | For the full index set with $b=1$, necessarily $\ell=2$, $d=2$, and either $4\mid k$ with $n=1-k$, or $k$ is an odd square with $n=2-k$. |

Here `Smooth k z` includes $z\neq 0$ and means that every prime divisor of $|z|$
is at most $k$. The density requirements are
$|S|\geq k-\frac{k}{5\log k}$ and, for very dense sets,
$|S|\geq k-\frac{k}{(\log k)^3}$. Theorem 1.2 states the necessary-condition
direction, as in the paper.

`MainResults` asserts that there is a single $k_0\geq 3$ such that all three
specifications hold for every $k\geq k_0$. Its quantifiers on the exponent and
progression data come after the choice of $k_0$.

The entry point is
[`PerfectPowers.mainResults_of_external_inputs`](PerfectPowers/Main/Conditional.lean).
Import `PerfectPowers` to use the library.

## Four external hypotheses

The main theorem takes the following propositions as explicit arguments. Their
names are in namespace `PerfectPowers.External`. The project supplies no proofs
of these inputs and declares no global mathematical axioms for them.

### 1. Affine Faltings

[`AffineFaltingsStatement`](PerfectPowers/External/AffineFaltings.lean):
an integer-coefficient affine plane equation over $\mathbb{Q}$ that is absolutely
irreducible, geometrically nonsingular, and of geometric genus at least two has
finitely many rational zeros.

The `AffinePlaneCurve` structure includes proofs of irreducibility over
$\mathbb{Q}$ and its algebraic closure. Nonsingularity is the Jacobian criterion
at every zero over that algebraic closure.

### 2. Superelliptic genus lower bound

[`SuperellipticGenusStatement`](PerfectPowers/External/Genus.lean):
for every $\ell\geq 2$, nonzero integer $B$, and distinct positive integer shifts
$C_1,\ldots,C_m$, the curve

```math
B y^\ell=\prod_{j=1}^{m}(x+C_j)
```

has geometric genus at least two for
$m=\mathrm{branchCount}(\ell)$, where $m=6$ for $\ell=2,3$ and $m=\ell$
for $\ell\geq 4$. The bound is uniform in $B$ and the shifts; $B$ may have either
sign. The exact genus formula and the broader range of $m$ in the paper's proof
of Lemma 4.1 are outside the formalized results. The signed coordinate choice in
the equal-fiber argument permits positive shifts in both curve applications;
see [PaperComparison.lean](PerfectPowers/PaperComparison.lean).

**Geometric boundary.** Both inputs use the
[genus of the coordinate function field](PerfectPowers/Curves/GeometricGenus.lean):
the $\mathbb{Q}$-dimension of rational differentials regular at every discrete
valuation subring containing the constants and having that function field as
its fraction field, including places at infinity. The standard comparison with
smooth-projective genus, the geometric interpretation of the Jacobian
criterion, and the affine corollary of projective Faltings belong to the accepted
external boundary; their comparison proofs are outside this development.

### 3. Rémond's rational-point bound

[`RemondStatement`](PerfectPowers/External/Remond.lean) is the finite branch
of Rémond's Théorème 1.1 (2010). For an integer-coefficient polynomial $F(X,Y)$
of total degree $D$ and a natural number $M\geq 3$ bounding the absolute value of
every coefficient, **assuming its rational zero set is finite**, the bound is

```math
\#\{(x,y)\in\mathbb{Q}^2:F(x,y)=0\}
\leq \exp\!\left(5^{D^4}\log M\,\log\log M\right).
```

The Lean statement bounds every finite subset of that zero set and explicitly
requires finiteness. The exponent on five is $D^4$.

### 4. Uniform prime distribution in arithmetic progressions

[`PrimeAPStatement`](PerfectPowers/External/PrimeAP.lean) retains the estimate
of Lemma 3.3. For every real $A>0$ there exists $C_A>0$ such that

```math
\left|\theta(x,y;d,a)-\frac{x-y}{\varphi(d)}\right|
\leq \frac{C_A x}{(\log x)^A},
```

where

```math
\theta(x,y;d,a)=
\sum_{\substack{y<p\leq x\\p\text{ prime}\\p\equiv a\pmod{d}}}\log p,
```

for all real $x\geq y\geq 5$, natural numbers
$2\leq d\leq(\log x)^{199/100}$, and integers $a$ with $\gcd(|a|,d)=1$.
The constant depends only on $A$, uniformly in $x,y,d,a$. The paper's assertion
that the constant is effectively computable is outside the formalized input.

### Internal deductions and logical axioms

[SuperellipticGeometry.lean](PerfectPowers/Curves/SuperellipticGeometry.lean)
proves absolute irreducibility and geometric affine nonsingularity independently
of inputs 1 and 2.
[AffineFiniteness.lean](PerfectPowers/Curves/AffineFiniteness.lean) then derives
the required curve-family finiteness from those two inputs. Lemma 3.6 and the
restricted consecutive-product square obstruction are proved without any of the
four inputs. No additional external hypothesis is needed for these steps.
[EXTERNAL_INPUTS.txt](EXTERNAL_INPUTS.txt) gives further interface details.

The dependency audits report only `propext`, `Classical.choice`, and `Quot.sound`.
**An axiom audit does not prove the four external statements:** they occur as
theorem arguments, so their absence from `#print axioms` is expected.

## Differences from the paper

The paper explicitly asserts effective computability of $k_0$; the Lean result
asserts existence only. The main numerical conclusions, density requirements,
signed cases, and uniform exponent range are retained under the four inputs.

| Paper item | Lean formulation or proof |
| --- | --- |
| Variables and exponent range | Positive integral $d$ is a natural number with $d>0$; $n,b,y$ remain integers. Internally the exponent condition is $\ell^5\leq\log\log k$; [ExponentRange.lean](PerfectPowers/Analytic/ExponentRange.lean) proves equivalence to the fifth-root formulation on the relevant domain. |
| Theorem 1.4 | [ShortPrimeIntervals.lean](PerfectPowers/Analytic/ShortPrimeIntervals.lean) uses a prime in $(x,5x/4]$ for sufficiently large $x$, derived from mathlib's ordinary prime number theorem. This suffices for the same endpoint ranges. |
| Theorem 1.2: consecutive products | [StepOneObstruction.lean](PerfectPowers/Main/StepOneObstruction.lean) reduces to elementary nonsquareness for consecutive products of length $k\geq 2$ starting at $1\leq a\leq k$. It replaces the appeal to Erdős–Selfridge for this application; the unrestricted theorem is outside scope. |
| Lemma 3.6 | [OddNonsquare.lean](PerfectPowers/Squares/OddNonsquare.lean) gives an elementary proof for every positive odd start and length at least two, replacing the Saradha citation. |
| Lemma 4.1 and its proof | The required family finiteness is deduced from affine Faltings, internally proved geometry, and the assumed genus lower bound for $m=\mathrm{branchCount}(\ell)$. The full lemma's range and the exact genus formula are outside scope. |
| Lemma 4.4 | [ElementaryTuples.lean](PerfectPowers/Combinatorics/ElementaryTuples.lean) replaces the sieve argument. For $u=m/c$, it uses the stronger size condition $12u\cdot 2^{\exp(4u)}\leq k$ and exponential constant $5$ in place of $2.77$. [TupleThreshold.lean](PerfectPowers/Analytic/TupleThreshold.lean) proves the stronger condition uniformly in the required applications. The full original lemma is outside scope. |
| Lemmas 5.3–5.5 | Explicit factorial inequalities replace the asymptotic estimates, and coefficient-dependent blocks replace the dyadic split in Lemma 5.4. The heavy-fiber bound improves from $0.049k/\log k$ to $0.02k/\log k$, without the hypothesis on the total number of trivial power parts. |

[PaperComparison.lean](PerfectPowers/PaperComparison.lean) records the additional
changes to deletion bounds, curve counting, constants, and coordinates.

Numbering follows the paper draft reviewed on November 19, 2026. The SHA-256
of its reviewed text extraction is
`ED379DAD2D1C29E728FAC11E32CEBFF732569B723BF6EE3690819A785549D8E2`.
A stable public reference to the exact paper version remains to be supplied.

## Build and checks

The pinned environment is **Lean 4.36.0** and mathlib commit
`cedb8afa01aa10d8483a3740b748a59502bb8c7e`; see
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and
[lake-manifest.json](lake-manifest.json).

With Git, the matching Lean toolchain installed through `elan`, and `lake`
on your path, run from the project root:

```sh
lake exe cache get
lake build PerfectPowers.Audit
```

The audit target builds the library and prints dependency information for the
main theorem and substantial intermediate results. Plain `lake build` builds
the library alone. These standard commands also apply on Windows with the
matching toolchain installed.

[Challenge.lean](Challenge.lean) is a standalone mathlib-only specification of
the main results and the two supporting square obstructions. Its **three
intentional `sorry` placeholders** mark specification targets.
[Solution.lean](Solution.lean) proves these targets using the library.
Neither the library nor `Solution` imports `Challenge`; the proof library has
no proof placeholders.

```sh
lake build Challenge Solution
lake env lean scripts/CheckChallengeInterfaces.lean
lake env lean scripts/AuditSolution.lean
node scripts/check-submission.mjs
```

These commands build the wrappers, prove the four external-interface
equivalences and exponent-range equivalence, print solution axiom dependencies,
and run the source/configuration preflight (which requires Node.js).
Building `Challenge` produces three expected placeholder warnings.

For full Comparator verification from a clean Linux checkout, with Node.js,
`bubblewrap`, and the required user namespaces available:

```sh
bash scripts/verify-comparator.sh
```

Run this as an unprivileged user in a checkout without a `.lake` directory.
The [script](scripts/verify-comparator.sh) first runs `lake comparator --paranoid`
with sandboxing enabled, then runs the build and interface audits.
The [GitHub Actions workflow](.github/workflows/verify.yml) invokes it.

**Recorded status:** on November 24, 2026, a clean Ubuntu 24.04.5 LTS run under
WSL 2 passed Comparator with sandboxing and `--paranoid` enabled. All six bundled
checkers accepted all three targets. The library and wrapper build, dependency
audits, and five interface-equivalence checks also passed, with only the three
expected specification-placeholder warnings. The
[first hosted GitHub Actions run](https://github.com/kylevpratt/perfect-powers-with-small-exponents-from-products-of-terms-in-progression/actions/runs/45499122897)
at commit `4d47f5154b0f47e7dc09c70b062b7c0fa4e0fcb8` also passed all build,
audit, and Comparator steps. Registry submission remains unperformed. The WSL
logs are retained locally; hosted logs are available in the linked run.

## Project notes

The source directories group the arithmetic, combinatorics, coefficient-fiber,
analytic, curve, and square arguments. The repository sources comprise the
Lean library, standalone comparison files, build configuration, portable
verification tools, and documentation. Local caches, generated output,
historical notes, and Windows development helpers are excluded by
[.gitignore](.gitignore).

The paper is by Kyle Pratt. The Lean formalization was generated and iterated
by Codex under Kyle Pratt's mathematical direction, using Lean and mathlib.

## License and citation

The Lean formalization, supporting scripts, and repository documentation are
licensed under the [Apache License 2.0](LICENSE). Copyright 2026 Kyle Pratt.
Third-party components retain their respective licenses; the paper's licensing
is separate.

Please cite the formalization using [CITATION.cff](CITATION.cff), which also
identifies the associated paper. Publication identifiers can be added when
available.
