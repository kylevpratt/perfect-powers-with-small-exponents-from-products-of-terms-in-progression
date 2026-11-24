module

public import Mathlib.Data.Int.GCD
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Challenge: perfect powers from products of terms in progression

Specification for Kyle Pratt's *Perfect powers with small exponents from
products of terms in progression*. The statements follow the author's draft
of that paper. Only Mathlib is imported. All project definitions needed to
read the targets and their hypotheses are written below.

Targets:
* `PerfectPowersChallenge.main_results`: Theorems 1.2, 1.4, and 1.5 with
  one absolute threshold, conditional on exactly four external statements.
* `PerfectPowersChallenge.lemma_3_6`: odd positive progression products
  of length at least two are not squares, with no external hypothesis.
* `PerfectPowersChallenge.consecutive_product_nonsquare`: the restricted
  consecutive-product obstruction, also with no external hypothesis.

Agreed scope: existence of the threshold, without an effective-computability
claim. The four external inputs, including the geometric comparison boundary
described below, are accepted hypotheses. Proving them is not a target.
The three target proof holes are intentional. The separate Solution must
supply proofs. A successful comparison does not prove the external inputs.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PerfectPowersChallenge

/-! ## Progressions and the paper's hypotheses -/

/-- The progression term `n + i*d`, with all arithmetic in the integers. -/
def term (n : ℤ) (d i : ℕ) : ℤ := n + (i : ℤ) * (d : ℤ)

/-- The integer product of progression terms whose indices lie in `S`. -/
def progressionProduct (n : ℤ) (d : ℕ) (S : Finset ℕ) : ℤ :=
  ∏ i ∈ S, term n d i

/-- For nonzero `z`, this is the paper's `P⁺(z) ≤ k` when `k ≥ 1`.
In particular, both `1` and `-1` satisfy the prime-divisor condition. -/
def Smooth (k : ℕ) (z : ℤ) : Prop :=
  z ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ z.natAbs → p ≤ k

/-- The paper's fifth-root bound, with no primality requirement on `ell`.
The logarithm domain `3 ≤ k` is redundant above the final threshold. -/
def SmallExponent (k ell : ℕ) : Prop :=
  3 ≤ k ∧ 2 ≤ ell ∧
    (ell : ℝ) ≤ (Real.log (Real.log (k : ℝ))) ^ (1 / 5 : ℝ)

/-- The first density condition in Theorem 1.5: loss at most `0.2*k/log k`. -/
def Dense (k : ℕ) (S : Finset ℕ) : Prop :=
  (k : ℝ) - (1 / 5 : ℝ) * (k : ℝ) / Real.log (k : ℝ) ≤ (S.card : ℝ)

/-- The additional density condition in Theorem 1.5: loss at most `k/(log k)^3`. -/
def VeryDense (k : ℕ) (S : Finset ℕ) : Prop :=
  (k : ℝ) - (k : ℝ) / Real.log (k : ℝ) ^ 3 ≤ (S.card : ℝ)

/-- The central equation and all its arithmetic hypotheses.
The start, coefficient, and power base are signed nonzero integers.
The positive integer step is represented by a natural number with `0 < d`.
No nonvanishing condition is imposed on terms outside `S`. -/
structure Solution (k ell : ℕ) (n : ℤ) (d : ℕ) (b y : ℤ) (S : Finset ℕ) : Prop where
  index_subset : S ⊆ Finset.range k
  n_ne_zero : n ≠ 0
  d_pos : 0 < d
  b_ne_zero : b ≠ 0
  y_ne_zero : y ≠ 0
  coprime : Nat.Coprime n.natAbs d
  b_smooth : Smooth k b
  equation : progressionProduct n d S = b * y ^ ell

/-- `p` is prime, exceeds `k`, and is no greater than any other such prime. -/
def LeastPrimeAbove (k p : ℕ) : Prop :=
  p.Prime ∧ k < p ∧ ∀ q : ℕ, q.Prime → k < q → p ≤ q

/-- Exactly the three closed ranges in the paper's display (1.4).
All subtractions here are integer subtractions, including `k - 1`. -/
def AdmissiblePair (k p : ℕ) (n : ℤ) (d : ℕ) : Prop :=
  (d = 1 ∧ 1 ≤ n ∧ n ≤ (p : ℤ) - (k : ℤ)) ∨
  (d = 1 ∧ -((p : ℤ) - 1) ≤ n ∧ n ≤ -(k : ℤ)) ∨
  (d = 2 ∧ -((p : ℤ) - 2) ≤ n ∧
    n ≤ (p : ℤ) - 2 - 2 * ((k : ℤ) - 1) ∧ Odd n)

/-! ## The three main conclusions -/

/-- Theorem 1.5, including its stronger-density conclusion. -/
def Theorem15At (k : ℕ) : Prop :=
  ∀ (ell : ℕ) (n : ℤ) (d : ℕ) (b y : ℤ) (S : Finset ℕ),
    SmallExponent k ell → Dense k S → Solution k ell n d b y S →
      Smooth k (progressionProduct n d S) ∧
      (d : ℝ) ≤ 3 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) ∧
      n.natAbs ≤ k * (d + 1) ∧
      (VeryDense k S → d = 1 ∨ d = 2)

/-- Theorem 1.4, including all endpoint ranges from (1.4). -/
def Theorem14At (k : ℕ) : Prop :=
  ∀ (ell : ℕ) (n : ℤ) (d : ℕ) (b y : ℤ),
    SmallExponent k ell → Solution k ell n d b y (Finset.range k) →
      Smooth k (progressionProduct n d (Finset.range k)) ∧
      (d = 1 ∨ d = 2) ∧ n.natAbs ≤ k * (d + 1) ∧
      ∃ p : ℕ, LeastPrimeAbove k p ∧ AdmissiblePair k p n d

/-- Theorem 1.2: every solution lies in one of the two stated families.
As in the paper's theorem, this is the necessary-condition direction. -/
def Theorem12At (k : ℕ) : Prop :=
  ∀ (ell : ℕ) (n : ℤ) (d : ℕ) (y : ℤ),
    SmallExponent k ell → Solution k ell n d 1 y (Finset.range k) →
      ell = 2 ∧ d = 2 ∧
      ((4 ∣ k ∧ n = 1 - (k : ℤ)) ∨
        (Odd k ∧ IsSquare k ∧ n = 2 - (k : ℤ)))

/-- One threshold precedes all quantifiers on the allowed exponent and on
the progression data. No effective-computability assertion is included. -/
def MainResults : Prop :=
  ∃ k₀ : ℕ, 3 ≤ k₀ ∧
    ∀ k : ℕ, k₀ ≤ k → Theorem15At k ∧ Theorem14At k ∧ Theorem12At k

/-! ## Equations, rational points, and a concrete genus invariant -/

/-- Evaluate an integer bivariate polynomial at the rational pair `(x,y)`. -/
def evalPair (P : ℚ × ℚ) : MvPolynomial (Fin 2) ℤ →+* ℚ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun i => if i = 0 then P.1 else P.2)

/-- The set of rational pairs at which `F` vanishes. -/
def RationalZeros (F : MvPolynomial (Fin 2) ℤ) : Set (ℚ × ℚ) :=
  {P | evalPair P F = 0}

/-- The rational differentials generated by `a * db`, with `a,b` in `R`. -/
def differentialsRegularAt (K : Type*) [Field K] [Algebra ℚ K]
    (R : Subalgebra ℚ K) : Submodule ℚ (KaehlerDifferential ℚ K) :=
  Submodule.span ℚ (Set.range (fun ab : R × R =>
    (ab.1 : K) • KaehlerDifferential.D ℚ K (ab.2 : K)))

/-- Regularity at every discrete valuation subring containing the constants
and having fraction field `K`. No places at infinity are omitted. -/
def regularDifferentials (K : Type*) [Field K] [Algebra ℚ K] :
    Submodule ℚ (KaehlerDifferential ℚ K) :=
  ⨅ (R : Subalgebra ℚ K) (_ : IsDiscreteValuationRing R) (_ : IsFractionRing R K),
    differentialsRegularAt K R

/-- The dimension over `ℚ` of the space of everywhere regular differentials. -/
def functionFieldGenus (K : Type*) [Field K] [Algebra ℚ K] : ℕ :=
  Module.finrank ℚ (regularDifferentials K)

/-- An affine plane equation irreducible over both `ℚ` and its algebraic
closure. These proof fields are premises to the geometric inputs. -/
structure AffinePlaneCurve where
  equation : MvPolynomial (Fin 2) ℤ
  irreducible : Irreducible (equation.map (Int.castRingHom ℚ))
  geometricallyIrreducible :
    Irreducible (equation.map (Int.castRingHom (AlgebraicClosure ℚ)))

namespace AffinePlaneCurve

/-- The principal ideal generated by the curve equation over `ℚ`. -/
abbrev coordinateIdeal (C : AffinePlaneCurve) : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {C.equation.map (Int.castRingHom ℚ)}

instance (C : AffinePlaneCurve) : C.coordinateIdeal.IsPrime :=
  Ideal.isPrime_span_singleton_of_prime C.irreducible.prime

/-- The coordinate ring `ℚ[x,y]/(F)` of the integral affine plane equation. -/
abbrev coordinateRing (C : AffinePlaneCurve) :=
  MvPolynomial (Fin 2) ℚ ⧸ C.coordinateIdeal

/-- The fraction field of the integral coordinate ring. -/
abbrev functionField (C : AffinePlaneCurve) := FractionRing C.coordinateRing

/-- Genus is defined from the actual coordinate function field, rather than
assigned by a formula to the family of equations used in this project. -/
def geometricGenus (C : AffinePlaneCurve) : ℕ :=
  functionFieldGenus C.functionField

/-- The Jacobian criterion at every geometric affine zero. -/
def Nonsingular (C : AffinePlaneCurve) : Prop :=
  ∀ P : Fin 2 → AlgebraicClosure ℚ,
    MvPolynomial.eval₂ (Int.castRingHom _) P C.equation = 0 →
      ∃ i : Fin 2, MvPolynomial.eval₂ (Int.castRingHom _) P
        (MvPolynomial.pderiv i C.equation) ≠ 0

end AffinePlaneCurve

/-! ## The four accepted external statements

These are definitions of propositions, not global axioms.
The standard identification of the regular-differential invariant above
with the genus of the smooth projective model, and the passage from
projective Faltings to the following affine statement, belong to the
accepted external boundary. They are not claimed as internal proofs.
-/

/-- External input 1: the accepted affine-plane formulation of Faltings. -/
def AffineFaltingsStatement : Prop :=
  ∀ C : AffinePlaneCurve, C.Nonsingular → 2 ≤ C.geometricGenus →
    (RationalZeros C.equation).Finite

/-- Six branches for exponents two or three; `ell` branches otherwise.
Only exponents at least two occur in the external genus hypothesis. -/
def branchCount (ell : ℕ) : ℕ := if ell ≤ 3 then 6 else ell

/-- Coordinates `X 0 = x`, `X 1 = y`: `B*y^ell - ∏ j (x+C_j)`. -/
def curvePolynomial (ell : ℕ) {m : ℕ} (B : ℤ) (C : Fin m → ℤ) :
    MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.C B * MvPolynomial.X 1 ^ ell -
    ∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j))

/-- External input 2: the genus lower bound for the required family.
It applies to every geometrically integral curve with the displayed equation.
To use it, a Solution must supply the irreducibility proofs in `curve`;
this hypothesis supplies only the genus bound. Distinct positive shifts
and either sign of the nonzero integer coefficient `B` are allowed. -/
def SuperellipticGenusStatement : Prop :=
  ∀ (ell : ℕ) (B : ℤ) (C : Fin (branchCount ell) → ℤ),
    2 ≤ ell → B ≠ 0 → Function.Injective C → (∀ j, 0 < C j) →
    ∀ curve : AffinePlaneCurve,
      curve.equation = curvePolynomial ell B C → 2 ≤ curve.geometricGenus

/-- Every integer coefficient of `F` has absolute value at most `M`. -/
def CoefficientsBounded (F : MvPolynomial (Fin 2) ℤ) (M : ℕ) : Prop :=
  ∀ s, (F.coeff s).natAbs ≤ M

/-- The power of five is nested: `exp(5^(D^4) * log M * log(log M))`. -/
def remondBound (D M : ℕ) : ℝ :=
  Real.exp ((5 : ℝ) ^ (D ^ 4) * Real.log (M : ℝ) * Real.log (Real.log (M : ℝ)))

/-- External input 3: the finite branch of Remond's Theoreme 1.1.
Finiteness is an explicit prerequisite. Bounding every finite subset of
the rational zero set then expresses the bound on its cardinality. -/
def RemondStatement : Prop :=
  ∀ (F : MvPolynomial (Fin 2) ℤ) (M : ℕ),
    3 ≤ M → CoefficientsBounded F M → (RationalZeros F).Finite →
    ∀ points : Finset (ℚ × ℚ), (↑points : Set (ℚ × ℚ)) ⊆ RationalZeros F →
      (points.card : ℝ) ≤ remondBound F.totalDegree M

/-- The weighted prime sum over `y < p ≤ x`, with `p ≡ a (mod d)`. -/
def thetaAP (x y : ℝ) (d : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter
      (fun p : ℕ => y < (p : ℝ) ∧ Int.ModEq (d : ℤ) (p : ℤ) a),
    Real.log (p : ℝ)

/-- External input 4: Lemma 3.3's uniform prime-AP estimate.
The positive constant depends only on `A`, preceding all other parameters.
No algorithm for computing that constant is asserted in this scope. -/
def PrimeAPStatement : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ (x y : ℝ) (d : ℕ) (a : ℤ),
      5 ≤ y → y ≤ x → 2 ≤ d →
      (d : ℝ) ≤ (Real.log x) ^ (199 / 100 : ℝ) →
      Nat.Coprime a.natAbs d →
      |thetaAP x y d a - (x - y) / (Nat.totient d : ℝ)| ≤
        C * x / (Real.log x) ^ A

/-! ## Advertised targets

Only these three proofs are left blank. Solution must prove matching statements
using only `propext`, `Classical.choice`, and `Quot.sound`.
-/

/-- Theorems 1.2, 1.4, and 1.5, conditional on the four accepted inputs. -/
theorem main_results
    (hFaltings : AffineFaltingsStatement)
    (hGenus : SuperellipticGenusStatement)
    (hRemond : RemondStatement) (hAP : PrimeAPStatement) : MainResults := by
  sorry

/-- Lemma 3.6. Positivity and oddness of the product make this equivalent
to the paper's exclusion of positive odd square roots. -/
theorem lemma_3_6 (m k : ℕ) (hm : 0 < m) (hodd : Odd m) (hk : 2 ≤ k) :
    ¬ IsSquare (∏ i ∈ Finset.range k, (m + 2 * i)) := by
  sorry

/-- The consecutive-product obstruction needed after Theorem 1.4.
This target is restricted to `1 ≤ a ≤ k`; it makes no claim for `a > k`. -/
theorem consecutive_product_nonsquare (k a : ℕ)
    (hk : 2 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) :
    ¬ IsSquare (∏ i ∈ Finset.range k, (a + i)) := by
  sorry

end PerfectPowersChallenge
