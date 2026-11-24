module

public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Foundational definitions for the formalization of Kyle Pratt's
"Perfect powers with small exponents from products of terms in progression".

The main results are specified separately and are not assumed by this module.
-/

set_option autoImplicit false

@[expose] public section

namespace PerfectPowers

def term (n : ℤ) (d i : ℕ) : ℤ := n + (i : ℤ) * (d : ℤ)

def progressionProduct (n : ℤ) (d : ℕ) (S : Finset ℕ) : ℤ :=
  ∏ i ∈ S, term n d i

/-- Nonzero signed integers whose prime divisors are at most `k`. -/
def Smooth (k : ℕ) (z : ℤ) : Prop :=
  z ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ z.natAbs → p ≤ k

/-- The polynomial version of the exponent range, with a safe logarithm domain. -/
def SmallExponent (k ell : ℕ) : Prop :=
  3 ≤ k ∧ 2 ≤ ell ∧ (ell : ℝ) ^ 5 ≤ Real.log (Real.log (k : ℝ))

def Dense (k : ℕ) (S : Finset ℕ) : Prop :=
  (k : ℝ) - (1 / 5 : ℝ) * (k : ℝ) / Real.log (k : ℝ) ≤ (S.card : ℝ)

def VeryDense (k : ℕ) (S : Finset ℕ) : Prop :=
  (k : ℝ) - (k : ℝ) / Real.log (k : ℝ) ^ 3 ≤ (S.card : ℝ)

/-- A solution of the central equation. No primality condition is imposed on `ell`. -/
structure Solution (k ell : ℕ) (n : ℤ) (d : ℕ) (b y : ℤ) (S : Finset ℕ) : Prop where
  index_subset : S ⊆ Finset.range k
  n_ne_zero : n ≠ 0
  d_pos : 0 < d
  b_ne_zero : b ≠ 0
  y_ne_zero : y ≠ 0
  coprime : Nat.Coprime n.natAbs d
  b_smooth : Smooth k b
  equation : progressionProduct n d S = b * y ^ ell

/-- This relation avoids choosing a least prime before proving its existence. -/
def LeastPrimeAbove (k p : ℕ) : Prop :=
  p.Prime ∧ k < p ∧ ∀ q : ℕ, q.Prime → k < q → p ≤ q

/-- The three ranges in (1.4), with all interval arithmetic performed in `ℤ`. -/
def AdmissiblePair (k p : ℕ) (n : ℤ) (d : ℕ) : Prop :=
  (d = 1 ∧ 1 ≤ n ∧ n ≤ (p : ℤ) - (k : ℤ)) ∨
  (d = 1 ∧ -((p : ℤ) - 1) ≤ n ∧ n ≤ -(k : ℤ)) ∨
  (d = 2 ∧ -((p : ℤ) - 2) ≤ n ∧
    n ≤ (p : ℤ) - 2 - 2 * ((k : ℤ) - 1) ∧ Odd n)

end PerfectPowers
