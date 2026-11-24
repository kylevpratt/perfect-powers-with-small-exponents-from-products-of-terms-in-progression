module

public import PerfectPowers.Basic.Definitions

/-!
Specifications for Theorems 1.2, 1.4, and 1.5. These are definitions of
propositions, not assumed proofs. `Main.Conditional` proves them from the
four agreed external inputs, with no remaining internal hypothesis.

Scope difference from the paper: the threshold is asserted to exist,
without an effective-computability claim. This and the substantive proof
changes are documented in `PerfectPowers.PaperComparison`.
-/

set_option autoImplicit false

@[expose] public section

namespace PerfectPowers

def Theorem15At (k : ℕ) : Prop :=
  ∀ (ell : ℕ) (n : ℤ) (d : ℕ) (b y : ℤ) (S : Finset ℕ),
    SmallExponent k ell → Dense k S → Solution k ell n d b y S →
      Smooth k (progressionProduct n d S) ∧
      (d : ℝ) ≤ 3 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) ∧
      n.natAbs ≤ k * (d + 1) ∧
      (VeryDense k S → d = 1 ∨ d = 2)

def Theorem14At (k : ℕ) : Prop :=
  ∀ (ell : ℕ) (n : ℤ) (d : ℕ) (b y : ℤ),
    SmallExponent k ell → Solution k ell n d b y (Finset.range k) →
      Smooth k (progressionProduct n d (Finset.range k)) ∧
      (d = 1 ∨ d = 2) ∧ n.natAbs ≤ k * (d + 1) ∧
      ∃ p : ℕ, LeastPrimeAbove k p ∧ AdmissiblePair k p n d

def Theorem12At (k : ℕ) : Prop :=
  ∀ (ell : ℕ) (n : ℤ) (d : ℕ) (y : ℤ),
    SmallExponent k ell → Solution k ell n d 1 y (Finset.range k) →
      ell = 2 ∧ d = 2 ∧
      ((4 ∣ k ∧ n = 1 - (k : ℤ)) ∨
        (Odd k ∧ IsSquare k ∧ n = 2 - (k : ℤ)))

/-- One absolute threshold works for all three results and every allowed exponent. -/
def MainResults : Prop :=
  ∃ k₀ : ℕ, 3 ≤ k₀ ∧
    ∀ k : ℕ, k₀ ≤ k → Theorem15At k ∧ Theorem14At k ∧ Theorem12At k

end PerfectPowers
