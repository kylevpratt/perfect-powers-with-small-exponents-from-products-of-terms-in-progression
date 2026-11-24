module

public import PerfectPowers.Curves.Equation
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# The permitted Remond input

This is the finite branch of Theoreme 1.1 of Remond (2010). Finiteness must
be supplied before the bound can be used. The power inside `exp` is `5^(D^4)`.
No mathematical axiom is introduced by defining this proposition.
-/

@[expose] public section

namespace PerfectPowers.External

def RationalZeros (F : MvPolynomial (Fin 2) ℤ) : Set (ℚ × ℚ) :=
  {P | evalPair P F = 0}

def CoefficientsBounded (F : MvPolynomial (Fin 2) ℤ) (M : ℕ) : Prop :=
  ∀ s, (F.coeff s).natAbs ≤ M

noncomputable def remondBound (D M : ℕ) : ℝ :=
  Real.exp ((5 : ℝ) ^ (D ^ 4) * Real.log (M : ℝ) * Real.log (Real.log (M : ℝ)))

def RemondStatement : Prop :=
  ∀ (F : MvPolynomial (Fin 2) ℤ) (M : ℕ),
    3 ≤ M → CoefficientsBounded F M → (RationalZeros F).Finite →
    ∀ points : Finset (ℚ × ℚ), (↑points : Set (ℚ × ℚ)) ⊆ RationalZeros F →
      (points.card : ℝ) ≤ remondBound F.totalDegree M

end PerfectPowers.External
