module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The permitted prime-distribution input (Lemma 3.3)

This module defines a proposition; it does not declare an axiom or prove it.
The error constant is uniform in every parameter other than the fixed `A`.
The project requires only this bound. Computing effective constants is
outside the agreed scope of the existence-of-threshold result.
-/

@[expose] public section

namespace PerfectPowers.External

noncomputable def thetaAP (x y : ℝ) (d : ℕ) (a : ℤ) : ℝ :=
  ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter
      (fun p : ℕ => y < (p : ℝ) ∧ Int.ModEq (d : ℤ) (p : ℤ) a),
    Real.log (p : ℝ)

def PrimeAPStatement : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ (x y : ℝ) (d : ℕ) (a : ℤ),
      5 ≤ y → y ≤ x → 2 ≤ d →
      (d : ℝ) ≤ (Real.log x) ^ (199 / 100 : ℝ) →
      Nat.Coprime a.natAbs d →
      |thetaAP x y d a - (x - y) / (Nat.totient d : ℝ)| ≤
        C * x / (Real.log x) ^ A

end PerfectPowers.External
