module

public import PerfectPowers.Fibers.LargeCoefficients
public import PerfectPowers.Analytic.FactorialDeficit
public import PerfectPowers.Analytic.PrimeCounting
import Mathlib.Tactic

/-! # The initial mass lower bound (Lemma 5.3) -/

public section

open Filter

namespace PerfectPowers

/-- One threshold works for every primitive progression and every decomposition;
no bound on the exponent is needed for this initial estimate. -/
theorem eventually_initial_small_mass :
    ∀ᶠ k : ℕ in atTop,
      ∀ (ell d : ℕ) (n : ℤ) (S : Finset ℕ) (D : Decomposition k ell n d S) (I : GoodIndices D),
        Nat.Coprime n.natAbs d → S ⊆ Finset.range k → Dense k S →
        (1 / 10 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) ≤ (D.smallIndices I).card := by
  filter_upwards [eventually_factorial_square_deficit,
    eventually_primeCounting_le_twenty_one_twentieths] with k hdef hpi
  intro ell d n S D I hprimitive hS hdense
  have hR := hdef (D.largeIndices I).card (D.large_indices_factorial_le_square I hprimitive hS)
  have hcardNat : S.card ≤ (D.smallIndices I).card + (D.largeIndices I).card + Nat.primeCounting k := by
    rw [D.small_large_card]
    exact I.card_bound
  have hcard : (S.card : ℝ) ≤ (D.smallIndices I).card + (D.largeIndices I).card +
      (Nat.primeCounting k : ℝ) := by exact_mod_cast hcardNat
  change (k : ℝ) - (1 / 5 : ℝ) * (k : ℝ) / Real.log (k : ℝ) ≤ (S.card : ℝ) at hdense
  rw [mul_div_assoc] at hdense
  linarith

end PerfectPowers
