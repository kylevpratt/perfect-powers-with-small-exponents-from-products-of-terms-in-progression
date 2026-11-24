module

public import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Tactic

/-! # Factorial logarithm bounds with explicit errors -/

public section

namespace PerfectPowers

theorem log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log (n.factorial : ℝ) := by
  simpa only [Real.sum_log_eq_log_factorial] using Real.le_sum_log_nat n

theorem log_factorial_upper {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - n + Real.log (n : ℝ) + 1 := by
  have h := Real.sum_log_le (x := (n : ℝ)) (by exact_mod_cast hn)
  simpa only [Nat.floor_natCast, Real.sum_log_eq_log_factorial] using h

end PerfectPowers
