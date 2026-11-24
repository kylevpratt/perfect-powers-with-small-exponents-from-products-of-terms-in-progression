module

public import PerfectPowers.Basic.Definitions
import Mathlib.Tactic

/-! # The branch count and numerical parameters used in the counting arguments -/

@[expose] public section

namespace PerfectPowers

def branchCount (ell : ℕ) : ℕ := if ell ≤ 3 then 6 else ell

noncomputable def rho (m : ℕ) : ℝ := 1 / (1000 * Real.log (m : ℝ))

theorem branchCount_properties {ell : ℕ} (hell : 2 ≤ ell) :
    4 ≤ branchCount ell ∧ ell ≤ branchCount ell ∧ ell ∣ branchCount ell ∧
      branchCount ell + ell ≥ 7 ∧ branchCount ell ≤ 3 * ell := by
  by_cases hsmall : ell ≤ 3
  · interval_cases ell <;> norm_num [branchCount]
  · simp only [branchCount, ite_eq_right hsmall]
    exact ⟨by omega, le_rfl, dvd_rfl, by omega, by omega⟩

end PerfectPowers
