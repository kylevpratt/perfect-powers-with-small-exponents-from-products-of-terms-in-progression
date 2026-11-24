module

public import PerfectPowers.Analytic.UniformExponent
import Mathlib.Tactic

/-! # Uniform elementary size conditions for the branch parameter -/

public section

open Filter

namespace PerfectPowers

theorem eventually_branchCount_le_loglog :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell →
      (branchCount ell : ℝ) ≤ Real.log (Real.log (k : ℝ)) := by
  filter_upwards [eventually_uniform_branchCount_fourth_power (by norm_num : (0 : ℝ) < 1)] with k hk
  intro ell hell
  have hm : (1 : ℝ) ≤ branchCount ell := by
    have h := (branchCount_properties hell.2.1).1
    exact_mod_cast (show 1 ≤ branchCount ell by omega)
  have hpow : (branchCount ell : ℝ) ≤ (branchCount ell : ℝ) ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hm (by norm_num : 1 ≤ 4)
  have h := hk ell hell
  linarith

theorem eventually_branchCount_sq_le :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell → (branchCount ell : ℝ) ^ 2 ≤ (k : ℝ) := by
  filter_upwards [eventually_uniform_branchCount_fourth_power (by norm_num : (0 : ℝ) < 1)] with k hk
  intro ell hell
  have hm : (1 : ℝ) ≤ branchCount ell := by
    have h := (branchCount_properties hell.2.1).1
    exact_mod_cast (show 1 ≤ branchCount ell by omega)
  have hpow : (branchCount ell : ℝ) ^ 2 ≤ (branchCount ell : ℝ) ^ 4 :=
    pow_le_pow_right₀ hm (by norm_num)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := hell.1; omega)
  have hlogk := Real.log_le_sub_one_of_pos hkpos
  have hloglogk := Real.log_le_sub_one_of_pos hell.log_pos
  have h := hk ell hell
  linarith

end PerfectPowers
