module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # A threshold uniform for all bounded-multiplicity parameters -/

public section

open Filter

namespace PerfectPowers

theorem eventually_mass_exceeds_multiplicity :
    ∀ᶠ k : ℕ in atTop, ∀ (m : ℕ) (δ : ℝ), (m : ℝ) ^ 2 ≤ k →
      (1 / 1000 : ℝ) ≤ δ → (m : ℝ) ≤ δ * ((k : ℝ) / Real.log (k : ℝ)) := by
  have hlim : Tendsto (fun k : ℕ => (Real.log (k : ℝ)) ^ 2 / (k : ℝ)) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa only [Real.rpow_two, Real.rpow_one, Function.comp_def] using h
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 1000000),
    eventually_ge_atTop (2 : ℕ)] with k hsmall hk
  intro m δ hm hδ
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hlogSq : (1000 * Real.log (k : ℝ)) ^ 2 ≤ (k : ℝ) := by
    have h := (div_lt_iff₀ hkpos).mp hsmall
    nlinarith
  have hprod : (m : ℝ) * (1000 * Real.log (k : ℝ)) ≤ (k : ℝ) := by
    nlinarith [sq_nonneg ((m : ℝ) - 1000 * Real.log (k : ℝ))]
  have hbase : (m : ℝ) ≤ (1 / 1000 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hLpos).mpr
    nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_right hδ (div_nonneg hkpos.le hLpos.le))

end PerfectPowers
