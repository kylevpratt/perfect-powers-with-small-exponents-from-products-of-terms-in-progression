module

public import PerfectPowers.Analytic.PrimeAPContradiction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # One absolute size threshold for the prime-AP argument -/

public section

open Filter

namespace PerfectPowers

structure PrimeAPEnvelope (k : ℕ) (C : ℝ) : Prop where
  k_ge : 12 ≤ k
  log_ge : 1 ≤ Real.log (k : ℝ)
  seven : 7 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) ≤ (k : ℝ)
  modulus : 3 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) ≤
    (Real.log (k : ℝ)) ^ (199 / 100 : ℝ)
  cost : 84 * C + 24 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) < (Real.log (k : ℝ)) ^ 2

theorem log_three_halves_square {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem eventually_primeAPEnvelope {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, PrimeAPEnvelope k C := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hhalf := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hlog
  have hgap := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 49 / 100)).comp hlog
  have hratio : Tendsto
      (fun k : ℕ => (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) / (k : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
        (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (12 : ℕ), hlog.eventually_ge_atTop 1,
    hlog.eventually_gt_atTop (168 * C + 1), hhalf.eventually_ge_atTop 48,
    hgap.eventually_ge_atTop 3,
    hratio.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 7)] with k hk hL hLC hhalf hgap hratio
  change 48 ≤ (Real.log (k : ℝ)) ^ (1 / 2 : ℝ) at hhalf
  change 3 ≤ (Real.log (k : ℝ)) ^ (49 / 100 : ℝ) at hgap
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLpos : 0 < Real.log (k : ℝ) := by linarith
  have hRpos := Real.rpow_pos_of_pos hLpos (3 / 2 : ℝ)
  have hmul : (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) *
      (Real.log (k : ℝ)) ^ (1 / 2 : ℝ) = (Real.log (k : ℝ)) ^ 2 := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hmod : (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) *
      (Real.log (k : ℝ)) ^ (49 / 100 : ℝ) = (Real.log (k : ℝ)) ^ (199 / 100 : ℝ) := by
    rw [← Real.rpow_add hLpos]
    norm_num
  refine ⟨hk, hL, ?_, ?_, ?_⟩
  · have := (div_lt_iff₀ hkpos).mp hratio
    linarith
  · have := mul_le_mul_of_nonneg_left hgap hRpos.le
    rw [hmod] at this
    linarith
  · have h48 := mul_le_mul_of_nonneg_left hhalf hRpos.le
    rw [hmul] at h48
    have hconst : 168 * C < (Real.log (k : ℝ)) ^ 2 := by nlinarith
    linarith

end PerfectPowers
