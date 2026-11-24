module

public import PerfectPowers.Analytic.TupleCurveParameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # The common-divisor tuple count exceeds the uniform curve budget -/

public section

open Filter

namespace PerfectPowers

theorem eventually_tuple_count_gt_quarter_power :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell →
      Real.exp (Real.log (k : ℝ) / 4) < tupleDensity (branchCount ell) * (k : ℝ) /
        (6 * ((branchCount ell : ℝ) + 1)) := by
  have hx : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0 : ℝ) < 3 / 4)).tendsto_div_nhds_zero
  have hsmall : ∀ᶠ k : ℕ in atTop,
      (Real.log (k : ℝ)) ^ 3 / Real.exp ((3 / 4 : ℝ) * Real.log (k : ℝ)) < 1 / 12000 :=
    hx.eventually (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 12000))
  filter_upwards [eventually_branchCount_le_loglog, hsmall] with k hmT hsmall
  intro ell hell
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := hell.1; omega)
  have hlogpos := hell.log_pos
  have hm4 : (4 : ℝ) ≤ branchCount ell := by exact_mod_cast (branchCount_properties hell.2.1).1
  have hmpos : (0 : ℝ) < branchCount ell := by linarith
  have hlogmpos : 0 < Real.log (branchCount ell : ℝ) := Real.log_pos (by linarith)
  have hmPlus : (branchCount ell : ℝ) + 1 ≤ Real.log (k : ℝ) := by
    linarith [hmT ell hell, Real.log_le_sub_one_of_pos hlogpos]
  have hlogm : Real.log (branchCount ell : ℝ) ≤ Real.log (k : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hmpos]
  have hdenpos : 0 < 12000 * (branchCount ell : ℝ) * ((branchCount ell : ℝ) + 1) *
      Real.log (branchCount ell : ℝ) := by positivity
  have hden : 12000 * (branchCount ell : ℝ) * ((branchCount ell : ℝ) + 1) *
      Real.log (branchCount ell : ℝ) ≤ 12000 * (Real.log (k : ℝ)) ^ 3 := by
    calc
      _ ≤ 12000 * Real.log (k : ℝ) * Real.log (k : ℝ) * Real.log (k : ℝ) := by gcongr; linarith
      _ = _ := by ring
  have hpoly : 12000 * (Real.log (k : ℝ)) ^ 3 < Real.exp ((3 / 4 : ℝ) * Real.log (k : ℝ)) := by
    have h := (div_lt_iff₀ (Real.exp_pos _)).mp hsmall
    linarith
  have hmul := mul_lt_mul_of_pos_right (hden.trans_lt hpoly) (Real.exp_pos (Real.log (k : ℝ) / 4))
  have hexp : Real.exp ((3 / 4 : ℝ) * Real.log (k : ℝ)) * Real.exp (Real.log (k : ℝ) / 4) = (k : ℝ) := by
    rw [← Real.exp_add]
    convert Real.exp_log hkpos using 1; congr 1; ring
  rw [hexp] at hmul
  have hid : tupleDensity (branchCount ell) * (k : ℝ) / (6 * ((branchCount ell : ℝ) + 1)) =
      (k : ℝ) / (12000 * (branchCount ell : ℝ) * ((branchCount ell : ℝ) + 1) * Real.log (branchCount ell : ℝ)) := by
    unfold tupleDensity
    field_simp
    ring
  rw [hid]
  apply (lt_div_iff₀ hdenpos).mpr
  simpa only [mul_comm] using hmul

end PerfectPowers
