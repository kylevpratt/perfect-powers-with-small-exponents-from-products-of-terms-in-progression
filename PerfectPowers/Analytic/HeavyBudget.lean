module

public import PerfectPowers.Analytic.CurveBudget
public import PerfectPowers.Analytic.LogBlocks
public import PerfectPowers.Analytic.BranchRange
import Mathlib.Tactic

/-! # Uniform numerical bounds for the heavy-fiber counting argument -/

public section

open Filter

namespace PerfectPowers

theorem eventually_heavy_counting_budget :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell →
      ((branchCount ell : ℝ) + 1) ^ 2 *
          (((3 * (logBlockSize k) ^ branchCount ell : ℕ) : ℝ) *
            External.remondBound (branchCount ell) (3 * (logBlockSize k + 1) ^ branchCount ell)) +
        (branchCount ell : ℝ) * ((branchCount ell : ℝ) + 1) * ((k : ℝ) / logBlockSize k) *
          (1 + Real.log (k : ℝ)) ≤ (1 / 50 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hT : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ))) atTop atTop := Real.tendsto_log_atTop.comp hx
  have hlimT := (isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlimx := (isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0 : ℝ) < 3 / 4)).tendsto_div_nhds_zero
  have hsmallT : ∀ᶠ k : ℕ in atTop,
      (Real.log (Real.log (k : ℝ))) ^ 2 / Real.exp (Real.log (Real.log (k : ℝ))) < 1 / 400 := by
    have h := hT.eventually (hlimT.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 400))
    simpa only [one_mul] using h
  have hsmallx : ∀ᶠ k : ℕ in atTop,
      (Real.log (k : ℝ)) ^ 3 / Real.exp ((3 / 4 : ℝ) * Real.log (k : ℝ)) < 1 / 100 := by
    exact hx.eventually (hlimx.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 100))
  filter_upwards [eventually_uniform_curve_family_budget, eventually_branchCount_le_loglog,
    hsmallT, hsmallx] with k hcurve hmT hST hSx
  intro ell hell
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := hell.1; omega)
  have hlogpos := hell.log_pos
  have hlog1 : 1 ≤ Real.log (k : ℝ) := by
    linarith [hell.loglog_ge_thirty_two, Real.log_le_sub_one_of_pos hlogpos]
  obtain ⟨hL, hLlow, hLlog⟩ := logBlockSize_properties hell
  have hcurveL := hcurve ell hell (logBlockSize k) hL hLlog
  have hpow : (logBlockSize k) ^ branchCount ell ≤ (logBlockSize k) ^ (2 * branchCount ell) :=
    Nat.pow_le_pow_right hL (by omega)
  have hcount : ((3 * (logBlockSize k) ^ branchCount ell : ℕ) : ℝ) ≤
      (3 * (logBlockSize k) ^ (2 * branchCount ell) : ℕ) := by exact_mod_cast Nat.mul_le_mul_left 3 hpow
  have hremond0 : 0 ≤ External.remondBound (branchCount ell) (3 * (logBlockSize k + 1) ^ branchCount ell) := by
    unfold External.remondBound
    exact (Real.exp_pos _).le
  have hcountCurve := (mul_le_mul_of_nonneg_right hcount hremond0).trans hcurveL
  have hmPlus : (branchCount ell : ℝ) + 1 ≤ Real.log (k : ℝ) := by
    linarith [hmT ell hell, Real.log_le_sub_one_of_pos hlogpos]
  have hmSq : ((branchCount ell : ℝ) + 1) ^ 2 ≤ (Real.log (k : ℝ)) ^ 2 := by
    gcongr
  have hpoly : 100 * (Real.log (k : ℝ)) ^ 3 ≤ Real.exp ((3 / 4 : ℝ) * Real.log (k : ℝ)) := by
    have h := (div_lt_iff₀ (Real.exp_pos _)).mp hSx
    linarith
  have hpolyMul := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (Real.log (k : ℝ) / 4)).le
  have hexp : Real.exp ((3 / 4 : ℝ) * Real.log (k : ℝ)) *
      Real.exp (Real.log (k : ℝ) / 4) = (k : ℝ) := by
    rw [← Real.exp_add]
    convert Real.exp_log hkpos using 1; congr 1; ring
  rw [hexp] at hpolyMul
  have hcurvePart : ((branchCount ell : ℝ) + 1) ^ 2 *
      (((3 * (logBlockSize k) ^ branchCount ell : ℕ) : ℝ) *
        External.remondBound (branchCount ell) (3 * (logBlockSize k + 1) ^ branchCount ell)) ≤
      ((1 / 100 : ℝ) * (k : ℝ)) / Real.log (k : ℝ) := by
    apply (le_div_iff₀ hlogpos).mpr
    have hmul1 := mul_le_mul_of_nonneg_left hcountCurve (sq_nonneg ((branchCount ell : ℝ) + 1))
    have hmul2 := mul_le_mul_of_nonneg_right hmSq (Real.exp_pos (Real.log (k : ℝ) / 4)).le
    have hmul3 := mul_le_mul_of_nonneg_right (hmul1.trans hmul2) hlogpos.le
    nlinarith
  have hTbudget : 400 * (Real.log (Real.log (k : ℝ))) ^ 2 ≤ Real.log (k : ℝ) := by
    rw [Real.exp_log hlogpos] at hST
    have h := (div_lt_iff₀ hlogpos).mp hST
    linarith
  have hm1 : (1 : ℝ) ≤ branchCount ell := by
    have h := (branchCount_properties hell.2.1).1
    exact_mod_cast (show 1 ≤ branchCount ell by omega)
  have hblock := block_remainder_le hkpos hlog1 hLlow hm1 (hmT ell hell) hTbudget
  rw [mul_div_assoc] at hcurvePart
  linarith

end PerfectPowers
