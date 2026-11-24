module

public import PerfectPowers.Analytic.UniformExponent
public import PerfectPowers.External.Remond
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# A uniform budget for finitely many low-height curves

This estimate contains no rational-point assumption: it only bounds the
explicit expression in Remond's result. The exponent and the coefficient
box may both vary. The logarithm of the box side is at most `4 log log k`.
-/

public section

open Filter

namespace PerfectPowers

theorem eventually_curve_cost_bound :
    ∀ᶠ T : ℝ in atTop, 10 * T ^ 2 + 36 * T ^ 4 * Real.exp (T / 4) ≤ Real.exp (T / 2) := by
  have h2 := (isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h4 := (isLittleO_pow_exp_pos_mul_atTop 4 (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  filter_upwards [h2.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 20),
    h4.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 72)] with T hT2 hT4
  have htwo : 10 * T ^ 2 ≤ (1 / 2 : ℝ) * Real.exp (T / 2) := by
    have h := (div_lt_iff₀ (Real.exp_pos ((1 / 2 : ℝ) * T))).mp hT2
    have hid : (1 / 2 : ℝ) * T = T / 2 := by ring
    rw [hid] at h
    linarith
  have hfour : 36 * T ^ 4 ≤ (1 / 2 : ℝ) * Real.exp (T / 4) := by
    have h := (div_lt_iff₀ (Real.exp_pos ((1 / 4 : ℝ) * T))).mp hT4
    have hid : (1 / 4 : ℝ) * T = T / 4 := by ring
    rw [hid] at h
    linarith
  have hfourMul := mul_le_mul_of_nonneg_right hfour (Real.exp_pos (T / 4)).le
  have hexp : Real.exp (T / 4) * Real.exp (T / 4) = Real.exp (T / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

theorem curve_family_budget_of_parameters {m L : ℕ} {T : ℝ}
    (hT : 8 ≤ T) (hmT : (m : ℝ) ≤ T)
    (hpow : (m : ℝ) ^ 4 * Real.log 5 ≤ T / 4)
    (hL : 1 ≤ L) (hlogL : Real.log ((L : ℝ) + 1) ≤ 4 * T)
    (hcost : 10 * T ^ 2 + 36 * T ^ 4 * Real.exp (T / 4) ≤ Real.exp (T / 2)) :
    ((3 * L ^ (2 * m) : ℕ) : ℝ) * External.remondBound m (3 * (L + 1) ^ m) ≤
      Real.exp (Real.exp T / 4) := by
  have hT0 : 0 ≤ T := by linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hH : (3 : ℝ) ≤ (3 * (L + 1) ^ m : ℕ) := by
    exact_mod_cast (show 3 ≤ 3 * (L + 1) ^ m by have := Nat.one_le_pow m (L + 1) (by omega); omega)
  have hHpos : (0 : ℝ) < (3 * (L + 1) ^ m : ℕ) := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by linarith [Real.log_three_lt_d9]
  have hlogL' : Real.log (L : ℝ) ≤ 4 * T :=
    (Real.log_le_log hLpos (by linarith)).trans hlogL
  have hlogCount : Real.log ((3 * L ^ (2 * m) : ℕ) : ℝ) ≤ 10 * T ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num only [Nat.cast_ofNat, Nat.cast_mul]
    have hmul := mul_le_mul_of_nonneg_left hlogL' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm0)
    nlinarith
  have hlogHeight : Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ) ≤ 6 * T ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hmul := mul_le_mul_of_nonneg_left hlogL hm0
    nlinarith
  have hlogHeightOne : 1 ≤ Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ) := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hH
    linarith [Real.log_three_gt_d9]
  have hloglog : 0 ≤ Real.log (Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ)) := Real.log_nonneg hlogHeightOne
  have hloglogBound : Real.log (Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ)) ≤
      Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ))]
  have hheightProduct : Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ) *
      Real.log (Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ)) ≤ 36 * T ^ 4 := by
    have hmul := mul_le_mul hlogHeight hlogHeight
      (by linarith : 0 ≤ Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ)) (by positivity : 0 ≤ 6 * T ^ 2)
    have hmul' := mul_le_mul_of_nonneg_left hloglogBound (by linarith : 0 ≤ Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ))
    nlinarith
  have hbase : (5 : ℝ) ^ (m ^ 4) ≤ Real.exp (T / 4) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5)]
    apply Real.exp_le_exp.mpr
    simpa only [Nat.cast_pow, mul_comm] using hpow
  have hcountpos : (0 : ℝ) < (3 * L ^ (2 * m) : ℕ) := by positivity
  have hlogAll : Real.log (((3 * L ^ (2 * m) : ℕ) : ℝ) *
      External.remondBound m (3 * (L + 1) ^ m)) ≤ Real.exp (T / 2) := by
    rw [Real.log_mul hcountpos.ne' (by unfold External.remondBound; positivity),
      External.remondBound, Real.log_exp]
    have hprod := mul_le_mul hbase hheightProduct
      (mul_nonneg (by linarith : 0 ≤ Real.log ((3 * (L + 1) ^ m : ℕ) : ℝ)) hloglog)
      (Real.exp_pos (T / 4)).le
    nlinarith
  have hE : 4 ≤ Real.exp (T / 2) := by linarith [Real.add_one_le_exp (T / 2)]
  have hEsq : Real.exp (T / 2) * Real.exp (T / 2) = Real.exp T := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hinner : Real.exp (T / 2) ≤ Real.exp T / 4 := by nlinarith
  have hexp := Real.exp_le_exp.mpr (hlogAll.trans hinner)
  rw [Real.exp_log (mul_pos hcountpos (by unfold External.remondBound; positivity))] at hexp
  exact hexp

theorem eventually_uniform_curve_family_budget :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell → ∀ L : ℕ, 1 ≤ L →
      Real.log ((L : ℝ) + 1) ≤ 4 * Real.log (Real.log (k : ℝ)) →
      ((3 * L ^ (2 * branchCount ell) : ℕ) : ℝ) *
          External.remondBound (branchCount ell) (3 * (L + 1) ^ branchCount ell) ≤
        Real.exp (Real.log (k : ℝ) / 4) := by
  have hT : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_uniform_branchCount_fourth_power (by norm_num : (0 : ℝ) < 1 / 100),
    hT.eventually eventually_curve_cost_bound] with k hfour hcost
  intro ell hell L hL hlogL
  have hT32 := hell.loglog_ge_thirty_two
  have hm : 1 ≤ branchCount ell := by have := (branchCount_properties hell.2.1).1; omega
  have hmR : (1 : ℝ) ≤ branchCount ell := by exact_mod_cast hm
  have hm14 : (branchCount ell : ℝ) ≤ (branchCount ell : ℝ) ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hmR (by norm_num : 1 ≤ 4)
  have hmT : (branchCount ell : ℝ) ≤ Real.log (Real.log (k : ℝ)) := by
    linarith [hfour ell hell]
  have hlog5 : Real.log 5 ≤ 2 := by linarith [Real.log_five_lt_d9]
  have hpow : (branchCount ell : ℝ) ^ 4 * Real.log 5 ≤ Real.log (Real.log (k : ℝ)) / 4 := by
    have h := mul_le_mul_of_nonneg_left hlog5 (pow_nonneg (Nat.cast_nonneg (branchCount ell)) 4)
    nlinarith [hfour ell hell]
  have h := curve_family_budget_of_parameters (by linarith : 8 ≤ Real.log (Real.log (k : ℝ)))
    hmT hpow hL hlogL hcost
  simpa only [Real.exp_log hell.log_pos] using h

end PerfectPowers
