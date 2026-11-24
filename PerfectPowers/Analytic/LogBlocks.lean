module

public import PerfectPowers.Analytic.ExponentRange
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! # Integer block lengths with controlled logarithmic size -/

@[expose] public section

namespace PerfectPowers

noncomputable def logBlockSize (k : ℕ) : ℕ := ⌈(Real.log (k : ℝ)) ^ 3⌉₊

theorem logBlockSize_properties {k ell : ℕ} (h : SmallExponent k ell) :
    1 ≤ logBlockSize k ∧ (Real.log (k : ℝ)) ^ 3 ≤ (logBlockSize k : ℝ) ∧
      Real.log ((logBlockSize k : ℝ) + 1) ≤ 4 * Real.log (Real.log (k : ℝ)) := by
  have hx : 0 < Real.log (k : ℝ) := h.log_pos
  have hx2 : 2 ≤ Real.log (k : ℝ) := by
    linarith [h.loglog_ge_thirty_two, Real.log_le_sub_one_of_pos hx]
  have hceil : (logBlockSize k : ℝ) < (Real.log (k : ℝ)) ^ 3 + 1 :=
    Nat.ceil_lt_add_one (pow_nonneg hx.le 3)
  refine ⟨Nat.one_le_ceil_iff.mpr (pow_pos hx 3), Nat.le_ceil _, ?_⟩
  have hcube : (8 : ℝ) ≤ (Real.log (k : ℝ)) ^ 3 := by
    have hpow : (2 : ℝ) ^ 3 ≤ (Real.log (k : ℝ)) ^ 3 := by gcongr
    norm_num at hpow
    exact hpow
  have hmul := mul_le_mul_of_nonneg_right hx2 (pow_nonneg hx.le 3)
  have hbound : (logBlockSize k : ℝ) + 1 ≤ (Real.log (k : ℝ)) ^ 4 := by
    nlinarith
  calc
    _ ≤ Real.log ((Real.log (k : ℝ)) ^ 4) := Real.log_le_log (by positivity) hbound
    _ = _ := by rw [Real.log_pow]; norm_num

theorem block_remainder_le {k m L : ℕ} {T : ℝ}
    (hkpos : (0 : ℝ) < k) (hx : 1 ≤ Real.log (k : ℝ))
    (hL : (Real.log (k : ℝ)) ^ 3 ≤ (L : ℝ))
    (hm : (1 : ℝ) ≤ m) (hmT : (m : ℝ) ≤ T)
    (hTbudget : 400 * T ^ 2 ≤ Real.log (k : ℝ)) :
    (m : ℝ) * ((m : ℝ) + 1) * ((k : ℝ) / L) * (1 + Real.log (k : ℝ)) ≤
      (1 / 100 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) := by
  have hxpos : 0 < Real.log (k : ℝ) := by linarith
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (pow_pos hxpos 3) hL
  have hT0 : 0 ≤ T := by linarith
  have hM : (m : ℝ) * ((m : ℝ) + 1) ≤ 2 * T ^ 2 := by nlinarith
  have hMx := mul_le_mul_of_nonneg_right hM (mul_nonneg (by linarith : 0 ≤ 1 + Real.log (k : ℝ)) hxpos.le)
  have hTwice : 2 * T ^ 2 * ((1 + Real.log (k : ℝ)) * Real.log (k : ℝ)) ≤
      4 * T ^ 2 * (Real.log (k : ℝ)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (show 1 + Real.log (k : ℝ) ≤ 2 * Real.log (k : ℝ) by linarith)
      (mul_nonneg (by positivity : 0 ≤ 2 * T ^ 2) hxpos.le)
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hTbudget (sq_nonneg (Real.log (k : ℝ)))
  have hcoeff : 100 * ((m : ℝ) * ((m : ℝ) + 1) * (1 + Real.log (k : ℝ)) * Real.log (k : ℝ)) ≤ L := by
    nlinarith
  have hratio : ((m : ℝ) * ((m : ℝ) + 1) * (1 + Real.log (k : ℝ)) * Real.log (k : ℝ)) / L ≤ 1 / 100 := by
    apply (div_le_iff₀ hLpos).mpr
    linarith
  have hmul := mul_le_mul_of_nonneg_right hratio hkpos.le
  have htarget : (m : ℝ) * ((m : ℝ) + 1) * ((k : ℝ) / L) * (1 + Real.log (k : ℝ)) ≤
      ((1 / 100 : ℝ) * (k : ℝ)) / Real.log (k : ℝ) := by
    apply (le_div_iff₀ hxpos).mpr
    convert hmul using 1; ring
  simpa only [mul_div_assoc] using htarget

end PerfectPowers
