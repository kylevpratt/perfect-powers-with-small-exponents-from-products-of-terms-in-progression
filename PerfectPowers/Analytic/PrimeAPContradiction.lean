module

public import PerfectPowers.Basic.Definitions
import Mathlib.Tactic

/-! # The finite numerical contradiction used with Lemma 3.3 -/

public section

namespace PerfectPowers

theorem prime_weight_estimate_contradiction {k : ℕ} {S : Finset ℕ}
    {C x R θ M : ℝ} (hk : 5 ≤ k) (hC : 0 ≤ C) (hR : 0 < R)
    (hR2 : R ^ 2 = (Real.log (k : ℝ)) ^ 3)
    (hcost : 84 * C + 24 * R < (Real.log (k : ℝ)) ^ 2)
    (hxlo : (k : ℝ) ≤ x) (hxhi : x ≤ 7 * (k : ℝ) * R) (hxquad : x ≤ (k : ℝ) ^ 2)
    (hdense : VeryDense k S)
    (hθ : θ ≤ ((k : ℝ) - S.card) * Real.log x)
    (herr : |θ - M| ≤ C * x / (Real.log x) ^ 5)
    (hmain : (k : ℝ) / (12 * R) ≤ M) : False := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hxpos : 0 < x := lt_of_lt_of_le hkpos hxlo
  have hloglo : Real.log (k : ℝ) ≤ Real.log x := Real.log_le_log hkpos hxlo
  have hloghi : Real.log x ≤ 2 * Real.log (k : ℝ) := by
    have h := Real.log_le_log hxpos hxquad
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hlogxpos : 0 < Real.log x := lt_of_lt_of_le hLpos hloglo
  have hmissing : (k : ℝ) - S.card ≤ (k : ℝ) / (Real.log (k : ℝ)) ^ 3 := by
    change (k : ℝ) - (k : ℝ) / (Real.log (k : ℝ)) ^ 3 ≤ S.card at hdense
    linarith
  have hupper : θ ≤ 2 * (k : ℝ) / (Real.log (k : ℝ)) ^ 2 := by
    calc
      θ ≤ ((k : ℝ) - S.card) * Real.log x := hθ
      _ ≤ ((k : ℝ) / (Real.log (k : ℝ)) ^ 3) * Real.log x :=
        mul_le_mul_of_nonneg_right hmissing hlogxpos.le
      _ ≤ ((k : ℝ) / (Real.log (k : ℝ)) ^ 3) * (2 * Real.log (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hloghi (div_nonneg hkpos.le (pow_nonneg hLpos.le 3))
      _ = _ := by field_simp
  have herror : C * x / (Real.log x) ^ 5 ≤ 7 * C * (k : ℝ) * R / (Real.log (k : ℝ)) ^ 5 := by
    have hnum : C * x ≤ 7 * C * (k : ℝ) * R := by nlinarith
    have hden : (Real.log (k : ℝ)) ^ 5 ≤ (Real.log x) ^ 5 := by gcongr
    exact div_le_div₀ (by positivity) hnum (by positivity) hden
  have hcostScaled := mul_lt_mul_of_pos_right hcost (mul_pos hkpos (pow_pos hLpos 3))
  have hid : (2 * (k : ℝ) / (Real.log (k : ℝ)) ^ 2 +
      7 * C * (k : ℝ) * R / (Real.log (k : ℝ)) ^ 5) * (12 * R) =
      ((24 * R + 84 * C) * (k : ℝ) * (Real.log (k : ℝ)) ^ 3) / (Real.log (k : ℝ)) ^ 5 := by
    field_simp [hLpos.ne']
    nlinarith [hR2]
  have hstrict : 2 * (k : ℝ) / (Real.log (k : ℝ)) ^ 2 +
      7 * C * (k : ℝ) * R / (Real.log (k : ℝ)) ^ 5 < (k : ℝ) / (12 * R) := by
    apply (lt_div_iff₀ (by positivity : 0 < 12 * R)).mpr
    rw [hid]
    apply (div_lt_iff₀ (pow_pos hLpos 5)).mpr
    nlinarith
  have hlow := (abs_le.mp herr).1
  linarith

end PerfectPowers
