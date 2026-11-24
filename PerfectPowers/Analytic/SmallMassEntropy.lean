module

public import PerfectPowers.Basic.Parameters
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The uniform entropy error in the mass-increment argument

The bound `0.01` is deliberately looser than the draft's `0.007`. It still
leaves enough room for the same `0.1` mass increment after the prime-counting
and density losses. All bounds here are finite inequalities uniform in `m`.
-/

public section

namespace PerfectPowers

theorem log_ge_one_of_four_le {m : ℕ} (hm : 4 ≤ m) : 1 ≤ Real.log (m : ℝ) := by
  have hlog : Real.log 4 ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  rw [Real.log_four_eq] at hlog
  linarith [Real.log_two_gt_d9]

theorem rho_pos {m : ℕ} (hm : 4 ≤ m) : 0 < rho m := by
  unfold rho
  exact one_div_pos.mpr (mul_pos (by norm_num) (by linarith [log_ge_one_of_four_le hm]))

theorem rho_le_one_thousandth {m : ℕ} (hm : 4 ≤ m) : rho m ≤ 1 / 1000 := by
  unfold rho
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000)
  nlinarith [log_ge_one_of_four_le hm]

theorem mass_entropy_mono {m y r : ℝ} (hm : 0 < m) (hy : 0 < y) (hr : 0 < r)
    (hyr : y ≤ r) (hrm : r ≤ m) :
    y * (Real.log (m / y) + 1) ≤ r * (Real.log (m / r) + 1) := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hr hy)
  rw [Real.log_div hr.ne' hy.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hy.le
  have hid : y * (r / y - 1) = r - y := by field_simp
  rw [hid] at hmul
  have hmono : 0 ≤ Real.log m - Real.log r :=
    sub_nonneg.mpr (Real.log_le_log hr hrm)
  have hcross := mul_nonneg (sub_nonneg.mpr hyr) hmono
  rw [Real.log_div hm.ne' hy.ne', Real.log_div hm.ne' hr.ne']
  nlinarith

theorem rho_entropy_le_one_hundredth {m : ℕ} (hm : 4 ≤ m) :
    rho m * (Real.log ((m : ℝ) / rho m) + 1) ≤ 1 / 100 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hL : 1 ≤ Real.log (m : ℝ) := log_ge_one_of_four_le hm
  have hL0 : 0 < Real.log (m : ℝ) := by linarith
  have h1000 : Real.log 1000 ≤ 7 := by
    rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow, Real.log_ten_eq]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlogL := Real.log_le_sub_one_of_pos hL0
  have hρ : 0 < rho m := rho_pos hm
  rw [Real.log_div hmR.ne' hρ.ne']
  have hlogρ : Real.log (rho m) = -Real.log 1000 - Real.log (Real.log (m : ℝ)) := by
    rw [rho, Real.log_div (by norm_num) (by positivity), Real.log_one,
      Real.log_mul (by norm_num) hL0.ne']
    ring
  rw [hlogρ]
  unfold rho
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < 1000 * Real.log (m : ℝ))).mpr
  nlinarith

theorem small_mass_entropy_le {m : ℕ} (hm : 4 ≤ m) {y : ℝ}
    (hy : 0 < y) (hyρ : y ≤ rho m) :
    y * (Real.log ((m : ℝ) / y) + 1) ≤ 1 / 100 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hρm : rho m ≤ (m : ℝ) := by
    have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
    linarith [rho_le_one_thousandth hm]
  exact (mass_entropy_mono hmR hy (rho_pos hm) hyρ hρm).trans (rho_entropy_le_one_hundredth hm)

end PerfectPowers
