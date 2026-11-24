module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# An explicit elementary prime-counting inequality

Chebyshev's theta bound and the elementary count of odd integers suffice for
the deletion argument for odd progressions. No prime-distribution input is used.
-/

public section

open MeasureTheory intervalIntegral

namespace PerfectPowers

theorem primeCounting_le_half_add_one (n : ℕ) :
    (Nat.primeCounting n : ℝ) ≤ (n : ℝ) / 2 + 1 := by
  by_cases hn : 2 ≤ n
  · have h := Nat.primeCounting_add_le (a := 2) (k := 2) (by decide) le_rfl (n - 2)
    have htwo : Nat.primeCounting 2 = 1 := by decide
    have htot : Nat.totient 2 = 1 := by decide
    rw [Nat.add_sub_of_le hn, htwo, htot, one_mul] at h
    have hdiv : 2 * Nat.primeCounting n ≤ n + 2 := by omega
    have hreal : (2 : ℝ) * Nat.primeCounting n ≤ n + 2 := by exact_mod_cast hdiv
    linarith
  · have hz : Nat.primeCounting n = 0 := Nat.primeCounting_eq_zero_iff.mpr (by omega)
    simp only [hz, Nat.cast_zero]
    positivity

theorem primeCounting_floor_le_half_add_one {x : ℝ} (hx : 0 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / 2 + 1 := by
  exact (primeCounting_le_half_add_one _).trans (by linarith [Nat.floor_le hx])

theorem primeCounting_mul_log_le {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x ≤
      Real.log 4 * x + x / 2 - 1 + Real.log (x / 2) := by
  have hx0 : 0 < x := by linarith
  have hmono : Monotone (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ)) := by
    intro a b hab
    change (Nat.primeCounting ⌊a⌋₊ : ℝ) ≤ Nat.primeCounting ⌊b⌋₊
    exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono hab)
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
    fun_prop
  have hleft : IntervalIntegrable
      (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) volume 2 x := by
    exact hmono.intervalIntegrable.mul_continuousOn (by
      intro t ht
      have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
      fun_prop)
  have hright : IntervalIntegrable (fun t : ℝ => 1 / 2 + t⁻¹) volume 2 x :=
    (intervalIntegrable_const).add hinv
  have hi : (∫ t in 2..x, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) ≤
      x / 2 - 1 + Real.log (x / 2) := by
    calc
      _ ≤ ∫ t in 2..x, (1 / 2 + t⁻¹) := by
        apply integral_mono_on hx hleft hright
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hc := primeCounting_floor_le_half_add_one ht0.le
        apply (div_le_iff₀ ht0).mpr
        rw [add_mul, inv_mul_cancel₀ ht0.ne']
        linarith
      _ = _ := by
        rw [integral_add intervalIntegrable_const hinv, intervalIntegral.integral_const,
          integral_inv_of_pos (by norm_num) hx0]
        simp only [smul_eq_mul]
        ring
  have heq := Chebyshev.theta_eq_primeCounting_mul_log_sub_integral hx
  have htheta := Chebyshev.theta_le_log4_mul_x hx0.le
  linarith

/-- The quantitative inequality needed to compare the retained odd terms with
the odd part of the factorial. -/
theorem primeCounting_log_two_mul_add_one_lt {k : ℕ} (hk : 2 ≤ k) :
    (Nat.primeCounting k : ℝ) * Real.log (2 * (k : ℝ)) + 1 <
      (1 + Real.log 4) * k := by
  have hLlo : (2 : ℝ) / 3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hLhi : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log k :=
    Real.log_mul (by norm_num) hk0.ne'
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  by_cases hlarge : 32 ≤ k
  · have hk32 : (32 : ℝ) ≤ k := by exact_mod_cast hlarge
    have hpi := primeCounting_mul_log_le (x := (k : ℝ)) (by exact_mod_cast hk)
    rw [Nat.floor_natCast] at hpi
    have hhalf := primeCounting_le_half_add_one k
    have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      norm_num
    have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) / 32 - 1 + 5 * Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (k : ℝ) / 32 by positivity)
      rw [Real.log_div hk0.ne' (by norm_num), hlog32] at h
      linarith
    rw [Real.log_div hk0.ne' (by norm_num), hfour] at hpi
    rw [hlog, hfour]
    have hLpos : 0 ≤ Real.log 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hhalf hLpos
    have hmargin := mul_pos (show 0 < (7 : ℝ) / 10 - Real.log 2 by linarith) hk0
    nlinarith
  · have hsmall : k < 32 := by omega
    have hnum : ∀ n : Fin 32, 2 ≤ n.val →
        3 * Nat.primeCounting n.val * (Nat.log 2 n.val + 2) * 7 + 30 < 70 * n.val := by
      decide +kernel
    have hn := hnum ⟨k, hsmall⟩ hk
    have hpow : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by decide) k
    have hpowR : (k : ℝ) < (2 : ℝ) ^ (Nat.log 2 k + 1) := by exact_mod_cast hpow
    have hlogbound : Real.log (2 * (k : ℝ)) ≤
        ((Nat.log 2 k + 2 : ℕ) : ℝ) * Real.log 2 := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * k)
        (show 2 * (k : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 k + 2) by
          rw [show Nat.log 2 k + 2 = (Nat.log 2 k + 1) + 1 by omega, pow_succ]
          linarith)
      simpa only [Real.log_pow] using h
    have hmul := mul_le_mul_of_nonneg_left hlogbound (Nat.cast_nonneg (Nat.primeCounting k) : (0 : ℝ) ≤ _)
    have hnR : (3 : ℝ) * Nat.primeCounting k * ((Nat.log 2 k + 2 : ℕ) : ℝ) * 7 + 30 < 70 * k := by
      exact_mod_cast hn
    have hcoeff : (0 : ℝ) ≤ (Nat.primeCounting k : ℝ) * ((Nat.log 2 k + 2 : ℕ) : ℝ) := by positivity
    have hmulL := mul_le_mul_of_nonneg_left hLhi.le hcoeff
    rw [hfour]
    have hmulK := mul_lt_mul_of_pos_right hLlo hk0
    nlinarith

end PerfectPowers
