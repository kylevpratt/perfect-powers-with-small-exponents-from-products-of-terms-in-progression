module

public import PerfectPowers.Analytic.FactorialBounds
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Uniform factorial deficits for the two mass estimates

The weighted estimate is shared by Lemmas 5.3 and 5.5. The initial-mass
estimate is its specialization to `P = 1` and `delta = 0`, so the same
log-factorial and limiting arguments are proved only once.
-/

public section

open Filter

namespace PerfectPowers

theorem weighted_factorial_square_deficit_bound {k R P : ℕ} (hk : 1 ≤ k) (hP : 0 < P)
    (hfac : P * (k + R).factorial ≤ k.factorial ^ 2) :
    Real.log (P : ℝ) + 2 * (k : ℝ) * Real.log 2 ≤
      ((k : ℝ) - R) * (Real.log (k : ℝ) + Real.log 2) + 2 * Real.log (k : ℝ) + 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsumpos : (0 : ℝ) < (k : ℝ) + R := by positivity
  have hfacR : (P : ℝ) * ((k + R).factorial : ℝ) ≤ (k.factorial : ℝ) ^ 2 := by exact_mod_cast hfac
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (P : ℝ) * (k + R).factorial) hfacR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hmain : Real.log (P : ℝ) +
      (((k : ℝ) + R) * Real.log ((k : ℝ) + R) - ((k : ℝ) + R)) ≤
      2 * ((k : ℝ) * Real.log (k : ℝ) - k + Real.log (k : ℝ) + 1) := by
    have hlo := log_factorial_lower (k + R)
    have hhi := log_factorial_upper hk
    simp only [Nat.cast_add] at hlo
    linarith
  have ht := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < 2 * k) hsumpos)
  rw [Real.log_div (by positivity) hsumpos.ne', Real.log_mul (by norm_num) hkpos.ne'] at ht
  have htm := mul_le_mul_of_nonneg_left ht hsumpos.le
  have hquot : ((k : ℝ) + R) * (2 * (k : ℝ) / ((k : ℝ) + R) - 1) =
      2 * (k : ℝ) - ((k : ℝ) + R) := by field_simp
  rw [hquot] at htm
  nlinarith

/-- One threshold works for every mass parameter, product, and factorial index. -/
theorem eventually_weighted_factorial_deficit :
    ∀ᶠ k : ℕ in atTop, ∀ (R P : ℕ) (δ : ℝ), 0 < P →
      P * (k + R).factorial ≤ k.factorial ^ 2 →
      0 ≤ δ → δ ≤ Real.log (k : ℝ) / 1000 →
      (δ - 1 / 100) * (k : ℝ) ≤ Real.log (P : ℝ) →
      (R : ℝ) ≤ (k : ℝ) - (δ + 27 / 20) * ((k : ℝ) / Real.log (k : ℝ)) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hilog := tendsto_inv_atTop_zero.comp hlog
  have hik := tendsto_inv_atTop_zero.comp hcast
  have hratio : Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcast
  let B : ℝ := 27 / 20 + 1 / 100 + Real.log 2 / 1000
  have ht : Tendsto
      (fun k : ℕ => B + ((27 / 20 : ℝ) * Real.log 2) * (Real.log (k : ℝ))⁻¹ +
        2 * (Real.log (k : ℝ) / (k : ℝ)) + 2 * (k : ℝ)⁻¹) atTop (nhds B) := by
    have hc : Tendsto (fun _ : ℕ => B) atTop (nhds B) := tendsto_const_nhds
    simpa using ((hc.add (hilog.const_mul ((27 / 20 : ℝ) * Real.log 2))).add
      (hratio.const_mul 2)).add (hik.const_mul 2)
  have hmargin : B < 2 * Real.log 2 := by
    dsimp [B]
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  filter_upwards [ht.eventually_lt_const hmargin, eventually_ge_atTop (2 : ℕ)] with k hb hk
  intro R P δ hP hfac hδ0 hδ hmass
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδL : δ / Real.log (k : ℝ) ≤ 1 / 1000 := by
    apply (div_le_iff₀ hLpos).mpr
    linarith
  have hδcorr := mul_le_mul_of_nonneg_right hδL (mul_nonneg hlog2.le hkpos.le)
  have hbscale := mul_lt_mul_of_pos_right hb hkpos
  have hid : (B + ((27 / 20 : ℝ) * Real.log 2) * (Real.log (k : ℝ))⁻¹ +
        2 * (Real.log (k : ℝ) / (k : ℝ)) + 2 * (k : ℝ)⁻¹) * (k : ℝ) =
      B * (k : ℝ) + (27 / 20 : ℝ) * Real.log 2 * ((k : ℝ) / Real.log (k : ℝ)) +
        2 * Real.log (k : ℝ) + 2 := by field_simp [hkpos.ne', hLpos.ne']
  rw [hid] at hbscale
  dsimp [B] at hbscale
  have hscaled : (δ + 27 / 20) * ((k : ℝ) / Real.log (k : ℝ)) *
      (Real.log (k : ℝ) + Real.log 2) + 2 * Real.log (k : ℝ) + 2 <
      (δ + 2 * Real.log 2 - 1 / 100) * (k : ℝ) := by
    have heq : (δ + 27 / 20) * ((k : ℝ) / Real.log (k : ℝ)) *
        (Real.log (k : ℝ) + Real.log 2) =
      δ * (k : ℝ) + (27 / 20 : ℝ) * (k : ℝ) +
        (δ / Real.log (k : ℝ)) * (Real.log 2 * (k : ℝ)) +
        (27 / 20 : ℝ) * Real.log 2 * ((k : ℝ) / Real.log (k : ℝ)) := by
      field_simp [hLpos.ne']
      ring
    rw [heq]
    nlinarith
  have hdef := weighted_factorial_square_deficit_bound (by omega : 1 ≤ k) hP hfac
  by_contra hn
  have hgap : (k : ℝ) - R < (δ + 27 / 20) * ((k : ℝ) / Real.log (k : ℝ)) := by linarith
  have hmul := mul_lt_mul_of_pos_right hgap (by positivity : 0 < Real.log (k : ℝ) + Real.log 2)
  nlinarith

/-- Initial mass needs only the unweighted specialization. -/
theorem eventually_factorial_square_deficit :
    ∀ᶠ k : ℕ in atTop, ∀ R : ℕ, (k + R).factorial ≤ k.factorial ^ 2 →
      (R : ℝ) ≤ (k : ℝ) - (27 / 20 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) := by
  filter_upwards [eventually_weighted_factorial_deficit, eventually_ge_atTop (1 : ℕ)] with k hk hk1
  intro R hfac
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  have hmass : ((0 : ℝ) - 1 / 100) * (k : ℝ) ≤ Real.log (1 : ℝ) := by
    rw [Real.log_one]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  simpa using hk R 1 0 (by norm_num) (by simpa using hfac) le_rfl
    (div_nonneg hlog (by norm_num)) (by simpa only [Nat.cast_one] using hmass)

end PerfectPowers
