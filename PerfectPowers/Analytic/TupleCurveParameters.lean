module

public import PerfectPowers.Analytic.TupleThreshold
public import PerfectPowers.Analytic.BranchRange
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Curve boxes for the common-divisor tuples in Proposition 3.5 -/

@[expose] public section

open Filter

namespace PerfectPowers

noncomputable def tupleEta (m : ℕ) : ℝ := tupleDensity m / 3 * Real.exp (-5 * tupleScale m)

noncomputable def tupleSide (m : ℕ) : ℕ :=
  ⌈(3 / tupleDensity m) * Real.exp (5 * tupleScale m)⌉₊

theorem tupleEta_pos {m : ℕ} (hm : 2 ≤ m) : 0 < tupleEta m := by
  unfold tupleEta
  exact mul_pos (div_pos (tupleDensity_pos hm) (by norm_num)) (Real.exp_pos _)

theorem tupleScale_ge_m {m : ℕ} (hm : 2 ≤ m) : (m : ℝ) ≤ tupleScale m := by
  rw [← tupleDensity_scale]
  apply (le_div_iff₀ (tupleDensity_pos hm)).mpr
  have h := mul_le_mul_of_nonneg_left (tupleDensity_le_one hm) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  simpa only [mul_one] using h

theorem tupleSide_pos {m : ℕ} (hm : 2 ≤ m) : 1 ≤ tupleSide m :=
  Nat.one_le_ceil_iff.mpr (mul_pos (div_pos (by norm_num) (tupleDensity_pos hm)) (Real.exp_pos _))

theorem tupleEta_mul_side_ge_one {m : ℕ} (hm : 2 ≤ m) : 1 ≤ tupleEta m * (tupleSide m : ℝ) := by
  have hceil := Nat.le_ceil ((3 / tupleDensity m) * Real.exp (5 * tupleScale m))
  have h := mul_le_mul_of_nonneg_left hceil (tupleEta_pos hm).le
  have hid : tupleEta m * ((3 / tupleDensity m) * Real.exp (5 * tupleScale m)) = 1 := by
    unfold tupleEta
    rw [show -5 * tupleScale m = -(5 * tupleScale m) by ring, Real.exp_neg]
    field_simp [(tupleDensity_pos hm).ne']
  rwa [hid] at h

theorem tupleSide_log_le_ten_scale {m : ℕ} (hm : 2 ≤ m) :
    Real.log ((tupleSide m : ℝ) + 1) ≤ 10 * tupleScale m := by
  let A : ℝ := (3 / tupleDensity m) * Real.exp (5 * tupleScale m)
  have hc : 0 < tupleDensity m := tupleDensity_pos hm
  have hu : 0 < tupleScale m := tupleScale_pos hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hu2 : 2 ≤ tupleScale m := by
    have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith [tupleScale_ge_m hm]
  have hrecip : 1 / tupleDensity m ≤ tupleScale m := by
    rw [← tupleDensity_scale]
    exact div_le_div_of_nonneg_right hm1 hc.le
  have hthree : 3 ≤ 3 / tupleDensity m := by
    apply (le_div_iff₀ hc).mpr
    linarith [tupleDensity_le_one hm]
  have hE : 1 ≤ Real.exp (5 * tupleScale m) := Real.one_le_exp_iff.mpr (by positivity)
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hceil : (tupleSide m : ℝ) < A + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ A)
  have hside : (tupleSide m : ℝ) + 1 ≤ 3 * A := by linarith
  have hlog := Real.log_le_log (by positivity : 0 < (tupleSide m : ℝ) + 1) hside
  rw [Real.log_mul (by norm_num) (by linarith : A ≠ 0)] at hlog
  have hlogA : Real.log A = Real.log (3 / tupleDensity m) + 5 * tupleScale m := by
    dsimp [A]
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
  rw [hlogA] at hlog
  have hlogQ : Real.log (3 / tupleDensity m) ≤ 3 / tupleDensity m := by
    linarith [Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 3) hc)]
  have hQ := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 3)
  rw [mul_one_div] at hQ
  linarith [Real.log_three_lt_d9]

theorem quotient_le_tupleSide {k f m : ℕ} (hm : 2 ≤ m)
    (hf : tupleEta m * (k : ℝ) < (f : ℝ)) : k / f ≤ tupleSide m := by
  have hside := tupleEta_mul_side_ge_one hm
  have hspos : (0 : ℝ) < tupleSide m := by exact_mod_cast tupleSide_pos hm
  have hfpos : (0 : ℝ) < f := lt_of_le_of_lt (mul_nonneg (tupleEta_pos hm).le (Nat.cast_nonneg k)) hf
  have hmul := mul_lt_mul_of_pos_right hf hspos
  have hmul2 := mul_le_mul_of_nonneg_right hside (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hratio : (k : ℝ) / (f : ℝ) ≤ (tupleSide m : ℝ) := by
    apply (div_le_iff₀ hfpos).mpr
    nlinarith
  have hfloor : ((k / f : ℕ) : ℝ) ≤ (tupleSide m : ℝ) := Nat.cast_div_le.trans hratio
  exact_mod_cast hfloor

theorem eventually_tupleSide_log_bound :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell →
      Real.log ((tupleSide (branchCount ell) : ℝ) + 1) ≤ 4 * Real.log (Real.log (k : ℝ)) := by
  filter_upwards [eventually_uniform_tupleScale (by norm_num : (0 : ℝ) < 1 / 4)] with k hk
  intro ell hell
  have hm : 2 ≤ branchCount ell := by have := (branchCount_properties hell.2.1).1; omega
  linarith [tupleSide_log_le_ten_scale hm, hk ell hell, hell.loglog_ge_thirty_two]

theorem eventually_trivial_count_le_tuple_density :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell →
      (k : ℝ) / (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) ≤ tupleDensity (branchCount ell) * (k : ℝ) := by
  filter_upwards [eventually_uniform_tupleScale (by norm_num : (0 : ℝ) < 1)] with k hk
  intro ell hell
  have hm : 2 ≤ branchCount ell := by have := (branchCount_properties hell.2.1).1; omega
  have hmR : (1 : ℝ) ≤ branchCount ell := by exact_mod_cast (show 1 ≤ branchCount ell by omega)
  have hlog1 : 1 ≤ Real.log (k : ℝ) := by
    linarith [hell.loglog_ge_thirty_two, Real.log_le_sub_one_of_pos hell.log_pos]
  have hpow : Real.log (k : ℝ) ≤ (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hscale : tupleScale (branchCount ell) ≤ (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) := by
    linarith [hk ell hell, Real.log_le_sub_one_of_pos hell.log_pos]
  have hmul := mul_le_mul_of_nonneg_left hscale (tupleDensity_pos hm).le
  have hid : tupleDensity (branchCount ell) * tupleScale (branchCount ell) = (branchCount ell : ℝ) := by
    rw [← tupleDensity_scale]
    field_simp [(tupleDensity_pos hm).ne']
  rw [hid] at hmul
  have hone : 1 ≤ tupleDensity (branchCount ell) * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) := by linarith
  have hbound : 1 / (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) ≤ tupleDensity (branchCount ell) :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hell.log_pos _)).mpr hone
  have h := mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  simpa only [one_div_mul_eq_div] using h

end PerfectPowers
