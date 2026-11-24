module

public import PerfectPowers.Analytic.UniformExponent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Uniform applicability of the revised tuple lemma

The stronger double-exponential size condition still holds with one absolute
threshold, uniformly for every allowed exponent. No computable modulus is
claimed by the eventual statement.
-/

@[expose] public section

open Filter

namespace PerfectPowers

noncomputable def tupleScale (m : ℕ) : ℝ := 2000 * (m : ℝ) ^ 2 * Real.log (m : ℝ)

noncomputable def tupleDensity (m : ℕ) : ℝ := 1 / (2000 * (m : ℝ) * Real.log (m : ℝ))

theorem tupleDensity_pos {m : ℕ} (hm : 2 ≤ m) : 0 < tupleDensity m := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) (by linarith)) (Real.log_pos hmR))

theorem tupleDensity_le_one {m : ℕ} (hm : 2 ≤ m) : tupleDensity m ≤ 1 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hinv : (m : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hmR
  have hlog : (1 / 2 : ℝ) ≤ Real.log (m : ℝ) := by
    linarith [Real.one_sub_inv_le_log_of_pos hm0]
  have hden : 1 ≤ 2000 * (m : ℝ) * Real.log (m : ℝ) := by nlinarith
  exact (div_le_iff₀ (by linarith : 0 < 2000 * (m : ℝ) * Real.log (m : ℝ))).mpr
    (by simpa only [one_mul] using hden)

theorem tupleDensity_scale (m : ℕ) : (m : ℝ) / tupleDensity m = tupleScale m := by
  rw [tupleDensity, div_div_eq_mul_div, div_one, tupleScale]
  ring

theorem tupleScale_pos {m : ℕ} (hm : 2 ≤ m) : 0 < tupleScale m := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  exact mul_pos (mul_pos (by norm_num) (pow_pos (by linarith) _)) (Real.log_pos hmR)

theorem tupleScale_le_fourth_power {m : ℕ} (hm : 1 ≤ m) :
    tupleScale m ≤ 2000 * (m : ℝ) ^ 4 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : Real.log (m : ℝ) ≤ (m : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < m)]
  have hpow : (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 :=
    pow_le_pow_right₀ hmR (by norm_num)
  calc
    tupleScale m ≤ 2000 * (m : ℝ) ^ 2 * (m : ℝ) := by
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2000 * (m : ℝ) ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem eventually_uniform_tupleScale {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell →
      tupleScale (branchCount ell) ≤ ε * Real.log (Real.log (k : ℝ)) := by
  filter_upwards [eventually_uniform_branchCount_fourth_power (div_pos hε (by norm_num :
    (0 : ℝ) < 2000))] with k hk
  intro ell hell
  have hm : 1 ≤ branchCount ell := by have := (branchCount_properties hell.2.1).1; omega
  have h := mul_le_mul_of_nonneg_left (hk ell hell) (by norm_num : (0 : ℝ) ≤ 2000)
  have hbound := tupleScale_le_fourth_power hm
  nlinarith

theorem double_exponential_tuple_cost_bound {T u : ℝ}
    (hT : 8 ≤ T) (hu : 0 < u) (huT : u ≤ T / 8) :
    12 * u * (2 : ℝ) ^ (Real.exp (4 * u)) ≤ Real.exp (Real.exp T) := by
  let E := Real.exp (T / 2)
  have hE : 4 ≤ E := by
    have := Real.add_one_le_exp (T / 2)
    dsimp [E]
    linarith
  have hTE : T ≤ 2 * E := by
    have := Real.add_one_le_exp (T / 2)
    dsimp [E]
    linarith
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hexp : Real.exp (4 * u) ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hlogu : Real.log (12 * u) ≤ 12 * u := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 12 * u)]
  have hcostpos : 0 < 12 * u * (2 : ℝ) ^ (Real.exp (4 * u)) := by positivity
  have hlog : Real.log (12 * u * (2 : ℝ) ^ (Real.exp (4 * u))) ≤ Real.exp T := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    have hmul := mul_le_mul_of_nonneg_right hexp hlog2
    have hmul2 := mul_le_mul_of_nonneg_left hlog2le (Real.exp_pos (T / 2)).le
    have hEsq : E * E = Real.exp T := by
      dsimp [E]
      rw [← Real.exp_add]
      congr 1
      ring
    have hquad : 4 * E ≤ E * E := by nlinarith
    nlinarith
  have h := Real.exp_le_exp.mpr hlog
  simpa only [Real.exp_log hcostpos] using h

theorem eventually_uniform_tuple_size_condition :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell →
      12 * tupleScale (branchCount ell) *
        (2 : ℝ) ^ (Real.exp (4 * tupleScale (branchCount ell))) ≤ (k : ℝ) := by
  filter_upwards [eventually_uniform_tupleScale (by norm_num : (0 : ℝ) < 1 / 8)] with k hk
  intro ell hell
  have hm : 2 ≤ branchCount ell := by have := (branchCount_properties hell.2.1).1; omega
  have h := double_exponential_tuple_cost_bound
    (by linarith [hell.loglog_ge_thirty_two]) (tupleScale_pos hm)
    (by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hk ell hell)
  simpa only [Real.exp_log hell.log_pos,
    Real.exp_log (by exact_mod_cast (show 0 < k by have := hell.1; omega) : (0 : ℝ) < k)] using h

end PerfectPowers
