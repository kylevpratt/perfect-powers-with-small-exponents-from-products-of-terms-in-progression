module

public import PerfectPowers.Analytic.ExponentRange
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Uniform estimates for a varying exponent

The quantifier over `ell` is inside `eventually`: each epsilon gives one
threshold for all exponents in the paper's range. These are existence
statements about thresholds, not algorithms for computing them.
-/

public section

open Filter

namespace PerfectPowers

theorem exists_uniform_fourth_power_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ z : ℝ, 0 ≤ z → z ^ 5 ≤ 243 * T →
      z ^ 4 ≤ ε * T := by
  let M : ℝ := 243 / ε
  have hM : 0 < M := div_pos (by norm_num) hε
  refine ⟨M ^ 4 / ε, ?_⟩
  intro T hT z hz hpow
  by_cases hzM : z ≤ M
  · have hsmall : z ^ 4 ≤ M ^ 4 := by gcongr
    have hscale : M ^ 4 ≤ ε * T := by
      have := (div_le_iff₀ hε).mp hT
      nlinarith
    exact hsmall.trans hscale
  · have hlarge : M ≤ z := le_of_lt (lt_of_not_ge hzM)
    calc
      z ^ 4 ≤ z ^ 5 / M := by
        apply (le_div_iff₀ hM).mpr
        nlinarith [mul_le_mul_of_nonneg_right hlarge (pow_nonneg hz 4)]
      _ ≤ 243 * T / M := div_le_div_of_nonneg_right hpow hM.le
      _ = ε * T := by dsimp [M]; field_simp

theorem eventually_uniform_branchCount_fourth_power {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell →
      (branchCount ell : ℝ) ^ 4 ≤ ε * Real.log (Real.log (k : ℝ)) := by
  obtain ⟨T0, hT0⟩ := exists_uniform_fourth_power_bound hε
  have hT : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hT.eventually_ge_atTop T0] with k hk
  intro ell hell
  exact hT0 _ hk _ (Nat.cast_nonneg _) hell.branchCount_fifth_power_bound

end PerfectPowers
