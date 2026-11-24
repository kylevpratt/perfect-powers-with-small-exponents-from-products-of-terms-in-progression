module

public import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Tactic

/-!
# Qualitative prime-counting bounds

These use mathlib's proved PNT and introduce no external mathematical input.
They establish the eventual bounds required by the project's existence-only
threshold target. The uniform prime-AP input in Lemma 3.3 is separate.
-/

public section

open Filter Asymptotics

namespace PerfectPowers

theorem eventually_primeCounting_le_real {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (1 + epsilon) * (x / Real.log x) := by
  have hden : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_ne_zero (by linarith) (Real.log_pos hx).ne'
  have ht := (isEquivalent_iff_tendsto_one hden).mp Nat.isEquivalent_primeCounting
  have hupper := ht.eventually_lt_const (show (1 : ℝ) < 1 + epsilon by linarith)
  filter_upwards [hupper, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  change (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x) < 1 + epsilon at hx
  exact ((div_lt_iff₀ (div_pos (by linarith) (Real.log_pos hx1))).mp hx).le

theorem eventually_primeCounting_le {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : ℕ in atTop,
      (Nat.primeCounting k : ℝ) ≤ (1 + epsilon) * ((k : ℝ) / Real.log (k : ℝ)) := by
  have h := tendsto_natCast_atTop_atTop.eventually (eventually_primeCounting_le_real hepsilon)
  simpa using h

theorem eventually_primeCounting_le_twenty_one_twentieths :
    ∀ᶠ k : ℕ in atTop,
      (Nat.primeCounting k : ℝ) ≤ (21 / 20 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) := by
  convert eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1 / 20) using 1; norm_num

end PerfectPowers
