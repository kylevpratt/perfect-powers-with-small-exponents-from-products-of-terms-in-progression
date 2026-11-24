module

public import PerfectPowers.Basic.Parameters
import Mathlib.Tactic

/-! # Exponent-range equivalence and a uniform polynomial bound for the branch count -/

public section

namespace PerfectPowers

theorem fifth_power_le_iff_le_fifth_root {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    a ^ 5 ≤ T ↔ a ≤ T ^ (1 / 5 : ℝ) := by
  symm
  simpa [one_div, Real.rpow_natCast] using
    Real.le_rpow_inv_iff_of_pos ha hT (by norm_num : (0 : ℝ) < 5)

theorem smallExponent_iff_paper_range {k ell : ℕ} (hk : 3 ≤ k) (hell : 2 ≤ ell)
    (hT : 0 ≤ Real.log (Real.log (k : ℝ))) :
    SmallExponent k ell ↔ (ell : ℝ) ≤ (Real.log (Real.log (k : ℝ))) ^ (1 / 5 : ℝ) := by
  have heq := fifth_power_le_iff_le_fifth_root (Nat.cast_nonneg ell) hT
  exact ⟨fun h => heq.mp h.2.2, fun h => ⟨hk, hell, heq.mpr h⟩⟩

theorem SmallExponent.log_pos {k ell : ℕ} (h : SmallExponent k ell) :
    0 < Real.log (k : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < k by have := h.1; omega)

theorem SmallExponent.loglog_ge_thirty_two {k ell : ℕ} (h : SmallExponent k ell) :
    32 ≤ Real.log (Real.log (k : ℝ)) := by
  have hell : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast h.2.1
  have hpow : (2 : ℝ) ^ 5 ≤ (ell : ℝ) ^ 5 := by gcongr
  norm_num at hpow
  linarith [h.2.2]

/-- One bound, with an absolute constant, controls every varying allowed exponent. -/
theorem SmallExponent.branchCount_fifth_power_bound {k ell : ℕ} (h : SmallExponent k ell) :
    (branchCount ell : ℝ) ^ 5 ≤ 243 * Real.log (Real.log (k : ℝ)) := by
  have hm : (branchCount ell : ℝ) ≤ 3 * (ell : ℝ) := by
    exact_mod_cast (branchCount_properties h.2.1).2.2.2.2
  calc
    (branchCount ell : ℝ) ^ 5 ≤ (3 * (ell : ℝ)) ^ 5 := by gcongr
    _ = 243 * (ell : ℝ) ^ 5 := by ring
    _ ≤ 243 * Real.log (Real.log (k : ℝ)) := mul_le_mul_of_nonneg_left h.2.2 (by norm_num)

end PerfectPowers
