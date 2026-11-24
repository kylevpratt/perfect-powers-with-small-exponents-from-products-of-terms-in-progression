module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # Products of index distances and the factorial deletion bound -/

public section

namespace PerfectPowers

theorem prod_range_dist_right (k : ℕ) :
    (∏ i ∈ Finset.range k, Nat.dist i k) = k.factorial := by
  calc
    (∏ i ∈ Finset.range k, Nat.dist i k) =
        ∏ i ∈ Finset.range k, ((k - 1 - i) + 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hik := Finset.mem_range.mp hi
      rw [Nat.dist_eq_sub_of_le hik.le]
      omega
    _ = ∏ i ∈ Finset.range k, (i + 1) := Finset.prod_range_reflect (fun i => i + 1) k
    _ = k.factorial := Finset.prod_range_add_one_eq_factorial k

theorem prod_dist_erase_eq_factorials {k j : ℕ} (hj : j < k) :
    (∏ i ∈ (Finset.range k).erase j, Nat.dist i j) =
      j.factorial * (k - 1 - j).factorial := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hjk : j = k
      · subst j
        simp [Finset.range_add_one, prod_range_dist_right]
      · have hjlt : j < k := by omega
        have hknot : k ∉ (Finset.range k).erase j := by simp
        rw [Finset.range_add_one, Finset.erase_insert_of_ne (Ne.symm hjk),
          Finset.prod_insert hknot, ih hjlt]
        rw [Nat.dist_eq_sub_of_le_right hjlt.le]
        have hsub : k - j = (k - 1 - j) + 1 := by omega
        have hsub' : k + 1 - 1 - j = k - j := by omega
        rw [hsub', hsub, Nat.factorial_succ]
        ring

theorem prod_dist_erase_dvd_factorial {k j : ℕ} (hj : j < k) :
    (∏ i ∈ (Finset.range k).erase j, Nat.dist i j) ∣ (k - 1).factorial := by
  rw [prod_dist_erase_eq_factorials hj]
  exact Nat.factorial_mul_factorial_dvd_factorial (by omega)

end PerfectPowers
