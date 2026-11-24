module

public import PerfectPowers.Arithmetic.FullProductTools
public import PerfectPowers.Basic.LeastPrime
public import PerfectPowers.Analytic.ShortPrimeIntervals
import Mathlib.Tactic

/-! # Positive starting points in the full-product classification -/

public section

namespace PerfectPowers

theorem step_one_positive_classification {k p : ℕ} {n : ℤ}
    (hk : 4 ≤ k) (hp : LeastPrimeAbove k p) (_hn : 0 < n) (hnbound : n ≤ 2 * (k : ℤ))
    (hprime : ∀ x : ℝ, (k : ℝ) ≤ x → ∃ q : ℕ, q.Prime ∧ x < (q : ℝ) ∧ (q : ℝ) ≤ (5 / 4 : ℝ) * x)
    (hsmooth : ∀ i : ℕ, i < k → Smooth k (term n 1 i)) : n ≤ (p : ℤ) - (k : ℤ) := by
  have hnp : n < (p : ℤ) := by
    by_contra hnot
    have hpn : (p : ℤ) ≤ n := le_of_not_gt hnot
    have hkn : (k : ℝ) ≤ (n : ℝ) := by
      have hkpZ : (k : ℤ) < p := by exact_mod_cast hp.2.1
      exact_mod_cast (show (k : ℤ) ≤ n by omega)
    obtain ⟨q, hq, hql, hqu⟩ := hprime (n : ℝ) hkn
    have hnq : n ≤ (q : ℤ) := by exact_mod_cast hql.le
    have h4q : 4 * (q : ℤ) ≤ 5 * n := by
      exact_mod_cast (show (4 : ℝ) * (q : ℝ) ≤ 5 * (n : ℝ) by linarith)
    have hqend : (q : ℤ) ≤ n + ((k : ℤ) - 1) := by omega
    obtain ⟨i, hi, heq⟩ := exists_index_step_one hnq hqend
    have hqk : k < q := by exact_mod_cast (lt_of_le_of_lt hkn hql)
    exact not_smooth_nat_prime hq hqk (heq ▸ hsmooth i hi)
  by_contra hnot
  have hpend : (p : ℤ) ≤ n + ((k : ℤ) - 1) := by omega
  obtain ⟨i, hi, heq⟩ := exists_index_step_one hnp.le hpend
  exact not_smooth_nat_prime hp.1 hp.2.1 (heq ▸ hsmooth i hi)

theorem step_two_positive_impossible {k : ℕ} {n : ℤ}
    (hk : 4 ≤ k) (hn : 0 < n) (hnbound : n ≤ 3 * (k : ℤ)) (hodd : Odd n)
    (hprime : ∀ x : ℝ, (k : ℝ) ≤ x → ∃ q : ℕ, q.Prime ∧ x < (q : ℝ) ∧ (q : ℝ) ≤ (5 / 4 : ℝ) * x)
    (hsmooth : ∀ i : ℕ, i < k → Smooth k (term n 2 i)) : False := by
  let M : ℤ := max n (k : ℤ)
  have hMk : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_max_right n (k : ℤ))
  have hMn : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_max_left n (k : ℤ))
  obtain ⟨q, hq, hql, hqu⟩ := hprime (M : ℝ) hMk
  have hqk : k < q := by exact_mod_cast (lt_of_le_of_lt hMk hql)
  have hnq : n ≤ (q : ℤ) := by exact_mod_cast (lt_of_le_of_lt hMn hql).le
  have h4q : 4 * (q : ℤ) ≤ 5 * M := by
    exact_mod_cast (show (4 : ℝ) * (q : ℝ) ≤ 5 * (M : ℝ) by linarith)
  have hqend : (q : ℤ) ≤ n + 2 * ((k : ℤ) - 1) := by
    by_cases hnk : n ≤ (k : ℤ)
    · dsimp [M] at h4q
      rw [max_eq_right hnk] at h4q
      omega
    · dsimp [M] at h4q
      rw [max_eq_left (le_of_not_ge hnk)] at h4q
      omega
  have hqodd : Odd (q : ℤ) := Int.odd_natCast q |>.mpr (hq.odd_of_ne_two (by omega))
  obtain ⟨i, hi, heq⟩ := exists_index_step_two hodd hqodd hnq hqend
  exact not_smooth_nat_prime hq hqk (heq ▸ hsmooth i hi)

end PerfectPowers
