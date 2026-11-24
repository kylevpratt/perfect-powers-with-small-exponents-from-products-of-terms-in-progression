module

public import PerfectPowers.Arithmetic.OddFactorial
public import PerfectPowers.Analytic.ElementaryPrimeCounting
import Mathlib.Tactic

/-! # A large prime divisor of a long odd progression

Delete one term of maximal valuation for each odd prime at most k. If all
prime divisors were at most k, the retained product would divide the odd part
of `(k-1)!`. The elementary logarithmic estimates contradict this divisibility.
-/

public section

namespace PerfectPowers

theorem exists_large_prime_dvd_odd_progression_of_long_start
    (m k : ℕ) (hm : 0 < m) (hodd : Odd m) (hk : 2 ≤ k) (hlong : 2 * k < m) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ i ∈ Finset.range k, (m + 2 * i) := by
  classical
  by_contra hprime
  have hsmooth : ∀ p : ℕ, p.Prime →
      p ∣ (∏ i ∈ Finset.range k, (m + 2 * i)) → p ≤ k := by
    intro p hp hdiv
    by_contra hpk
    exact hprime ⟨p, hp, by omega, hdiv⟩
  obtain ⟨I, _, hcard, hdiv⟩ := exists_odd_progression_deletion hk hm hodd hsmooth
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hprod0 : (0 : ℝ) < ((∏ i ∈ I, (m + 2 * i) : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i hi => (show 0 < m + 2 * i by omega))
  have hlower : (I.card : ℝ) * Real.log (2 * (k : ℝ)) ≤
      Real.log ((∏ i ∈ I, (m + 2 * i) : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (by intro i hi; positivity)]
    calc
      _ = ∑ i ∈ I, Real.log (2 * (k : ℝ)) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.log_le_log (by positivity)
        exact_mod_cast (show 2 * k ≤ m + 2 * i by omega)
  have hupper : Real.log ((∏ i ∈ I, (m + 2 * i) : ℕ) : ℝ) ≤
      Real.log (oddPart (k - 1).factorial : ℝ) := by
    apply Real.log_le_log hprod0
    exact_mod_cast Nat.le_of_dvd (oddPart_pos _) hdiv
  have hfact := log_oddPart_factorial_upper (show 1 ≤ k by omega)
  have hpi := primeCounting_log_two_mul_add_one_lt hk
  have hcardR : (k : ℝ) + 1 ≤ (I.card : ℝ) + Nat.primeCounting k := by exact_mod_cast hcard
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogpos : 0 ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hcount := mul_le_mul_of_nonneg_right hcardR hlogpos
  have hlog : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log k :=
    Real.log_mul (by norm_num) hk0.ne'
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog] at hlower hcount hpi
  rw [hfour] at hpi
  nlinarith

end PerfectPowers
