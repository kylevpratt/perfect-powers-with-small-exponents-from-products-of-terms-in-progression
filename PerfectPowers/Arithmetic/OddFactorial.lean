module

public import PerfectPowers.Arithmetic.OddDeletion
public import PerfectPowers.Analytic.FactorialBounds
public import Mathlib.Data.Nat.Multiplicity
import Mathlib.Tactic

/-! # The odd part of a factorial

Legendre's binary-digit formula bounds the power of two removed from the
factorial. The resulting logarithmic estimate is uniform, including small k.
-/

public section

namespace PerfectPowers

theorem oddPart_mul_two_pow {N : ℕ} (hN : N ≠ 0) :
    oddPart N * 2 ^ N.factorization 2 = N := by
  apply Nat.eq_of_factorization_eq
    (mul_ne_zero (oddPart_pos N).ne' (by positivity)) hN
  intro p
  rw [Nat.factorization_mul (oddPart_pos N).ne' (by positivity),
    Nat.prime_two.factorization_pow, Finsupp.add_apply]
  change (primePart (fun q => q ≠ 2) N).factorization p + _ = _
  rw [factorization_primePart, Finsupp.filter_apply]
  by_cases hp : p = 2 <;> simp [hp]

theorem two_pow_binary_digit_sum_le (n : ℕ) :
    2 ^ (Nat.digits 2 n).sum ≤ n + 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · simp [hn]
    · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      rw [Nat.digits_of_two_le_of_pos (by decide) hn0, List.sum_cons, pow_add]
      have h := ih (n / 2) (Nat.div_lt_self hn0 (by decide))
      have hr := Nat.mod_lt n (by decide : 0 < 2)
      have heq := Nat.mod_add_div n 2
      have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hcases with hr | hr <;> rw [hr] <;> norm_num <;> omega

theorem factorization_two_factorial_add_digit_sum (n : ℕ) :
    n.factorial.factorization 2 + (Nat.digits 2 n).sum = n := by
  have h : n.factorial.factorization 2 = n - (Nat.digits 2 n).sum := by
    rw [Nat.factorization_def _ Nat.prime_two]
    simpa only [show 2 - 1 = 1 from rfl, one_mul] using
      (Nat.prime_two.sub_one_mul_multiplicity_factorial (n := n))
  have hs := Nat.digit_sum_le 2 n
  omega

theorem log_factorial_pred_upper {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((k - 1).factorial : ℝ) ≤
      (k : ℝ) * Real.log k - k + 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hf : (k.factorial : ℝ) = k * ((k - 1).factorial : ℝ) := by
    exact_mod_cast (show k.factorial = k * (k - 1).factorial by
      simpa only [Nat.sub_add_cancel hk] using Nat.factorial_succ (k - 1))
  have hupper := log_factorial_upper hk
  rw [hf, Real.log_mul hk0.ne' (by positivity)] at hupper
  linarith

/-- The odd part of `(k-1)!` is at most `k * (k-1)! / 2^(k-1)`,
expressed logarithmically for the deletion comparison. -/
theorem log_oddPart_factorial_upper {k : ℕ} (hk : 1 ≤ k) :
    Real.log (oddPart (k - 1).factorial : ℝ) ≤
      (k : ℝ) * Real.log k - k - ((k : ℝ) - 1) * Real.log 2 + Real.log k + 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsum := factorization_two_factorial_add_digit_sum (k - 1)
  have hsumR : ((k - 1).factorial.factorization 2 : ℝ) +
      ((Nat.digits 2 (k - 1)).sum : ℝ) = (k : ℝ) - 1 := by
    exact_mod_cast (show (k - 1).factorial.factorization 2 +
      (Nat.digits 2 (k - 1)).sum = k - 1 from hsum)
  have hp := two_pow_binary_digit_sum_le (k - 1)
  rw [Nat.sub_add_cancel hk] at hp
  have hpR : (2 : ℝ) ^ (Nat.digits 2 (k - 1)).sum ≤ k := by exact_mod_cast hp
  have hlog := Real.log_le_log (by positivity) hpR
  rw [Real.log_pow] at hlog
  have hid : (oddPart (k - 1).factorial : ℝ) *
      (2 : ℝ) ^ (k - 1).factorial.factorization 2 = ((k - 1).factorial : ℝ) := by
    exact_mod_cast oddPart_mul_two_pow (Nat.factorial_ne_zero (k - 1))
  have hidlog := congrArg Real.log hid
  rw [Real.log_mul (by exact_mod_cast (oddPart_pos (k - 1).factorial).ne') (by positivity),
    Real.log_pow] at hidlog
  have hf := log_factorial_pred_upper hk
  have hsumlog := congrArg (fun t : ℝ => t * Real.log 2) hsumR
  nlinarith

end PerfectPowers
