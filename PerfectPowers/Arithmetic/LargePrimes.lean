module

public import PerfectPowers.Arithmetic.ProgressionGCD
public import PerfectPowers.Arithmetic.PrimeParts
import Mathlib.Tactic

/-! # Large-prime multiplicities in solutions of the central equation -/

public section

namespace PerfectPowers

theorem Solution.large_prime_valuation_multiple {k ell d : ℕ} {n b y : ℤ} {S : Finset ℕ}
    (h : Solution k ell n d b y S) {i p : ℕ} (hi : i ∈ S) (hp : p.Prime) (hpk : k < p) :
    ell ∣ (term n d i).natAbs.factorization p := by
  classical
  by_cases hpi : p ∣ (term n d i).natAbs
  · have hother (j : ℕ) (hj : j ∈ S) (hji : j ≠ i) :
        (term n d j).natAbs.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpj
      have hij := index_eq_of_large_common_divisor h.coprime
        (Finset.mem_range.mp (h.index_subset hj))
        (Finset.mem_range.mp (h.index_subset hi)) hpk.le hpj hpi
      exact hji hij
    have hval : (progressionProduct n d S).natAbs.factorization p =
        (term n d i).natAbs.factorization p := by
      rw [natAbs_progressionProduct, Nat.factorization_prod_apply
        (fun j hj => Int.natAbs_ne_zero.mpr (h.term_ne_zero hj))]
      exact Finset.sum_eq_single i (fun j hj hji => hother j hj hji)
        (fun hnot => (hnot hi).elim)
    have hbval : b.natAbs.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpb
      exact (not_le_of_gt hpk) (h.b_smooth.2 p hp hpb)
    have hnat : (progressionProduct n d S).natAbs = b.natAbs * y.natAbs ^ ell := by
      rw [h.equation, Int.natAbs_mul, Int.natAbs_pow]
    have hiEq : (term n d i).natAbs.factorization p = ell * y.natAbs.factorization p := by
      rw [← hval, hnat, Nat.factorization_mul
        (Int.natAbs_ne_zero.mpr h.b_ne_zero)
        (pow_ne_zero _ (Int.natAbs_ne_zero.mpr h.y_ne_zero))]
      simp [hbval, Nat.factorization_pow]
    rw [hiEq]
    exact dvd_mul_right _ _
  · rw [Nat.factorization_eq_zero_of_not_dvd hpi]
    exact dvd_zero ell

theorem Solution.largePart_is_power {k ell d : ℕ} {n b y : ℤ} {S : Finset ℕ}
    (h : Solution k ell n d b y S) {i : ℕ} (hi : i ∈ S) :
    ∃ x : ℕ, largePart k (term n d i).natAbs = x ^ ell := by
  apply (exists_eq_pow_iff_factorization_dvd (largePart_pos _ _).ne').mpr
  intro p hp
  change ell ∣ (primePart (fun p => ¬ p ≤ k) (term n d i).natAbs).factorization p
  rw [factorization_primePart, Finsupp.filter_apply]
  split_ifs with hpk
  · exact dvd_zero ell
  · exact h.large_prime_valuation_multiple hi hp (Nat.lt_of_not_ge hpk)

end PerfectPowers
