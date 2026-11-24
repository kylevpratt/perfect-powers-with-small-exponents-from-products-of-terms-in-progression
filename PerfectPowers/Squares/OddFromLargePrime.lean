module

public import PerfectPowers.Squares.OddLargePrime
public import PerfectPowers.Squares.DistinctSquareParts
public import PerfectPowers.Squares.OddValuationBound
import Mathlib.Tactic

/-!
# The squarefree-parts proof of Lemma 3.6, given its auxiliary prime fact

This module isolates the squarefree argument from the auxiliary assertion
that a prime divisor exceeds the length. `OddNonsquare` supplies that assertion
using `OddLongStartPrime` and the Bertrand argument in `OddShortStart`.
-/

public section

namespace PerfectPowers

theorem oddPrefix_mono : Monotone oddPrefix := by
  intro s t hst
  apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hst)
  intro i hi hnot
  omega

theorem not_isSquare_odd_progression_of_large_prime {k m p : ℕ} (hk : 2 ≤ k)
    (hm : 0 < m) (hodd : Odd m) (hp : p.Prime) (hpk : k < p)
    (hdiv : p ∣ ∏ i ∈ Finset.range k, (m + 2 * i)) :
    ¬IsSquare (∏ i ∈ Finset.range k, (m + 2 * i)) := by
  classical
  intro hsq
  have hmLarge := odd_square_start_large_of_prime hk hm hodd hp hpk hdiv hsq
  have hchoose : ∀ i : ℕ, ∃ a x : ℕ, 0 < a ∧ 0 < x ∧ x ^ 2 * a = m + 2 * i ∧ Squarefree a := by
    intro i
    exact Nat.sq_mul_squarefree_of_pos (by omega)
  choose a x ha hx heq hsf using hchoose
  have hparts : ∀ i : ℕ, m + 2 * i = a i * x i ^ 2 := by
    intro i
    rw [← heq i]
    ring
  have haodd : ∀ i : ℕ, Odd (a i) := by
    intro i
    have ho : Odd (a i * x i ^ 2) := by
      rw [← hparts]
      exact hodd.add_even ⟨i, by omega⟩
    exact Nat.Odd.of_mul_left ho
  have hprodid : (∏ i ∈ Finset.range k, (m + 2 * i)) =
      (∏ i ∈ Finset.range k, x i) ^ 2 * (∏ i ∈ Finset.range k, a i) := by
    simp_rw [hparts]
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
    ring
  have hsqA : IsSquare (∏ i ∈ Finset.range k, a i) := by
    apply isSquare_of_square_factor (Finset.prod_ne_zero_iff.mpr (fun i hi => (hx i).ne'))
    rwa [← hprodid]
  have hnat (i : ℕ) : (term (m : ℤ) 2 i).natAbs = m + 2 * i := by
    have heq : term (m : ℤ) 2 i = ((m + 2 * i : ℕ) : ℤ) := by simp [term]; ring
    rw [heq, Int.natAbs_natCast]
  have hcoprime : Nat.Coprime (m : ℤ).natAbs 2 := by
    simpa only [Int.natAbs_natCast] using Nat.coprime_two_right.mpr hodd
  have hspace : ∀ q : ℕ, q.Prime → ∀ i < k, q ∣ a i →
      ∀ j < k, q ∣ a j → i ≠ j → q ≤ Nat.dist i j := by
    intro q hq i hi hqi j hj hqj hne
    have hdi : q ∣ (term (m : ℤ) 2 i).natAbs := by rw [hnat, hparts]; exact dvd_mul_of_dvd_left hqi _
    have hdj : q ∣ (term (m : ℤ) 2 j).natAbs := by rw [hnat, hparts]; exact dvd_mul_of_dvd_left hqj _
    rcases lt_or_gt_of_ne hne with hij | hij
    · rw [Nat.dist_eq_sub_of_le hij.le]
      exact common_divisor_le_index_gap hcoprime hij hdi hdj
    · rw [Nat.dist_eq_sub_of_le_right hij.le]
      exact common_divisor_le_index_gap hcoprime hij hdj hdi
  have hdivA := squarefree_odd_product_dvd_oddPrefix_square
    (fun i hi => ⟨hsf i, haodd i⟩) hsqA hspace
  have hupper := Nat.le_of_dvd (pow_pos (oddPrefix_pos _) 2) hdivA
  have hlower := oddPrefix_card_le_prod_of_injOn (Finset.range k) a
    (square_parts_injective_of_large_start (by omega : k ^ 2 < m) (fun i hi => hparts i))
    (fun i hi => ⟨ha i, haodd i⟩)
  rw [Finset.card_range] at hlower
  have hstrict := oddPrefix_twice_gt_square (show 0 < k / 2 by omega)
  have hmono := oddPrefix_mono (show 2 * (k / 2) ≤ k by omega)
  omega

end PerfectPowers
