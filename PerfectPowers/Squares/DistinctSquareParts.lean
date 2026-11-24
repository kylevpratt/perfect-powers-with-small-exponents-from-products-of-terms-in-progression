module

public import PerfectPowers.Squares.OddPrefixes
import Mathlib.Tactic

/-! # Distinct square parts in the long-start case of Lemma 3.6 -/

public section

namespace PerfectPowers

theorem square_parts_injective_of_large_start {k m : ℕ} {a x : ℕ → ℕ}
    (hm : k ^ 2 < m)
    (hparts : ∀ i < k, m + 2 * i = a i * x i ^ 2) :
    Set.InjOn a (↑(Finset.range k) : Set ℕ) := by
  have hlarge : ∀ i < k, k < a i * x i := by
    intro i hi
    have heq := hparts i hi
    have ha : 1 ≤ a i := by
      by_contra h
      have hz : a i = 0 := by omega
      rw [hz, zero_mul] at heq
      nlinarith
    have hmul := Nat.mul_le_mul_right (m + 2 * i) ha
    have hid : (a i * x i) ^ 2 = a i * (m + 2 * i) := by rw [heq]; ring
    by_contra h
    have hle : a i * x i ≤ k := by omega
    have hsq := Nat.pow_le_pow_left hle 2
    nlinarith
  have hlt : ∀ i < k, ∀ j < k, i < j → a i ≠ a j := by
    intro i hi j hj hij heqa
    have hei := hparts i hi
    have hej := hparts j hj
    rw [← heqa] at hej
    have hxlt : x i < x j := by
      by_contra h
      have hsq := Nat.pow_le_pow_left (show x j ≤ x i by omega) 2
      have hmul := Nat.mul_le_mul_left (a i) hsq
      omega
    have hxstep : x i + 1 ≤ x j := by omega
    have hsq := Nat.pow_le_pow_left hxstep 2
    have hmul := Nat.mul_le_mul_left (a i) hsq
    have hbig := hlarge i hi
    nlinarith
  intro i hi j hj heq
  have hi' : i < k := Finset.mem_range.mp hi
  have hj' : j < k := Finset.mem_range.mp hj
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hlt i hi' j hj' hij heq).elim
  · exact hij
  · exact (hlt j hj' i hi' hij heq.symm).elim

end PerfectPowers
