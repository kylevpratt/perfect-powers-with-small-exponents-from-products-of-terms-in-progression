module

public import PerfectPowers.Squares.OddPrefixes
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Product comparisons for distinct positive odd parts -/

public section

namespace PerfectPowers

theorem odd_range_product_le_prod (S : Finset ℕ) (b : ℕ)
    (hb : ∀ a ∈ S, 2 * b + 1 ≤ a ∧ Odd a) :
    (∏ i ∈ Finset.range S.card, (2 * b + 1 + 2 * i)) ≤ ∏ a ∈ S, a := by
  classical
  induction S using Finset.strongInductionOn generalizing b with
  | _ S ih =>
    by_cases hne : S.Nonempty
    · let a := S.min' hne
      have ha : a ∈ S := Finset.min'_mem S hne
      have hrec := ih (S.erase a) (Finset.erase_ssubset ha) (b + 1) (by
        intro z hz
        have hzS := Finset.mem_of_mem_erase hz
        have haz : a ≤ z := Finset.min'_le S z hzS
        have hza : z ≠ a := (Finset.mem_erase.mp hz).1
        obtain ⟨r, hr⟩ := (hb a ha).2
        obtain ⟨t, ht⟩ := (hb z hzS).2
        exact ⟨by have := (hb a ha).1; omega, (hb z hzS).2⟩)
      have hc : (S.erase a).card + 1 = S.card := Finset.card_erase_add_one ha
      have hshift : (∏ i ∈ Finset.range (S.erase a).card, (2 * b + 1 + 2 * (i + 1))) =
          ∏ i ∈ Finset.range (S.erase a).card, (2 * (b + 1) + 1 + 2 * i) := by
        apply Finset.prod_congr rfl
        intro i hi
        ring
      rw [← hc, Finset.prod_range_succ', hshift]
      norm_num only [mul_zero, add_zero]
      calc
        _ ≤ (∏ z ∈ S.erase a, z) * a := Nat.mul_le_mul hrec (hb a ha).1
        _ = ∏ z ∈ S, z := by rw [← Finset.prod_erase_mul S _ ha]
    · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hS]

theorem oddPrefix_card_le_prod (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a ∧ Odd a) :
    oddPrefix S.card ≤ ∏ a ∈ S, a := by
  simpa only [oddPrefix, mul_zero, zero_add, add_comm] using
    odd_range_product_le_prod S 0 (by intro a ha; exact ⟨by have := (hS a ha).1; omega, (hS a ha).2⟩)

theorem oddPrefix_card_le_prod_of_injOn {ι : Type*} (S : Finset ι) (a : ι → ℕ)
    (hinj : Set.InjOn a (↑S : Set ι)) (ha : ∀ i ∈ S, 0 < a i ∧ Odd (a i)) :
    oddPrefix S.card ≤ ∏ i ∈ S, a i := by
  classical
  have h := oddPrefix_card_le_prod (S.image a) (by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact ha i hi)
  rwa [Finset.card_image_of_injOn hinj, Finset.prod_image hinj] at h

theorem oddPrefix_twice_gt_square {s : ℕ} (hs : 0 < s) :
    oddPrefix s ^ 2 < oddPrefix (2 * s) := by
  have htail : oddPrefix s < ∏ i ∈ Finset.range s, ((2 * s + 1) + 2 * i) := by
    apply Finset.prod_lt_prod_of_nonempty₀
    · intro i hi
      omega
    · intro i hi
      omega
    · exact ⟨0, Finset.mem_range.mpr hs⟩
  have hmul := Nat.mul_lt_mul_of_pos_left htail (oddPrefix_pos s)
  rw [← oddPrefix_add] at hmul
  simpa only [two_mul, pow_two] using hmul

end PerfectPowers
