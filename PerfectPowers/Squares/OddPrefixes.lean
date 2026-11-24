module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

/-!
# Odd-prefix products and elementary square cancellation

These algebraic lemmas are used in the proof of Lemma 3.6. The final
classification, which uses that proved lemma, is in `SignedOddProduct`.
-/

@[expose] public section

namespace PerfectPowers

def oddPrefix (N : ℕ) : ℕ := ∏ i ∈ Finset.range N, (2 * i + 1)

theorem oddPrefix_pos (N : ℕ) : 0 < oddPrefix N := by
  apply Finset.prod_pos
  intro i hi
  omega

theorem oddPrefix_add (N L : ℕ) :
    oddPrefix (N + L) = oddPrefix N * (∏ i ∈ Finset.range L, ((2 * N + 1) + 2 * i)) := by
  unfold oddPrefix
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  ring

theorem isSquare_of_square_factor {a b : ℕ} (ha : a ≠ 0) (hs : IsSquare (a ^ 2 * b)) : IsSquare b := by
  have hsQ := Rat.isSquare_natCast_iff.mpr hs
  have hdiv := hsQ.div (IsSquare.sq (a : ℚ))
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have heq : ((a ^ 2 * b : ℕ) : ℚ) / (a : ℚ) ^ 2 = (b : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hdiv
  exact Rat.isSquare_natCast_iff.mp hdiv

theorem oddPrefix_gap_isSquare {N P : ℕ} (hNP : N ≤ P)
    (hs : IsSquare (oddPrefix N * oddPrefix P)) :
    IsSquare (∏ i ∈ Finset.range (P - N), ((2 * N + 1) + 2 * i)) := by
  have hP := oddPrefix_add N (P - N)
  rw [Nat.add_sub_of_le hNP] at hP
  have heq : oddPrefix N * oddPrefix P = oddPrefix N ^ 2 *
      (∏ i ∈ Finset.range (P - N), ((2 * N + 1) + 2 * i)) := by rw [hP]; ring
  rw [heq] at hs
  exact isSquare_of_square_factor (oddPrefix_pos N).ne' hs

theorem square_mod_four_ne_three (a : ℕ) : (a * a) % 4 ≠ 3 := by
  have h := Nat.mod_lt a (by norm_num : 0 < 4)
  have hc : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases hc with h | h | h | h <;> simp [Nat.mul_mod, h]

end PerfectPowers
