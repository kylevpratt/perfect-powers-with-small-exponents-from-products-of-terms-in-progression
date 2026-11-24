module

public import PerfectPowers.Main.AdmissiblePairs
public import PerfectPowers.Squares.IntegerConsecutive
import Mathlib.Tactic

/-!
# The step-one square obstruction after the full-product classification

Only the proved restricted consecutive-product lemma is used. No unrestricted
Erdos--Selfridge theorem is needed or asserted here.

Proof difference from the paper: the admissible-pair classification and
Bertrand reduce to `1 <= a <= k`, where an elementary prime of multiplicity
one obstructs a square. This replaces the draft's Erdos--Selfridge citation.
See `PerfectPowers.PaperComparison`.
-/

public section

namespace PerfectPowers

theorem AdmissiblePair.not_isSquare_step_one {k p : ℕ} {n : ℤ}
    (h : AdmissiblePair k p n 1) (hk : 2 ≤ k) (hp : LeastPrimeAbove k p) :
    ¬ IsSquare (progressionProduct n 1 (Finset.range k)) := by
  have hpk := hp.lt_two_mul hk
  intro hs
  rcases h with ⟨_, hn0, hn⟩ | ⟨_, hn0, hn⟩ | ⟨hbad, _⟩
  · have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
    have ha : 1 ≤ n.toNat := by omega
    have hak : n.toNat ≤ k := by omega
    rw [← hcast] at hs
    exact not_isSquare_int_consecutive_of_start_le_length k n.toNat hk ha hak hs
  · let a : ℤ := -n - ((k : ℤ) - 1)
    have haZ : 1 ≤ a := by dsimp [a]; omega
    have hakZ : a ≤ (k : ℤ) := by dsimp [a]; omega
    have hcast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (by omega)
    have ha : 1 ≤ a.toNat := by omega
    have hak : a.toNat ≤ k := by omega
    have hrepr : n = -(a.toNat : ℤ) - ((k : ℤ) - 1) := by rw [hcast]; dsimp [a]; ring
    rw [hrepr] at hs
    exact not_isSquare_negative_consecutive_of_start_le_length k a.toNat hk ha hak hs
  · omega

theorem even_exponent_step_one_impossible {k p ell : ℕ} {n y : ℤ}
    (hk : 2 ≤ k) (hp : LeastPrimeAbove k p) (hpair : AdmissiblePair k p n 1)
    (h : Solution k ell n 1 1 y (Finset.range k)) (hell : Even ell) : False := by
  apply hpair.not_isSquare_step_one hk hp
  rw [h.equation, one_mul]
  exact hell.isSquare_pow y

end PerfectPowers
