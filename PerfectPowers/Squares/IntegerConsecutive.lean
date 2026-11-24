module

public import PerfectPowers.Basic.Products
public import PerfectPowers.Squares.Consecutive
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

/-! # Integer versions of the restricted consecutive-product obstruction -/

public section

namespace PerfectPowers

theorem not_isSquare_int_consecutive_of_start_le_length (k a : ℕ)
    (hk : 2 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) :
    ¬ IsSquare (progressionProduct (a : ℤ) 1 (Finset.range k)) := by
  intro hs
  apply not_isSquare_consecutive_of_start_le_length k a hk ha hak
  have hprod : progressionProduct (a : ℤ) 1 (Finset.range k) =
      ((∏ i ∈ Finset.range k, (a + i) : ℕ) : ℤ) := by
    simp [progressionProduct, term, Nat.cast_add]
  exact Int.isSquare_natCast_iff.mp (hprod ▸ hs)

/-- Absolute values give the reflected obstruction for either parity of `k`. -/
theorem not_isSquare_negative_consecutive_of_start_le_length (k a : ℕ)
    (hk : 2 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) :
    ¬ IsSquare (progressionProduct (-(a : ℤ) - ((k : ℤ) - 1)) 1 (Finset.range k)) := by
  intro hs
  have hreflect := progressionProduct_reflect (-(a : ℤ) - ((k : ℤ) - 1)) 1 k
  have hstart : -(-(a : ℤ) - ((k : ℤ) - 1)) - ((k : ℤ) - 1) * (1 : ℕ) = (a : ℤ) := by
    ring
  rw [hstart] at hreflect
  have habs := IsSquare.map Int.natAbsHom hs
  change IsSquare (progressionProduct (-(a : ℤ) - ((k : ℤ) - 1)) 1 (Finset.range k)).natAbs
    at habs
  have hprodpos : 0 ≤ progressionProduct (a : ℤ) 1 (Finset.range k) := by
    apply Finset.prod_nonneg
    intro i hi
    simp only [term, Nat.cast_one, mul_one]
    positivity
  have habseq : (progressionProduct (-(a : ℤ) - ((k : ℤ) - 1)) 1 (Finset.range k)).natAbs =
      (progressionProduct (a : ℤ) 1 (Finset.range k)).natAbs := by
    rw [hreflect, Int.natAbs_mul, Int.natAbs_pow]
    simp
  have hspos : IsSquare (progressionProduct (a : ℤ) 1 (Finset.range k)) := by
    have hn := habseq ▸ habs
    have hc := Int.isSquare_natCast_iff.mpr hn
    simpa only [Int.natCast_natAbs, abs_of_nonneg hprodpos] using hc
  exact not_isSquare_int_consecutive_of_start_le_length k a hk ha hak hspos

end PerfectPowers
