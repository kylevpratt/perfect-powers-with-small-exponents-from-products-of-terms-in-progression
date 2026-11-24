module

public import PerfectPowers.Basic.Products
import Mathlib.Tactic

/-! # Coprimality and common divisors of primitive progression terms -/

public section

namespace PerfectPowers

theorem gcd_term_step (n : ℤ) (d i : ℕ) :
    Int.gcd (term n d i) (d : ℤ) = Int.gcd n (d : ℤ) := by
  simp [term]

theorem term_coprime_step {n : ℤ} {d : ℕ} (h : Nat.Coprime n.natAbs d) (i : ℕ) :
    Nat.Coprime (term n d i).natAbs d := by
  change Int.gcd (term n d i) (d : ℤ) = 1
  rw [gcd_term_step]
  simpa only [Int.gcd_def, Int.natAbs_natCast] using h

/-- A common integer divisor of two terms of a primitive progression divides
their index difference. This form avoids any ordering choice on the indices. -/
theorem common_divisor_dvd_index_sub {n q : ℤ} {d i j : ℕ}
    (hprimitive : Nat.Coprime n.natAbs d)
    (hqi : q ∣ term n d i) (hqj : q ∣ term n d j) : q ∣ (j : ℤ) - (i : ℤ) := by
  have hqd : Int.gcd q (d : ℤ) = 1 := by
    apply Nat.dvd_one.mp
    have ht : Int.gcd (term n d i) (d : ℤ) = 1 := by
      rw [gcd_term_step]
      simpa only [Int.gcd_def, Int.natAbs_natCast] using hprimitive
    exact ht ▸ Int.gcd_dvd_gcd_of_dvd_left (d : ℤ) hqi
  apply Int.dvd_of_dvd_mul_left_of_gcd_one ?_ hqd
  simpa only [term_sub_term] using dvd_sub hqj hqi

theorem gcd_terms_dvd_index_sub {n : ℤ} {d : ℕ}
    (hprimitive : Nat.Coprime n.natAbs d) (i j : ℕ) :
    (Int.gcd (term n d i) (term n d j) : ℤ) ∣ (j : ℤ) - (i : ℤ) :=
  common_divisor_dvd_index_sub hprimitive (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)

theorem common_divisor_le_index_gap {n : ℤ} {d i j q : ℕ}
    (hprimitive : Nat.Coprime n.natAbs d) (hij : i < j)
    (hqi : q ∣ (term n d i).natAbs) (hqj : q ∣ (term n d j).natAbs) : q ≤ j - i := by
  have hdvd := common_divisor_dvd_index_sub hprimitive
    (Int.ofNat_dvd_left.mpr hqi) (Int.ofNat_dvd_left.mpr hqj)
  have hdvd' : q ∣ j - i := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [Nat.cast_sub hij.le] using hdvd
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hdvd'

/-- Even the boundary divisor `q = k` can occur in at most one of the first
`k` terms. This is stronger than the large-prime uniqueness needed later. -/
theorem index_eq_of_large_common_divisor {n : ℤ} {d i j q k : ℕ}
    (hprimitive : Nat.Coprime n.natAbs d) (hi : i < k) (hj : j < k) (hq : k ≤ q)
    (hqi : q ∣ (term n d i).natAbs) (hqj : q ∣ (term n d j).natAbs) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · have := common_divisor_le_index_gap hprimitive hij hqi hqj
    omega
  · exact hij
  · have := common_divisor_le_index_gap hprimitive hji hqj hqi
    omega

end PerfectPowers
