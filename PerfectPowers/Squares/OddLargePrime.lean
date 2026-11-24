module

public import PerfectPowers.Arithmetic.LargePrimes
public import PerfectPowers.Squares.OddPrefixes
import Mathlib.Tactic

/-! # A square odd progression with a large prime must start beyond k² -/

public section

namespace PerfectPowers

theorem odd_square_start_large_of_prime {k m p : ℕ} (_hk : 2 ≤ k)
    (hm : 0 < m) (hodd : Odd m) (hp : p.Prime) (hpk : k < p)
    (hdiv : p ∣ ∏ i ∈ Finset.range k, (m + 2 * i))
    (hsq : IsSquare (∏ i ∈ Finset.range k, (m + 2 * i))) : k ^ 2 + 3 ≤ m := by
  classical
  obtain ⟨z, hz⟩ := hsq
  have hprodpos : 0 < ∏ i ∈ Finset.range k, (m + 2 * i) := Finset.prod_pos (by intros; omega)
  have hzpos : 0 < z := by nlinarith
  have hprod : progressionProduct (m : ℤ) 2 (Finset.range k) =
      ((∏ i ∈ Finset.range k, (m + 2 * i) : ℕ) : ℤ) := by
    simp only [progressionProduct, term, Nat.cast_prod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    congr 1
    ext i
    ring
  have hsol : Solution k 2 (m : ℤ) 2 1 (z : ℤ) (Finset.range k) := {
    index_subset := Finset.Subset.refl _
    n_ne_zero := by exact_mod_cast hm.ne'
    d_pos := by norm_num
    b_ne_zero := by norm_num
    y_ne_zero := by exact_mod_cast hzpos.ne'
    coprime := by simpa only [Int.natAbs_natCast] using (Nat.coprime_two_right.mpr hodd)
    b_smooth := smooth_one k
    equation := by rw [hprod, hz]; push_cast; ring }
  obtain ⟨i, hi, hpi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdiv
  have hipos : 0 < m + 2 * i := by omega
  have hnat : (term (m : ℤ) 2 i).natAbs = m + 2 * i := by
    have heq : term (m : ℤ) 2 i = ((m + 2 * i : ℕ) : ℤ) := by simp [term]; ring
    rw [heq, Int.natAbs_natCast]
  have hval := hsol.large_prime_valuation_multiple hi hp hpk
  rw [hnat] at hval
  have hvpos := (hp.dvd_iff_one_le_factorization hipos.ne').mp hpi
  have hv2 : 2 ≤ (m + 2 * i).factorization p := Nat.le_of_dvd (by omega) hval
  have hp2 : p ^ 2 ∣ m + 2 * i := (hp.pow_dvd_iff_le_factorization hipos.ne').mpr hv2
  have hsize := Nat.le_of_dvd hipos hp2
  have hik : i < k := Finset.mem_range.mp hi
  have hpsq : (k + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
  nlinarith

end PerfectPowers
