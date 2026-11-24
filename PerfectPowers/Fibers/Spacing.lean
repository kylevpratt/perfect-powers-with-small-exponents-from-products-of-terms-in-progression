module

public import PerfectPowers.Arithmetic.Decomposition
public import PerfectPowers.Combinatorics.SpacedSets
import Mathlib.Tactic

/-! # Coefficient fibers, uniqueness of large coefficients, and spacing -/

@[expose] public section

namespace PerfectPowers

namespace Decomposition

variable {k ell d : ℕ} {n : ℤ} {S : Finset ℕ} (D : Decomposition k ell n d S)

def fiber (I : Finset ℕ) (alpha : ℕ) : Finset ℕ := I.filter (fun i => (D.a i).natAbs = alpha)

theorem equal_coeff_common_divisor {i j alpha : ℕ} (hi : i ∈ S) (hj : j ∈ S)
    (hai : (D.a i).natAbs = alpha) (haj : (D.a j).natAbs = alpha) :
    alpha ∣ (term n d i).natAbs ∧ alpha ∣ (term n d j).natAbs := by
  exact ⟨hai ▸ D.natAbs_a_dvd_term hi, haj ▸ D.natAbs_a_dvd_term hj⟩

/-- Lemma 5.2, including the boundary coefficient of absolute value `k`. -/
theorem large_coefficient_unique (hprimitive : Nat.Coprime n.natAbs d)
    (hS : S ⊆ Finset.range k) {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S)
    (hlarge : k ≤ (D.a i).natAbs) (heq : (D.a i).natAbs = (D.a j).natAbs) : i = j := by
  apply index_eq_of_large_common_divisor hprimitive
    (Finset.mem_range.mp (hS hi)) (Finset.mem_range.mp (hS hj)) hlarge
  · exact D.natAbs_a_dvd_term hi
  · exact heq.symm ▸ D.natAbs_a_dvd_term hj

theorem fiber_spacing (hprimitive : Nat.Coprime n.natAbs d) {I : Finset ℕ}
    (hI : I ⊆ S) {alpha i j : ℕ} (hi : i ∈ D.fiber I alpha) (hj : j ∈ D.fiber I alpha)
    (hne : i ≠ j) : alpha ≤ Nat.dist i j := by
  obtain ⟨hiI, hai⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjI, haj⟩ := Finset.mem_filter.mp hj
  obtain ⟨hdi, hdj⟩ := D.equal_coeff_common_divisor (hI hiI) (hI hjI) hai haj
  rcases lt_or_gt_of_ne hne with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij.le]
    exact common_divisor_le_index_gap hprimitive hij hdi hdj
  · rw [Nat.dist_eq_sub_of_le_right hji.le]
    exact common_divisor_le_index_gap hprimitive hji hdj hdi

/-- Integer form of Lemma 5.6; it implies the stated real quotient bound. -/
theorem fiber_card_le (hprimitive : Nat.Coprime n.natAbs d)
    (hS : S ⊆ Finset.range k) {I : Finset ℕ} (hI : I ⊆ S)
    {alpha : ℕ} (halpha : 0 < alpha) : (D.fiber I alpha).card ≤ k / alpha + 1 := by
  apply card_le_div_add_one_of_spacing halpha
  · exact fun i hi => hS (hI (Finset.mem_filter.mp hi).1)
  · exact fun i hi j hj hne => D.fiber_spacing hprimitive hI hi hj hne

end Decomposition
end PerfectPowers
