module

public import PerfectPowers.Arithmetic.GoodIndices
public import PerfectPowers.Fibers.Spacing
public import PerfectPowers.Combinatorics.ProductLowerBounds
import Mathlib.Tactic

/-! # The factorial constraint on the number of coefficients larger than `k` -/

@[expose] public section

namespace PerfectPowers
namespace Decomposition

variable {k ell d : ℕ} {n : ℤ} {S : Finset ℕ} (D : Decomposition k ell n d S)

def largeIndices (I : GoodIndices D) : Finset ℕ :=
  I.indices.filter (fun i => k < (D.a i).natAbs)

def smallIndices (I : GoodIndices D) : Finset ℕ :=
  I.indices.filter (fun i => (D.a i).natAbs ≤ k)

theorem small_large_card (I : GoodIndices D) :
    (D.smallIndices I).card + (D.largeIndices I).card = I.indices.card := by
  have hcompl : D.smallIndices I = I.indices \ D.largeIndices I := by
    ext i
    by_cases hi : i ∈ I.indices <;> simp [smallIndices, largeIndices, hi]
  rw [hcompl]
  exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)

theorem large_indices_factorial_le_square (I : GoodIndices D)
    (hprimitive : Nat.Coprime n.natAbs d) (hS : S ⊆ Finset.range k) :
    (k + (D.largeIndices I).card).factorial ≤ k.factorial ^ 2 := by
  classical
  let L := D.largeIndices I
  have hL : L ⊆ I.indices := Finset.filter_subset _ _
  have hinj : Set.InjOn (fun i => (D.a i).natAbs) (↑L : Set ℕ) := by
    intro i hi j hj heq
    exact D.large_coefficient_unique hprimitive hS (I.subset (hL hi)) (I.subset (hL hj))
      (Finset.mem_filter.mp hi).2.le heq
  have hbound : (k + 1).ascFactorial L.card ≤ ∏ i ∈ L, (D.a i).natAbs := by
    apply ascFactorial_card_le_prod_of_injOn L _ (k + 1) hinj
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hprodpos : 0 < ∏ i ∈ I.indices, (D.a i).natAbs := by
    apply Finset.prod_pos
    intro i hi
    exact Int.natAbs_pos.mpr (D.smooth i (I.subset hi)).1
  have hbound' : (k + 1).ascFactorial L.card ≤ k.factorial :=
    hbound.trans ((Nat.le_of_dvd hprodpos (Finset.prod_dvd_prod_of_subset L I.indices _ hL)).trans
      I.product_le_factorial)
  calc
    (k + L.card).factorial = k.factorial * (k + 1).ascFactorial L.card :=
      (Nat.factorial_mul_ascFactorial k L.card).symm
    _ ≤ k.factorial * k.factorial := Nat.mul_le_mul_left _ hbound'
    _ = k.factorial ^ 2 := by ring

end Decomposition
end PerfectPowers
