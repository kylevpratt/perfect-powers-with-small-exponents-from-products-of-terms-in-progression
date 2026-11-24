module

public import PerfectPowers.Fibers.LargeCoefficients
public import PerfectPowers.Analytic.MultiplicityLog
import Mathlib.Tactic

/-! # Small coefficients in fibers of bounded cardinality -/

@[expose] public section

namespace PerfectPowers.Decomposition

variable {k ell d : ℕ} {n : ℤ} {S : Finset ℕ} (D : Decomposition k ell n d S)

def lightIndices (I : GoodIndices D) (m : ℕ) : Finset ℕ :=
  I.indices.filter (fun i => (D.a i).natAbs ≤ k ∧ (D.fiber I.indices (D.a i).natAbs).card ≤ m)

def heavyIndices (I : GoodIndices D) (m : ℕ) : Finset ℕ :=
  I.indices.filter (fun i => (D.a i).natAbs ≤ k ∧ m < (D.fiber I.indices (D.a i).natAbs).card)

theorem lightIndices_subset_small (I : GoodIndices D) (m : ℕ) :
    D.lightIndices I m ⊆ D.smallIndices I := by
  intro i hi
  obtain ⟨hiI, hiK, hcap⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hiI, hiK⟩

theorem light_heavy_card (I : GoodIndices D) (m : ℕ) :
    (D.lightIndices I m).card + (D.heavyIndices I m).card = (D.smallIndices I).card := by
  have hlight : D.lightIndices I m = (D.smallIndices I).filter
      (fun i => (D.fiber I.indices (D.a i).natAbs).card ≤ m) := by
    ext i
    simp [lightIndices, smallIndices, and_assoc]
  have hheavy : D.heavyIndices I m = (D.smallIndices I).filter
      (fun i => ¬(D.fiber I.indices (D.a i).natAbs).card ≤ m) := by
    ext i
    simp [heavyIndices, smallIndices, and_assoc]
  rw [hlight, hheavy]
  exact Finset.card_filter_add_card_filter_not _

theorem light_fiber_card_le (I : GoodIndices D) (m a : ℕ) :
    ((D.lightIndices I m).filter (fun i => (D.a i).natAbs = a)).card ≤ m := by
  classical
  by_cases hne : ((D.lightIndices I m).filter (fun i => (D.a i).natAbs = a)).Nonempty
  · obtain ⟨i, hi⟩ := hne
    obtain ⟨hi, hai⟩ := Finset.mem_filter.mp hi
    have hcap := (Finset.mem_filter.mp hi).2.2
    rw [hai] at hcap
    have hsub : (D.lightIndices I m).filter (fun i => (D.a i).natAbs = a) ⊆ D.fiber I.indices a := by
      intro j hj
      obtain ⟨hjL, hja⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjL).1, hja⟩
    exact (Finset.card_le_card hsub).trans hcap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

theorem light_mass_log_bound (I : GoodIndices D) {m : ℕ} (hm : 0 < m)
    {N : ℝ} (hmN : (m : ℝ) ≤ N) (hN : N ≤ (D.lightIndices I m).card) :
    N * Real.log (N / m) - N ≤ Real.log ((∏ i ∈ D.smallIndices I, (D.a i).natAbs : ℕ) : ℝ) := by
  have hpos (i : ℕ) (hi : i ∈ D.lightIndices I m) : 0 < (D.a i).natAbs :=
    Int.natAbs_pos.mpr (D.smooth i (I.subset (Finset.mem_filter.mp hi).1)).1
  have hlog := log_prod_lower_of_real_mass (D.lightIndices I m) (fun i => (D.a i).natAbs)
    hm hpos (fun a => D.light_fiber_card_le I m a) hmN hN
  have hsmallpos : 0 < ∏ i ∈ D.smallIndices I, (D.a i).natAbs := by
    apply Finset.prod_pos
    intro i hi
    exact Int.natAbs_pos.mpr (D.smooth i (I.subset (Finset.mem_filter.mp hi).1)).1
  have hdiv := Finset.prod_dvd_prod_of_subset (D.lightIndices I m) (D.smallIndices I)
    (fun i => (D.a i).natAbs) (D.lightIndices_subset_small I m)
  have hle : ((∏ i ∈ D.lightIndices I m, (D.a i).natAbs : ℕ) : ℝ) ≤
      (∏ i ∈ D.smallIndices I, (D.a i).natAbs : ℕ) := by
    exact_mod_cast Nat.le_of_dvd hsmallpos hdiv
  exact hlog.trans (Real.log_le_log (by exact_mod_cast Finset.prod_pos hpos) hle)

theorem small_product_weighted_factorial_le_square (I : GoodIndices D)
    (hprimitive : Nat.Coprime n.natAbs d) (hS : S ⊆ Finset.range k) :
    (∏ i ∈ D.smallIndices I, (D.a i).natAbs) * (k + (D.largeIndices I).card).factorial ≤
      k.factorial ^ 2 := by
  classical
  let L := D.largeIndices I
  have hinj : Set.InjOn (fun i => (D.a i).natAbs) (↑L : Set ℕ) := by
    intro i hi j hj heq
    exact D.large_coefficient_unique hprimitive hS
      (I.subset (Finset.mem_filter.mp hi).1) (I.subset (Finset.mem_filter.mp hj).1)
      (Finset.mem_filter.mp hi).2.le heq
  have hbound : (k + 1).ascFactorial L.card ≤ ∏ i ∈ L, (D.a i).natAbs := by
    apply ascFactorial_card_le_prod_of_injOn L _ (k + 1) hinj
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsplit : (∏ i ∈ D.smallIndices I, (D.a i).natAbs) *
      (∏ i ∈ L, (D.a i).natAbs) = ∏ i ∈ I.indices, (D.a i).natAbs := by
    simpa only [L, smallIndices, largeIndices, not_le] using
      Finset.prod_filter_mul_prod_filter_not I.indices (fun i => (D.a i).natAbs ≤ k)
        (fun i => (D.a i).natAbs)
  have hprod : (∏ i ∈ D.smallIndices I, (D.a i).natAbs) * (k + 1).ascFactorial L.card ≤
      k.factorial := by
    calc
      _ ≤ (∏ i ∈ D.smallIndices I, (D.a i).natAbs) * (∏ i ∈ L, (D.a i).natAbs) :=
        Nat.mul_le_mul_left _ hbound
      _ = _ := hsplit
      _ ≤ _ := I.product_le_factorial
  rw [← Nat.factorial_mul_ascFactorial k L.card]
  calc
    _ = k.factorial * ((∏ i ∈ D.smallIndices I, (D.a i).natAbs) * (k + 1).ascFactorial L.card) := by ring
    _ ≤ k.factorial * k.factorial := Nat.mul_le_mul_left _ hprod
    _ = _ := by ring

end PerfectPowers.Decomposition
