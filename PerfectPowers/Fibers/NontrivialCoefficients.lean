module

public import PerfectPowers.Fibers.MassExpansion
public import PerfectPowers.Arithmetic.ManySmallTerms
import Mathlib.Tactic

/-! # Removing coefficients represented only by trivial power parts -/

@[expose] public section

namespace PerfectPowers.Decomposition

variable {k ell d : ℕ} {n : ℤ} {S : Finset ℕ} (D : Decomposition k ell n d S)

def nontrivialSmall (I : GoodIndices D) : Finset ℕ :=
  (D.smallIndices I).filter (fun i => D.x i ≠ 1)

def nontrivialCoefficients (I : GoodIndices D) : Finset ℕ :=
  (D.nontrivialSmall I).image (fun i => (D.a i).natAbs)

theorem nontrivialCoefficients_subset (I : GoodIndices D) :
    D.nontrivialCoefficients I ⊆ Finset.Icc 1 k := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hiK, hxi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hiI, hai⟩ := Finset.mem_filter.mp hiK
  exact Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr (D.smooth i (I.subset hiI)).1, hai⟩

theorem represented_card_le_nontrivial_add_trivial (I : GoodIndices D) :
    (D.representedSmall I).card ≤ (D.nontrivialCoefficients I).card +
      (smallTrivialIndices D I.indices).card := by
  classical
  let G := smallTrivialIndices D I.indices
  have hsub : D.representedSmall I ⊆ D.nontrivialCoefficients I ∪ G.image (fun i => (D.a i).natAbs) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    by_cases hxi : D.x i = 1
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2, hxi⟩, rfl⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩, rfl⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have himage : (G.image (fun i => (D.a i).natAbs)).card ≤ G.card := Finset.card_image_le
  change (D.representedSmall I).card ≤ (D.nontrivialCoefficients I).card + G.card
  omega

theorem exists_nontrivial_representatives (I : GoodIndices D) :
    ∃ r : ℕ → ℕ, ∀ a ∈ D.nontrivialCoefficients I,
      r a ∈ S ∧ (D.a (r a)).natAbs = a ∧ D.x (r a) ≠ 1 := by
  classical
  have hex : ∀ a : ℕ, ∃ i : ℕ, a ∈ D.nontrivialCoefficients I →
      i ∈ S ∧ (D.a i).natAbs = a ∧ D.x i ≠ 1 := by
    intro a
    by_cases ha : a ∈ D.nontrivialCoefficients I
    · obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
      obtain ⟨hiK, hxi⟩ := Finset.mem_filter.mp hi
      exact ⟨i, fun _ => ⟨I.subset (Finset.mem_filter.mp hiK).1, hia, hxi⟩⟩
    · exact ⟨0, fun ha' => (ha ha').elim⟩
  choose r hr using hex
  exact ⟨r, hr⟩

end PerfectPowers.Decomposition
