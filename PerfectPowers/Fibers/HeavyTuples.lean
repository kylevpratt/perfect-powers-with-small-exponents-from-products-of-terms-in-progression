module

public import PerfectPowers.Fibers.LightMass
public import PerfectPowers.Combinatorics.BlockTuples
import Mathlib.Tactic

/-! # Disjoint tuples covering most of the heavy-fiber mass -/

public section

namespace PerfectPowers.Decomposition

variable {k ell d : ℕ} {n : ℤ} {S : Finset ℕ} (D : Decomposition k ell n d S)

theorem heavy_fiber_eq (I : GoodIndices D) (m : ℕ) {a : ℕ}
    (ha : a ≤ k) (hheavy : m < (D.fiber I.indices a).card) :
    ((D.heavyIndices I m).filter (fun i => (D.a i).natAbs = a)) = D.fiber I.indices a := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiH, hia⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiH).1, hia⟩
  · intro hi
    obtain ⟨hiI, hia⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hiI, ?_, ?_⟩, hia⟩
    · simpa only [hia] using ha
    · simpa only [hia] using hheavy

theorem exists_heavy_short_tuples (I : GoodIndices D) {m L : ℕ} (hL : 0 < L)
    (hS : S ⊆ Finset.range k) :
    ∃ family : Finset (Finset ℕ),
      (∀ U ∈ family, U ⊆ D.heavyIndices I m ∧ U.card = m + 1 ∧
        ∃ a : ℕ, 1 ≤ a ∧ a ≤ k ∧ (∀ i ∈ U, (D.a i).natAbs = a) ∧
          ∀ i ∈ U, ∀ j ∈ U, Nat.dist i j < a * L) ∧
      (∀ U ∈ family, ∀ V ∈ family, U ≠ V → Disjoint U V) ∧
      ((D.heavyIndices I m).card : ℝ) ≤ ((m : ℝ) + 1) ^ 2 * family.card +
        (m : ℝ) * ((m : ℝ) + 1) * ((k : ℝ) / L) * (1 + Real.log (k : ℝ)) := by
  classical
  apply exists_disjoint_short_block_tuples (D.heavyIndices I m) (fun i => (D.a i).natAbs)
  · intro i hi
    exact hS (I.subset (Finset.mem_filter.mp hi).1)
  · intro i hi
    obtain ⟨hiI, hik, hmi⟩ := Finset.mem_filter.mp hi
    exact ⟨Int.natAbs_pos.mpr (D.smooth i (I.subset hiI)).1, hik⟩
  · exact hL
  · intro a ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
    obtain ⟨hiI, hik, hmi⟩ := Finset.mem_filter.mp hi
    have haK : a ≤ k := by simpa only [hia] using hik
    have hmass : m < (D.fiber I.indices a).card := by simpa only [hia] using hmi
    rw [D.heavy_fiber_eq I m haK hmass]
    omega

end PerfectPowers.Decomposition
