module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Disjoint monochromatic tuples

This is the finite fiber-extraction step in the elementary replacement for
Lemma 4.4. The remainder after extraction has at most `m` elements per label.
The bound below avoids floors and is stronger than the extraction bound used
in the draft.
-/

public section

namespace PerfectPowers

theorem exists_disjoint_monochromatic_tuples {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (B : Finset ι) (F : Finset κ) (g : ι → κ) (m : ℕ)
    (hmap : ∀ b ∈ B, g b ∈ F) :
    ∃ family : Finset (Finset ι),
      (∀ U ∈ family, U ⊆ B ∧ U.card = m + 1 ∧ ∃ f ∈ F, ∀ b ∈ U, g b = f) ∧
      (∀ U ∈ family, ∀ V ∈ family, U ≠ V → Disjoint U V) ∧
      B.card ≤ (m + 1) * family.card + m * F.card := by
  classical
  revert hmap
  induction B using Finset.strongInductionOn with
  | _ B ih =>
    intro hmap
    by_cases hex : ∃ U : Finset ι, U ⊆ B ∧ U.card = m + 1 ∧ ∃ f ∈ F, ∀ b ∈ U, g b = f
    · obtain ⟨U, hUB, hUcard, hcolor⟩ := hex
      have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
      have hproper : B \ U ⊂ B := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        obtain ⟨b, hb⟩ := hUne
        have hrest : b ∈ B \ U := by rw [heq]; exact hUB hb
        exact (Finset.mem_sdiff.mp hrest).2 hb
      obtain ⟨family, hprop, hpair, hcard⟩ := ih (B \ U) hproper
        (fun b hb => hmap b (Finset.mem_sdiff.mp hb).1)
      have hdis (V : Finset ι) (hV : V ∈ family) : Disjoint U V := by
        apply Finset.disjoint_left.mpr
        intro b hbU hbV
        exact (Finset.mem_sdiff.mp ((hprop V hV).1 hbV)).2 hbU
      have hnot : U ∉ family := by
        intro hU
        obtain ⟨b, hb⟩ := hUne
        exact Finset.disjoint_left.mp (hdis U hU) hb hb
      refine ⟨insert U family, ?_, ?_, ?_⟩
      · intro V hV
        rcases Finset.mem_insert.mp hV with rfl | hV
        · exact ⟨hUB, hUcard, hcolor⟩
        · exact ⟨(hprop V hV).1.trans Finset.sdiff_subset, (hprop V hV).2⟩
      · intro V hV W hW hVW
        rcases Finset.mem_insert.mp hV with hVU | hVf
        · subst V
          rcases Finset.mem_insert.mp hW with hWU | hWf
          · subst W
            exact (hVW rfl).elim
          · exact hdis W hWf
        · rcases Finset.mem_insert.mp hW with hWU | hWf
          · subst W
            exact (hdis V hVf).symm
          · exact hpair V hVf W hWf hVW
      · rw [Finset.card_insert_of_notMem hnot]
        have hc := Finset.card_sdiff_add_card_eq_card hUB
        nlinarith
    · have hcard : B.card ≤ m * F.card := by
        by_contra hn
        have hmul : F.card * m < B.card := by nlinarith
        obtain ⟨f, hf, hfiber⟩ :=
          Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap hmul
        obtain ⟨U, hU, hUcard⟩ := Finset.exists_subset_card_eq (show m + 1 ≤
          (B.filter (fun b => g b = f)).card by omega)
        apply hex
        exact ⟨U, hU.trans (Finset.filter_subset _ _), hUcard, f, hf,
          fun b hb => (Finset.mem_filter.mp (hU hb)).2⟩
      exact ⟨∅, by simp, by simp, by simpa using hcard⟩

end PerfectPowers
