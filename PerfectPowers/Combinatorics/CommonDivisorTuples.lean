module

public import PerfectPowers.Combinatorics.MinimalDivisors
import Mathlib.Tactic

/-!
# Common-divisor tuples with an explicit counting remainder

All analytic information is isolated in the cardinality of `roughIntegers`.
The elementary sieve bound required to finish the replacement for Lemma 4.4
is a separate obligation, not an assumption hidden in these theorems.
-/

public section

namespace PerfectPowers

theorem exists_disjoint_common_divisor_tuples {k : ℕ} {t : ℝ}
    (B : Finset ℕ) (m : ℕ) (hB : B ⊆ Finset.Icc 1 k)
    (htB : ∀ b ∈ B, t < (b : ℝ)) :
    ∃ family : Finset (Finset ℕ),
      (∀ U ∈ family, U ⊆ B ∧ U.card = m + 1 ∧
        ∃ f : ℕ, t < (f : ℝ) ∧ ∀ b ∈ U, f ∣ b) ∧
      (∀ U ∈ family, ∀ V ∈ family, U ≠ V → Disjoint U V) ∧
      B.card ≤ (m + 1) * family.card + m * (minimalLargeDivisors k t).card := by
  classical
  have hex : ∀ b : ℕ, ∃ f : ℕ, b ∈ B → f ∈ minimalLargeDivisors k t ∧ f ∣ b := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨f, hf, hfb⟩ := exists_minimal_large_divisor
        (Finset.mem_Icc.mp (hB hb)).1 (Finset.mem_Icc.mp (hB hb)).2 (htB b hb)
      exact ⟨f, fun _ => ⟨hf, hfb⟩⟩
    · exact ⟨1, fun hb' => (hb hb').elim⟩
  choose g hg using hex
  obtain ⟨family, hprop, hdis, hcard⟩ := exists_disjoint_monochromatic_tuples B
    (minimalLargeDivisors k t) g m (fun b hb => (hg b hb).1)
  refine ⟨family, ?_, hdis, hcard⟩
  intro U hU
  obtain ⟨hUB, hUc, f, hf, hcolor⟩ := hprop U hU
  refine ⟨hUB, hUc, f, (Finset.mem_filter.mp hf).2.1, ?_⟩
  intro b hb
  rw [← hcolor b hb]
  exact (hg b (hUB hb)).2

theorem exists_common_divisor_tuples_with_rough_error {k : ℕ} {t A : ℝ}
    (B : Finset ℕ) (m : ℕ) (hB : B ⊆ Finset.Icc 1 k) (ht : 0 ≤ t) (hA : 0 ≤ A) :
    ∃ family : Finset (Finset ℕ),
      (∀ U ∈ family, U ⊆ B ∧ U.card = m + 1 ∧
        ∃ f : ℕ, t < (f : ℝ) ∧ ∀ b ∈ U, f ∣ b) ∧
      (∀ U ∈ family, ∀ V ∈ family, U ≠ V → Disjoint U V) ∧
      (B.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * family.card +
        ((m : ℝ) * A + 1) * t + (m : ℝ) * (roughIntegers k A).card := by
  classical
  let B' := B.filter (fun b : ℕ => t < (b : ℝ))
  obtain ⟨family, hprop, hdis, hcard⟩ := exists_disjoint_common_divisor_tuples B' m
    ((Finset.filter_subset _ _).trans hB) (fun b hb => (Finset.mem_filter.mp hb).2)
  refine ⟨family, ?_, hdis, ?_⟩
  · intro U hU
    exact ⟨(hprop U hU).1.trans (Finset.filter_subset _ _), (hprop U hU).2⟩
  · have hsmall : ((B.filter (fun b : ℕ => ¬t < (b : ℝ))).card : ℝ) ≤ t := by
      apply card_positive_nat_below_real_le ht
      intro b hb
      obtain ⟨hbB, hbt⟩ := Finset.mem_filter.mp hb
      exact ⟨(Finset.mem_Icc.mp (hB hbB)).1, le_of_not_gt hbt⟩
    have hsplit : B'.card + (B.filter (fun b : ℕ => ¬t < (b : ℝ))).card = B.card :=
      Finset.card_filter_add_card_filter_not _
    have hsplitR : (B'.card : ℝ) + (B.filter (fun b : ℕ => ¬t < (b : ℝ))).card = B.card := by
      exact_mod_cast hsplit
    have hcardR : (B'.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * family.card +
        (m : ℝ) * (minimalLargeDivisors k t).card := by exact_mod_cast hcard
    have hF := mul_le_mul_of_nonneg_left (card_minimalLargeDivisors_le (k := k) ht hA)
      (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith

end PerfectPowers
