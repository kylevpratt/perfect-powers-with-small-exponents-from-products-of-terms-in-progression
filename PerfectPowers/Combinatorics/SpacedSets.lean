module

public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! # Counting separated indices by an injective quotient map -/

public section

namespace PerfectPowers

/-- At most one point of a `q`-separated set lies in each quotient block. -/
theorem card_le_pred_div_add_one_of_spacing {J : Finset ℕ} {k q : ℕ} (hq : 0 < q)
    (hJ : J ⊆ Finset.range k)
    (hspace : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → q ≤ Nat.dist i j) :
    J.card ≤ (k - 1) / q + 1 := by
  classical
  have hinj : Set.InjOn (fun i : ℕ => i / q) (↑J : Set ℕ) := by
    intro i hi j hj hij
    by_contra hne
    have hgap := hspace i hi j hj hne
    have hdi := Nat.div_add_mod i q
    have hdj := Nat.div_add_mod j q
    have hmi := Nat.mod_lt i hq
    have hmj := Nat.mod_lt j hq
    change i / q = j / q at hij
    rw [hij] at hdi
    rcases le_total i j with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle] at hgap
      omega
    · rw [Nat.dist_eq_sub_of_le_right hle] at hgap
      omega
  calc
    J.card = (J.image (fun i => i / q)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range ((k - 1) / q + 1)).card := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have hik := Finset.mem_range.mp (hJ hi)
      apply Finset.mem_range.mpr
      have := Nat.div_le_div_right (c := q) (show i ≤ k - 1 by omega)
      omega
    _ = (k - 1) / q + 1 := Finset.card_range _

theorem card_le_div_add_one_of_spacing {J : Finset ℕ} {k q : ℕ} (hq : 0 < q)
    (hJ : J ⊆ Finset.range k)
    (hspace : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → q ≤ Nat.dist i j) :
    J.card ≤ k / q + 1 := by
  exact (card_le_pred_div_add_one_of_spacing hq hJ hspace).trans
    (Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le k 1)) 1)

end PerfectPowers
