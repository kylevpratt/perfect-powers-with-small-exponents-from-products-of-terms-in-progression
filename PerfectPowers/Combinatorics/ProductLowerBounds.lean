module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Lower bounds for products of distinct positive coefficients -/

public section

namespace PerfectPowers

theorem ascFactorial_card_le_prod (S : Finset ℕ) (k : ℕ) (hb : ∀ a ∈ S, k ≤ a) :
    k.ascFactorial S.card ≤ ∏ a ∈ S, a := by
  classical
  induction S using Finset.strongInductionOn generalizing k with
  | _ S ih =>
    by_cases hne : S.Nonempty
    · let a := S.min' hne
      have ha : a ∈ S := Finset.min'_mem S hne
      have hrec : (k + 1).ascFactorial (S.erase a).card ≤ ∏ b ∈ S.erase a, b := by
        apply ih (S.erase a) (Finset.erase_ssubset ha) (k + 1)
        intro b hb'
        have hbS := Finset.mem_of_mem_erase hb'
        have hab : a ≤ b := Finset.min'_le S b hbS
        have hba : b ≠ a := (Finset.mem_erase.mp hb').1
        have hka := hb a ha
        omega
      have hc : (S.erase a).card + 1 = S.card := Finset.card_erase_add_one ha
      rw [← hc, Nat.ascFactorial_succ, ← Nat.succ_ascFactorial]
      calc
        k * (k + 1).ascFactorial (S.erase a).card ≤ a * ∏ b ∈ S.erase a, b :=
          Nat.mul_le_mul (hb a ha) hrec
        _ = ∏ b ∈ insert a (S.erase a), b := by rw [Finset.prod_insert (by simp)]
        _ = ∏ b ∈ S, b := by rw [Finset.insert_erase ha]
    · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hS]

theorem ascFactorial_card_le_prod_of_injOn {ι : Type*} (S : Finset ι) (b : ι → ℕ)
    (k : ℕ) (hinj : Set.InjOn b (↑S : Set ι)) (hb : ∀ i ∈ S, k ≤ b i) :
    k.ascFactorial S.card ≤ ∏ i ∈ S, b i := by
  classical
  have himage : ∀ a ∈ S.image b, k ≤ a := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hb i hi
  have h := ascFactorial_card_le_prod (S.image b) k himage
  rw [Finset.card_image_of_injOn hinj, Finset.prod_image hinj] at h
  exact h

end PerfectPowers
