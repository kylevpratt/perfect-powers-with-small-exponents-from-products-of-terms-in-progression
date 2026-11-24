module

public import PerfectPowers.Combinatorics.ProductLowerBounds
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Products with bounded multiplicities

If positive integers occur at most `m` times, their product times `m^N`
dominates `N!`. Taking logarithms gives the entropy estimate needed for
Lemma 5.5 without introducing a floor or a factorial rounding error.
-/

public section

namespace PerfectPowers

theorem card_le_mul_of_fiber_bound {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (A : Finset κ) (b : ι → κ) (m : ℕ)
    (hmap : ∀ i ∈ S, b i ∈ A) (hcap : ∀ a ∈ A, (S.filter (fun i => b i = a)).card ≤ m) :
    S.card ≤ m * A.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ _a ∈ A, m := Finset.sum_le_sum hcap
    _ = m * A.card := by simp [mul_comm]

theorem factorial_le_pow_mul_prod_of_multiplicity {ι : Type*}
    (S : Finset ι) (b : ι → ℕ) (m : ℕ)
    (hpos : ∀ i ∈ S, 0 < b i)
    (hcap : ∀ a : ℕ, (S.filter (fun i => b i = a)).card ≤ m) :
    S.card.factorial ≤ m ^ S.card * ∏ i ∈ S, b i := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image S b hS
      have hcard : S.card ≤ m * b i := by
        have h := card_le_mul_of_fiber_bound S (Finset.Icc 1 (b i)) b m
          (fun j hj => Finset.mem_Icc.mpr ⟨hpos j hj, hmax j hj⟩)
          (fun a _ => hcap a)
        simpa using h
      have hrec : (S.erase i).card.factorial ≤ m ^ (S.erase i).card * ∏ j ∈ S.erase i, b j := by
        apply ih (S.erase i) (Finset.erase_ssubset hi)
        · intro j hj
          exact hpos j (Finset.mem_of_mem_erase hj)
        · intro a
          exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset i S))).trans (hcap a)
      have hc : (S.erase i).card + 1 = S.card := Finset.card_erase_add_one hi
      rw [← hc, Nat.factorial_succ, pow_succ]
      calc
        ((S.erase i).card + 1) * (S.erase i).card.factorial ≤
            (m * b i) * (m ^ (S.erase i).card * ∏ j ∈ S.erase i, b j) := by
          exact Nat.mul_le_mul (by omega) hrec
        _ = (m ^ (S.erase i).card * m) * (b i * ∏ j ∈ S.erase i, b j) := by ring
        _ = _ := by rw [Finset.mul_prod_erase S b hi]
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

end PerfectPowers
