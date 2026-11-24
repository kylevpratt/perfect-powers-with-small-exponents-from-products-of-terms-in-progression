module

public import PerfectPowers.Main.SquareReduction
public import PerfectPowers.Squares.SignedOddProduct
import Mathlib.Tactic

/-!
# Theorem 1.2 deduced from Theorem 1.4 and Lemma 3.6

The signed classification applies the proved Lemma 3.6 directly; no
separate nonsquareness hypothesis is passed through the main proof.
-/

public section

open Filter

namespace PerfectPowers

theorem theorem12_of_theorem14 {k : ℕ} (hk : 21 ≤ k)
    (h14 : Theorem14At k) : Theorem12At k := by
  intro ell n d y hell hsol
  obtain ⟨hell2, hd2, hnodd, hnlo, hnhi⟩ := square_reduction_of_theorem14 hk h14 hell hsol
  subst ell
  subst d
  have hsq : IsSquare (progressionProduct n 2 (Finset.range k)) := by
    rw [hsol.equation, one_mul]
    exact IsSquare.sq y
  exact ⟨rfl, rfl, step_two_square_classification hnodd hnlo hnhi hsq⟩

theorem mainResults_of_eventually_theorem15
    (h15 : ∀ᶠ k : ℕ in atTop, Theorem15At k) : MainResults := by
  have hAll : ∀ᶠ k : ℕ in atTop, 3 ≤ k ∧ Theorem15At k ∧ Theorem14At k ∧ Theorem12At k := by
    filter_upwards [h15, eventually_theorem14_of_theorem15, eventually_ge_atTop (21 : ℕ)] with k hk h14 hk21
    have h14k := h14 hk
    exact ⟨by omega, hk, h14k, theorem12_of_theorem14 hk21 h14k⟩
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨max 3 k0, by omega, ?_⟩
  intro k hk
  exact (hk0 k (by omega)).2

end PerfectPowers
