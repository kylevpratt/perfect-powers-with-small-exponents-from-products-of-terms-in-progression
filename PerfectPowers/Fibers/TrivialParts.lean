module

public import PerfectPowers.Fibers.Spacing
import Mathlib.Tactic

/-! # At most two trivial power parts in any absolute-coefficient fiber -/

@[expose] public section

namespace PerfectPowers
namespace Decomposition

variable {k ell d : ℕ} {n : ℤ} {S : Finset ℕ} (D : Decomposition k ell n d S)

def trivialFiber (I : Finset ℕ) (alpha : ℕ) : Finset ℕ :=
  I.filter (fun i => (D.a i).natAbs = alpha ∧ D.x i = 1)

theorem trivialFiber_card_le_two (hd : 0 < d) {I : Finset ℕ} (hI : I ⊆ S) (alpha : ℕ) :
    (D.trivialFiber I alpha).card ≤ 2 := by
  classical
  let J := D.trivialFiber I alpha
  have himage : J.image (term n d) ⊆ ({(alpha : ℤ), -(alpha : ℤ)} : Finset ℤ) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hiI, hai, hxi⟩ := Finset.mem_filter.mp hi
    have hterm : term n d i = D.a i := by simp [D.factor i (hI hiI), hxi]
    rw [hterm]
    rcases Int.natAbs_eq_iff.mp hai with heq | heq <;> simp [heq]
  calc
    J.card = (J.image (term n d)).card :=
      (Finset.card_image_of_injective _ (term_injective n hd)).symm
    _ ≤ ({(alpha : ℤ), -(alpha : ℤ)} : Finset ℤ).card := Finset.card_le_card himage
    _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

end Decomposition
end PerfectPowers
