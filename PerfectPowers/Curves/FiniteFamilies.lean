module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Finite boxes of curve descriptors

The descriptor box deliberately includes zero `B` and repeated shifts. Those
extra descriptors only enlarge an upper bound; no injectivity claim about
descriptors and polynomials is needed. Counting uses these boxes directly;
there is no separate representation as a finite set of polynomials.
-/

@[expose] public section

namespace PerfectPowers

noncomputable def boundedCurveDescriptors (m M L : ℕ) : Finset (ℤ × (Fin m → ℤ)) :=
  (Finset.Icc (-(M : ℤ)) (M : ℤ)).product
    (Fintype.piFinset (fun _ : Fin m => Finset.Icc (1 : ℤ) (L : ℤ)))

theorem card_boundedCurveDescriptors (m M L : ℕ) :
    (boundedCurveDescriptors m M L).card = (2 * M + 1) * L ^ m := by
  have hB : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    omega
  have hC : (Finset.Icc (1 : ℤ) (L : ℤ)).card = L := by
    rw [Int.card_Icc]
    omega
  simp [boundedCurveDescriptors, hB, hC]

theorem mem_boundedCurveDescriptors {m M L : ℕ} {B : ℤ} {C : Fin m → ℤ} :
    (B, C) ∈ boundedCurveDescriptors m M L ↔
      (-(M : ℤ) ≤ B ∧ B ≤ (M : ℤ)) ∧ ∀ j, 1 ≤ C j ∧ C j ≤ (L : ℤ) := by
  simp [boundedCurveDescriptors, Fintype.mem_piFinset]

end PerfectPowers
