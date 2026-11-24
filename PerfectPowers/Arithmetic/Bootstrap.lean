module

public import PerfectPowers.Arithmetic.Decomposition
import Mathlib.Tactic

/-!
# The finite smoothness bootstrap in the proof of Theorem 1.5

After bounding the step, one small term with trivial power part bounds every
term. A nontrivial rough power part would then make its term too large.
-/

public section

namespace PerfectPowers.Decomposition

variable {k ell d : ℕ} {n : ℤ} {S : Finset ℕ} (D : Decomposition k ell n d S)

theorem start_bound_of_small_trivial_term (hS : S ⊆ Finset.range k)
    {i0 : ℕ} (hi0 : i0 ∈ S) (ha0 : (D.a i0).natAbs ≤ k) (hx0 : D.x i0 = 1) :
    n.natAbs ≤ k * (d + 1) := by
  have hi0k : i0 < k := Finset.mem_range.mp (hS hi0)
  have ht0 : (term n d i0).natAbs ≤ k := by
    rw [D.factor i0 hi0, hx0]
    simpa using ha0
  have hn : n = term n d i0 - (i0 : ℤ) * (d : ℤ) := by simp [term]
  have htri := Int.natAbs_sub_le (term n d i0) ((i0 : ℤ) * (d : ℤ))
  rw [← hn] at htri
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at htri
  nlinarith

theorem all_power_parts_eq_one_of_step_bound (hell : 2 ≤ ell) (hS : S ⊆ Finset.range k)
    {i0 : ℕ} (hi0 : i0 ∈ S) (ha0 : (D.a i0).natAbs ≤ k) (hx0 : D.x i0 = 1)
    (hstep : k * (2 * d + 1) < (k + 1) ^ 2) : ∀ i ∈ S, D.x i = 1 := by
  have hn := D.start_bound_of_small_trivial_term hS hi0 ha0 hx0
  intro i hi
  have hik : i < k := Finset.mem_range.mp (hS hi)
  have htermbound : (term n d i).natAbs ≤ k * (2 * d + 1) := by
    have htri := Int.natAbs_add_le n ((i : ℤ) * (d : ℤ))
    change (term n d i).natAbs ≤ _ at htri
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at htri
    nlinarith
  by_contra hxi
  have hxlarge : k < D.x i := (D.rough i hi).eq_one_or_gt.resolve_left hxi
  have hxmin : k + 1 ≤ D.x i := by omega
  have hx1 : 1 ≤ D.x i := D.x_pos i hi
  have hpow : (D.x i) ^ 2 ≤ (D.x i) ^ ell := pow_le_pow_right₀ hx1 hell
  have hpowmin : (k + 1) ^ 2 ≤ (D.x i) ^ 2 := Nat.pow_le_pow_left hxmin 2
  have ha1 : 1 ≤ (D.a i).natAbs := Int.natAbs_pos.mpr (D.smooth i hi).1
  have hfactor : (term n d i).natAbs = (D.a i).natAbs * (D.x i) ^ ell := by
    rw [D.factor i hi, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  have hpowterm : (D.x i) ^ ell ≤ (term n d i).natAbs := by
    rw [hfactor]
    simpa only [one_mul] using Nat.mul_le_mul_right ((D.x i) ^ ell) ha1
  omega

theorem product_smooth_of_step_bound (hell : 2 ≤ ell) (hS : S ⊆ Finset.range k)
    {i0 : ℕ} (hi0 : i0 ∈ S) (ha0 : (D.a i0).natAbs ≤ k) (hx0 : D.x i0 = 1)
    (hstep : k * (2 * d + 1) < (k + 1) ^ 2) : Smooth k (progressionProduct n d S) := by
  have hx := D.all_power_parts_eq_one_of_step_bound hell hS hi0 ha0 hx0 hstep
  apply smooth_prod
  intro i hi
  rw [D.factor i hi, hx i hi]
  simpa using D.smooth i hi

end PerfectPowers.Decomposition
