module

public import PerfectPowers.Curves.TupleConstruction
public import PerfectPowers.Fibers.TrivialParts
import Mathlib.Tactic

/-!
# Curves from tuples in one absolute-coefficient fiber

The curve coefficient has absolute value one. A numerator support of size at
least three contains a nontrivial power part, because at most two entries in
any such fiber have `x_i = 1`. This avoids discarding entire bad fibers.

Coordinate difference from (5.4)--(5.5) in the paper: `ProgressionTuple`
uses the signed coordinate `X = (a_i/f)*x_i^ell/d`, so the shifts are always
positive. The draft keeps `X` positive and allows a common sign on its
shifts. Absorbing that sign into `X` and the signed coefficient gives the
same equations and permits the positive-shift genus input in both curve
applications. See `PerfectPowers.PaperComparison`.
-/

public section

namespace PerfectPowers.ProgressionTuple

variable {k ell d m : ℕ} {n : ℤ} {S : Finset ℕ}
    {D : Decomposition k ell n d S} (T : ProgressionTuple D m)

theorem quotient_natAbs_eq_one {i : ℕ} (hdiv : (T.f : ℤ) ∣ D.a i)
    (habs : (D.a i).natAbs = T.f) : (T.quotient i).natAbs = 1 := by
  have hfactor := congrArg Int.natAbs (T.quotient_factor hdiv)
  simp only [Int.natAbs_mul, Int.natAbs_natCast, habs] at hfactor
  have hmul : T.f * (T.quotient i).natAbs = T.f * 1 := by simpa using hfactor.symm
  exact Nat.eq_of_mul_eq_mul_left T.f_pos hmul

theorem coefficient_natAbs_eq_one (habs : ∀ j, (D.a (T.index j)).natAbs = T.f) :
    T.coefficient.natAbs = 1 := by
  unfold coefficient
  rw [Int.natAbs_prod]
  have hq : ∀ j, (T.quotient (T.index j)).natAbs = 1 :=
    fun j => T.quotient_natAbs_eq_one (T.index_dvd j) (habs j)
  simp only [hq, Finset.prod_const_one]

theorem shift_le_of_short_gaps (hprimitive : Nat.Coprime n.natAbs d) {L : ℕ}
    (hgap : ∀ j, T.index j - T.base < T.f * L) (j : Fin m) : T.shift j ≤ (L : ℤ) := by
  have hfactor := T.shift_factor hprimitive j
  have hgapZ : (T.index j : ℤ) - (T.base : ℤ) < (T.f : ℤ) * (L : ℤ) := by
    rw [← Nat.cast_sub (T.base_lt j).le]
    exact_mod_cast (show T.index j - T.base < T.f * L from hgap j)
  have hf : (0 : ℤ) < T.f := by exact_mod_cast T.f_pos
  nlinarith

theorem support_has_nontrivial (hd : 0 < d) (hm : 3 ≤ m)
    (habs : ∀ j, (D.a (T.index j)).natAbs = T.f) : ∃ i ∈ T.support, 1 < D.x i := by
  classical
  by_contra hn
  push Not at hn
  have hsub : T.support ⊆ D.trivialFiber S T.f := by
    intro i hi
    obtain ⟨j, rfl⟩ := mem_support.mp hi
    have hxpos := D.x_pos (T.index j) (T.index_mem j)
    have hxle := hn (T.index j) (mem_support.mpr ⟨j, rfl⟩)
    exact Finset.mem_filter.mpr ⟨T.index_mem j, habs j, by omega⟩
  have hcard := (Finset.card_le_card hsub).trans (D.trivialFiber_card_le_two hd (Finset.Subset.refl S) T.f)
  rw [T.card_support] at hcard
  omega

end PerfectPowers.ProgressionTuple
