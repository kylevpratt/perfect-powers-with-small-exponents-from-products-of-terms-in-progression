module

public import PerfectPowers.Curves.PointAlgebra
import Mathlib.Tactic

/-!
# Constructing curve equations from a common-divisor tuple

The fields describe only selected indices and a divisor of their signed
coefficients. Integrality, positive distinct shifts, height bounds, and the
rational point are proved from those data.
-/

@[expose] public section

namespace PerfectPowers

structure ProgressionTuple {k ell d : ℕ} {n : ℤ} {S : Finset ℕ}
    (D : Decomposition k ell n d S) (m : ℕ) where
  base : ℕ
  index : Fin m → ℕ
  base_mem : base ∈ S
  index_mem : ∀ j, index j ∈ S
  base_lt : ∀ j, base < index j
  index_injective : Function.Injective index
  f : ℕ
  f_pos : 0 < f
  base_dvd : (f : ℤ) ∣ D.a base
  index_dvd : ∀ j, (f : ℤ) ∣ D.a (index j)

namespace ProgressionTuple

variable {k ell d m : ℕ} {n : ℤ} {S : Finset ℕ}
    {D : Decomposition k ell n d S} (T : ProgressionTuple D m)

def quotient (i : ℕ) : ℤ := D.a i / (T.f : ℤ)

def shift (j : Fin m) : ℤ := ((T.index j - T.base) / T.f : ℕ)

def coefficient : ℤ := ∏ j : Fin m, T.quotient (T.index j)

def point : ℚ × ℚ :=
  ((T.quotient T.base : ℚ) * (D.x T.base : ℚ) ^ ell / (d : ℚ),
    (∏ j : Fin m, (D.x (T.index j) : ℚ)) / (d : ℚ) ^ (m / ell))

theorem quotient_factor {i : ℕ} (hi : (T.f : ℤ) ∣ D.a i) :
    D.a i = (T.f : ℤ) * T.quotient i := by
  have h := Int.ediv_mul_cancel hi
  change D.a i = (T.f : ℤ) * (D.a i / (T.f : ℤ))
  nlinarith

theorem quotient_ne_zero {i : ℕ} (hi : i ∈ S) (hdiv : (T.f : ℤ) ∣ D.a i) :
    T.quotient i ≠ 0 := by
  intro hzero
  have h := T.quotient_factor hdiv
  rw [hzero, mul_zero] at h
  exact (D.smooth i hi).1 h

theorem coefficient_ne_zero : T.coefficient ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact T.quotient_ne_zero (T.index_mem j) (T.index_dvd j)

theorem divisor_dvd_gap (hprimitive : Nat.Coprime n.natAbs d) (j : Fin m) :
    T.f ∣ T.index j - T.base := by
  have hdiv := common_divisor_dvd_index_sub hprimitive
    (T.base_dvd.trans (D.a_dvd_term T.base_mem))
    ((T.index_dvd j).trans (D.a_dvd_term (T.index_mem j)))
  apply Int.natCast_dvd_natCast.mp
  simpa only [Nat.cast_sub (T.base_lt j).le] using hdiv

theorem shift_factor (hprimitive : Nat.Coprime n.natAbs d) (j : Fin m) :
    (T.index j : ℤ) - (T.base : ℤ) = (T.f : ℤ) * T.shift j := by
  have hnat := Nat.div_mul_cancel (T.divisor_dvd_gap hprimitive j)
  dsimp [shift]
  rw [← Nat.cast_sub (T.base_lt j).le]
  exact_mod_cast (show T.index j - T.base = T.f * ((T.index j - T.base) / T.f) by nlinarith)

theorem shift_pos (hprimitive : Nat.Coprime n.natAbs d) (j : Fin m) : 1 ≤ T.shift j := by
  have hfactor := T.shift_factor hprimitive j
  have hi : (T.base : ℤ) < T.index j := by exact_mod_cast T.base_lt j
  have hf : (0 : ℤ) < T.f := by exact_mod_cast T.f_pos
  nlinarith

theorem shift_injective (hprimitive : Nat.Coprime n.natAbs d) : Function.Injective T.shift := by
  intro i j hij
  have hi := T.shift_factor hprimitive i
  have hj := T.shift_factor hprimitive j
  rw [hij] at hi
  apply T.index_injective
  have heq : (T.index i : ℤ) = T.index j := by linarith
  exact_mod_cast heq

theorem shift_le (hS : S ⊆ Finset.range k) (j : Fin m) : T.shift j ≤ (k / T.f : ℕ) := by
  have hi : T.index j < k := Finset.mem_range.mp (hS (T.index_mem j))
  dsimp [shift]
  exact_mod_cast Nat.div_le_div_right (show T.index j - T.base ≤ k by omega)

theorem quotient_natAbs_le {i : ℕ} (hdiv : (T.f : ℤ) ∣ D.a i)
    (hbound : (D.a i).natAbs ≤ k) : (T.quotient i).natAbs ≤ k / T.f := by
  have hfactor := congrArg Int.natAbs (T.quotient_factor hdiv)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hfactor
  apply (Nat.le_div_iff_mul_le T.f_pos).mpr
  nlinarith

theorem coefficient_natAbs_le (hbound : ∀ j, (D.a (T.index j)).natAbs ≤ k) :
    T.coefficient.natAbs ≤ (k / T.f) ^ m := by
  unfold coefficient
  rw [Int.natAbs_prod]
  calc
    _ ≤ ∏ _j : Fin m, k / T.f := by
      apply Finset.prod_le_prod
      intro j hj
      exact T.quotient_natAbs_le (T.index_dvd j) (hbound j)
    _ = _ := by simp

theorem point_onCurve (hprimitive : Nat.Coprime n.natAbs d) (hd : 0 < d) (hm : ell ∣ m) :
    OnCurve ell T.coefficient T.shift T.point := by
  apply onCurve_of_integer_relations hm hd
  intro j
  exact D.divided_relation T.base_mem (T.index_mem j)
    (by exact_mod_cast T.f_pos.ne' : (T.f : ℤ) ≠ 0)
    (T.quotient_factor T.base_dvd) (T.quotient_factor (T.index_dvd j))
    (T.shift_factor hprimitive j)

end ProgressionTuple

end PerfectPowers
