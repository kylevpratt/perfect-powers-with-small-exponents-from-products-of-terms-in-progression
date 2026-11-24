module

public import PerfectPowers.Curves.Equation
public import PerfectPowers.External.Remond
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-!
# Coefficient heights of the constructed curves

The shifts used in the arithmetic construction are positive. This gives an
elementary coefficient bound by evaluating the polynomial with natural
coefficients at `(1,1)`. The `Y^ell` monomial has disjoint support from the
polynomial in `X`, so the height bound does not lose an extra factor of two.
-/

public section

namespace PerfectPowers

theorem coeff_nat_le_eval_one {σ : Type*} (P : MvPolynomial σ ℕ) (s : σ →₀ ℕ) :
    P.coeff s ≤ MvPolynomial.eval (fun _ => 1) P := by
  classical
  rw [MvPolynomial.eval_eq]
  simp only [one_pow, Finset.prod_const_one, mul_one]
  by_cases hs : s ∈ P.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs
  · simp [MvPolynomial.notMem_support_iff.mp hs]

theorem coeff_prod_linear_nat_bound {m L : ℕ} (C : Fin m → ℕ)
    (hC : ∀ j, C j ≤ L) (s : Fin 2 →₀ ℕ) :
    ((∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j))) :
      MvPolynomial (Fin 2) ℕ).coeff s ≤ (L + 1) ^ m := by
  calc
    _ ≤ MvPolynomial.eval (fun _ => 1)
        (∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j))) :=
      coeff_nat_le_eval_one _ s
    _ = ∏ j : Fin m, (1 + C j) := by simp
    _ ≤ ∏ _j : Fin m, (L + 1) := by
      apply Finset.prod_le_prod
      intro j hj
      have := hC j
      omega
    _ = (L + 1) ^ m := by simp

theorem degreeOf_Y_prod_linear_eq_zero {m : ℕ} (C : Fin m → ℤ) :
    (∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j)) :
      MvPolynomial (Fin 2) ℤ).degreeOf 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc
    _ ≤ ∑ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j) :
        MvPolynomial (Fin 2) ℤ).degreeOf 1 := MvPolynomial.degreeOf_prod_le _ _ _
    _ ≤ ∑ _j : Fin m, 0 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [MvPolynomial.degreeOf_X, ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
        MvPolynomial.degreeOf_C, max_self] using
        MvPolynomial.degreeOf_add_le (1 : Fin 2)
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) (MvPolynomial.C (C j))
    _ = 0 := by simp

theorem coeff_prod_linear_int_bound {m L : ℕ} (C : Fin m → ℤ)
    (hC0 : ∀ j, 0 ≤ C j) (hC : ∀ j, C j ≤ (L : ℤ)) (s : Fin 2 →₀ ℕ) :
    ((∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j)) :
      MvPolynomial (Fin 2) ℤ).coeff s).natAbs ≤ (L + 1) ^ m := by
  have hmap : MvPolynomial.map (Nat.castRingHom ℤ)
      (∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j).natAbs) :
        MvPolynomial (Fin 2) ℕ) =
      ∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j)) := by
    simp only [map_prod, map_add, MvPolynomial.map_X, MvPolynomial.map_C]
    apply Finset.prod_congr rfl
    intro j hj
    have heq : (Nat.castRingHom ℤ) (C j).natAbs = C j := by
      change ((C j).natAbs : ℤ) = C j
      rw [Int.natCast_natAbs, abs_of_nonneg (hC0 j)]
    rw [heq]
  rw [← hmap, MvPolynomial.coeff_map]
  change _ ≤ (L + 1) ^ m
  rw [show ∀ a : ℕ, ((Nat.castRingHom ℤ) a).natAbs = a from fun a => Int.natAbs_natCast a]
  apply coeff_prod_linear_nat_bound
  intro j
  exact_mod_cast (show (C j).natAbs ≤ (L : ℤ) by
    simpa only [Int.natCast_natAbs, abs_of_nonneg (hC0 j)] using hC j)

theorem curvePolynomial_coefficientsBounded {ell m L : ℕ} (hell : 0 < ell)
    {B : ℤ} {C : Fin m → ℤ} (hB : B.natAbs ≤ (L + 1) ^ m)
    (hC0 : ∀ j, 0 ≤ C j) (hC : ∀ j, C j ≤ (L : ℤ)) :
    External.CoefficientsBounded (curvePolynomial ell B C) ((L + 1) ^ m) := by
  classical
  intro s
  rw [curvePolynomial, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X_pow]
  by_cases hs : Finsupp.single (1 : Fin 2) ell = s
  · rw [ite_eq_left hs, mul_one]
    have hsz : s 1 = ell := by rw [← hs]; simp
    have hzero :
        (∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j)) :
          MvPolynomial (Fin 2) ℤ).coeff s = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      apply MvPolynomial.notMem_support_of_degreeOf_lt 1
      rw [degreeOf_Y_prod_linear_eq_zero, hsz]
      exact hell
    rw [hzero, sub_zero]
    exact hB
  · rw [ite_eq_right hs, mul_zero, zero_sub, Int.natAbs_neg]
    exact coeff_prod_linear_int_bound C hC0 hC s

end PerfectPowers
