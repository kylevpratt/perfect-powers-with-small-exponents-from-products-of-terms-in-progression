module

public import PerfectPowers.Curves.CoefficientBounds
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

/-! # Total-degree bounds for the affine equations -/

public section

namespace PerfectPowers

theorem totalDegree_prod_linear_le {m : ℕ} (C : Fin m → ℤ) :
    (∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j)) :
      MvPolynomial (Fin 2) ℤ).totalDegree ≤ m := by
  calc
    _ ≤ ∑ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j) :
        MvPolynomial (Fin 2) ℤ).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _j : Fin m, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C, max_eq_left (by omega :
        (0 : ℕ) ≤ 1)] using
        MvPolynomial.totalDegree_add (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ)
          (MvPolynomial.C (C j))
    _ = m := by simp

theorem curvePolynomial_totalDegree_le (ell : ℕ) {m : ℕ} (B : ℤ) (C : Fin m → ℤ) :
    (curvePolynomial ell B C).totalDegree ≤ max ell m := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le_max
  · simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow, zero_add] using
      MvPolynomial.totalDegree_mul (MvPolynomial.C B)
        (MvPolynomial.X 1 ^ ell : MvPolynomial (Fin 2) ℤ)
  · exact totalDegree_prod_linear_le C

end PerfectPowers
