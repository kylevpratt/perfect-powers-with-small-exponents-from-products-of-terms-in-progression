module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic

/-! # Affine superelliptic equations and their rational points -/

@[expose] public section

namespace PerfectPowers

def OnCurve (ell : ℕ) {m : ℕ} (B : ℤ) (C : Fin m → ℤ) (P : ℚ × ℚ) : Prop :=
  (B : ℚ) * P.2 ^ ell = ∏ j : Fin m, (P.1 + (C j : ℚ))

noncomputable def curvePolynomial (ell : ℕ) {m : ℕ} (B : ℤ) (C : Fin m → ℤ) :
    MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.C B * MvPolynomial.X 1 ^ ell -
    ∏ j : Fin m, (MvPolynomial.X 0 + MvPolynomial.C (C j))

def evalPair (P : ℚ × ℚ) : MvPolynomial (Fin 2) ℤ →+* ℚ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun i => if i = 0 then P.1 else P.2)

theorem evalPair_curvePolynomial (ell : ℕ) {m : ℕ} (B : ℤ) (C : Fin m → ℤ) (P : ℚ × ℚ) :
    evalPair P (curvePolynomial ell B C) =
      (B : ℚ) * P.2 ^ ell - ∏ j : Fin m, (P.1 + (C j : ℚ)) := by
  unfold curvePolynomial
  rw [map_sub, map_mul, map_pow, map_prod]
  have hC (z : ℤ) : evalPair P (MvPolynomial.C z) = (z : ℚ) := by
    exact MvPolynomial.eval₂_C _ _ z
  have hX0 : evalPair P (MvPolynomial.X 0) = P.1 := by simp [evalPair]
  have hX1 : evalPair P (MvPolynomial.X 1) = P.2 := by simp [evalPair]
  simp only [hC, hX0, hX1, map_add]

theorem onCurve_iff_eval_eq_zero (ell : ℕ) {m : ℕ} (B : ℤ) (C : Fin m → ℤ) (P : ℚ × ℚ) :
    OnCurve ell B C P ↔ evalPair P (curvePolynomial ell B C) = 0 := by
  rw [evalPair_curvePolynomial, sub_eq_zero]
  rfl

end PerfectPowers
