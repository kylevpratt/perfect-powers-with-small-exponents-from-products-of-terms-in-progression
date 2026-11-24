module

public import PerfectPowers.Curves.DegreeBounds
public import PerfectPowers.External.Remond
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Applying the permitted Remond input to the constructed equations

Finiteness is a modular explicit hypothesis here. `Curves.AffineFiniteness`
supplies it from the permitted affine Faltings and genus inputs, using the
internally proved irreducibility and nonsingularity of our equations.
-/

public section

namespace PerfectPowers

/-- Internal finiteness premise for a positive-shift superelliptic family.
`Curves.AffineFiniteness` proves it from the two agreed geometric inputs. -/
@[expose] def CurveFamilyFinite (ell m : ℕ) : Prop :=
  ∀ (B : ℤ) (C : Fin m → ℤ), B ≠ 0 → Function.Injective C →
    (∀ j, 0 < C j) → (External.RationalZeros (curvePolynomial ell B C)).Finite

theorem remondBound_mono_degree {D E M : ℕ} (hDE : D ≤ E) (hM : 3 ≤ M) :
    External.remondBound D M ≤ External.remondBound E M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 1 < Real.log (M : ℝ) := by
    have hthree : Real.log 3 ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hM)
    linarith [Real.log_three_gt_d9]
  have hloglog : 0 < Real.log (Real.log (M : ℝ)) := Real.log_pos hlogM
  unfold External.remondBound
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ hloglog.le
  apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ Real.log (M : ℝ))
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) (Nat.pow_le_pow_left hDE 4)

theorem curve_rational_points_bound_of_finite
    (hRemond : External.RemondStatement) {ell m L : ℕ} (hell : 0 < ell)
    {B : ℤ} {C : Fin m → ℤ} (hB : B.natAbs ≤ (L + 1) ^ m)
    (hC0 : ∀ j, 0 ≤ C j) (hC : ∀ j, C j ≤ (L : ℤ))
    (hfinite : (External.RationalZeros (curvePolynomial ell B C)).Finite)
    (points : Finset (ℚ × ℚ)) (hpoints : ∀ P ∈ points, OnCurve ell B C P) :
    (points.card : ℝ) ≤ External.remondBound (max ell m) (3 * (L + 1) ^ m) := by
  have hH : 0 < (L + 1) ^ m := pow_pos (by omega) _
  have hM : 3 ≤ 3 * (L + 1) ^ m := by omega
  have hcoeff : External.CoefficientsBounded (curvePolynomial ell B C) (3 * (L + 1) ^ m) := by
    intro s
    exact (curvePolynomial_coefficientsBounded hell hB hC0 hC s).trans (by omega)
  have hbound := hRemond (curvePolynomial ell B C) _ hM hcoeff hfinite points
    (fun P hP => (onCurve_iff_eval_eq_zero ell B C P).mp (hpoints P hP))
  exact hbound.trans (remondBound_mono_degree (curvePolynomial_totalDegree_le ell B C) hM)

end PerfectPowers
