module

public import PerfectPowers.Curves.GeometricGenus
public import PerfectPowers.Basic.Parameters
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic

/-! # Elementary geometric hypotheses for the superelliptic family

A simple root supplies an Eisenstein prime, proving irreducibility after
every characteristic-zero field extension. Distinct roots also give the
plane Jacobian criterion. No genus calculation is used here.
-/

@[expose] public section

noncomputable section

namespace PerfectPowers

open Polynomial

theorem irreducible_power_sub_of_separable_root {K : Type*} [Field K]
    {ell : ℕ} (hell : 0 < ell) {f : K[X]} (hsep : f.Separable)
    {a : K} (hroot : f.eval a = 0) :
    Irreducible (X ^ ell - C f : Polynomial (Polynomial K)) := by
  let P : Ideal K[X] := Ideal.span {X - C a}
  have hq : Prime (X - C a : K[X]) := Polynomial.prime_X_sub_C a
  have hP : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hq
  have hdiv : X - C a ∣ f := Polynomial.dvd_iff_isRoot.mpr hroot
  have hmonic := Polynomial.monic_X_pow_sub_C f hell.ne'
  have heisen : (X ^ ell - C f : Polynomial (Polynomial K)).IsEisensteinAt P := by
    apply hmonic.isEisensteinAt_of_mem_of_notMem hP.ne_top
    · intro n hn
      rw [Polynomial.natDegree_X_pow_sub_C] at hn
      have hne : ell ≠ n := by omega
      by_cases hn0 : n = 0
      · subst n
        simpa [P, Polynomial.coeff_sub, Polynomial.coeff_X_pow, hell.ne,
          Ideal.mem_span_singleton] using (dvd_neg.mpr hdiv)
      · simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, hn.ne, hn0]
    · intro hmem
      have hsq : (X - C a) ^ 2 ∣ -f := by
        simpa [P, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
          Polynomial.coeff_sub, Polynomial.coeff_X_pow, hell.ne] using hmem
      have hunit := hsep.squarefree (X - C a) (by simpa only [← pow_two] using dvd_neg.mp hsq)
      exact Polynomial.not_isUnit_X_sub_C a hunit
  apply heisen.irreducible hP hmonic.isPrimitive
  simpa only [Polynomial.natDegree_X_pow_sub_C] using hell

theorem irreducible_split_superelliptic {K : Type*} [Field K] {m ell : ℕ}
    (hell : 0 < ell) (hm : 0 < m) {B : K} (hB : B ≠ 0)
    (c : Fin m → K) (hc : Function.Injective c) :
    Irreducible (MvPolynomial.C B * MvPolynomial.X 1 ^ ell -
      ∏ j : Fin m, (MvPolynomial.X 0 - MvPolynomial.C (c j)) : MvPolynomial (Fin 2) K) := by
  let f : K[X] := Polynomial.C B⁻¹ * ∏ j : Fin m, (X - C (c j))
  have hsep : f.Separable :=
    Polynomial.Separable.unit_mul (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hB)))
      (Polynomial.separable_prod_X_sub_C_iff.mpr hc)
  let j : Fin m := ⟨0, hm⟩
  have hroot : f.eval (c j) = 0 := by
    dsimp [f]
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    have hz : (∏ i : Fin m, (X - C (c i) : K[X]).eval (c j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
    rw [hz, mul_zero]
  have hirr := irreducible_power_sub_of_separable_root hell hsep hroot
  have hunit : IsUnit (C (C B) : Polynomial (Polynomial K)) :=
    Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hB))
  have hscaled : Irreducible (C (C B) * (X ^ ell - C f)) :=
    (associated_unit_mul_right _ _ hunit).irreducible_iff.mp hirr
  have hpoly : C (C B) * (X ^ ell - C f) =
      C (C B) * X ^ ell - C (∏ j : Fin m, (X - C (c j))) := by
    rw [mul_sub, ← Polynomial.C_mul]
    congr 2
    dsimp [f]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hB, Polynomial.C_1, one_mul]
  rw [hpoly] at hscaled
  have hmap := (MulEquiv.irreducible_iff (Polynomial.Bivariate.equivMvPolynomial K)).mpr hscaled
  have hcp : Polynomial.C (∏ j : Fin m, (X - C (c j))) =
      ∏ j : Fin m, Polynomial.C (X - C (c j)) := map_prod Polynomial.C _ _
  rw [hcp] at hmap
  simpa only [map_sub, map_mul, map_pow, map_prod, Polynomial.C_sub,
    Polynomial.Bivariate.equivMvPolynomial_C_C, Polynomial.Bivariate.equivMvPolynomial_C_X,
    Polynomial.Bivariate.equivMvPolynomial_X] using hmap

theorem curvePolynomial_irreducible_over {K : Type*} [Field K] [CharZero K]
    {ell m : ℕ} (hell : 0 < ell) (hm : 0 < m) {B : ℤ} (hB : B ≠ 0)
    {C : Fin m → ℤ} (hC : Function.Injective C) :
    Irreducible ((curvePolynomial ell B C).map (Int.castRingHom K)) := by
  have hBK : (B : K) ≠ 0 := by exact_mod_cast hB
  have hc : Function.Injective (fun j => -(C j : K)) := by
    intro i j hij
    apply hC
    exact_mod_cast neg_injective hij
  have h := irreducible_split_superelliptic hell hm hBK (fun j => -(C j : K)) hc
  simpa [curvePolynomial, map_sub, map_mul, map_pow, map_prod] using h

theorem nonsingular_power_equation {K : Type*} [Field K] [CharZero K]
    {ell : ℕ} (hell : 0 < ell) {B : K} (hB : B ≠ 0) {f : K[X]}
    (hf : f.Separable) (P : Fin 2 → K)
    (hP : MvPolynomial.eval P (MvPolynomial.C B * MvPolynomial.X 1 ^ ell -
      Polynomial.aeval (MvPolynomial.X 0) f) = 0) :
    ∃ i : Fin 2, MvPolynomial.eval P (MvPolynomial.pderiv i
      (MvPolynomial.C B * MvPolynomial.X 1 ^ ell - Polynomial.aeval (MvPolynomial.X 0) f)) ≠ 0 := by
  have hev (g : K[X]) : MvPolynomial.eval P (Polynomial.aeval (MvPolynomial.X 0) g) =
      g.eval (P 0) := by
    induction g using Polynomial.induction_on' with
    | add g h hg hh => simp only [map_add, Polynomial.eval_add, hg, hh]
    | monomial n a => simp [Polynomial.aeval_def, Polynomial.eval₂_monomial, Polynomial.eval_monomial]
  have hd0 : MvPolynomial.pderiv (0 : Fin 2)
      (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) f) =
      Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) f.derivative := by
    rw [(MvPolynomial.pderiv (0 : Fin 2)).map_aeval]
    simp
  have hd1 : MvPolynomial.pderiv (1 : Fin 2)
      (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) f) = 0 := by
    rw [(MvPolynomial.pderiv (1 : Fin 2)).map_aeval]
    simp [MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  by_cases hy : P 1 = 0
  · refine ⟨0, ?_⟩
    have hroot : f.eval (P 0) = 0 := by
      simpa [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
        hy, zero_pow hell.ne', hev] using hP
    have hder := hf.eval₂_derivative_ne_zero (RingHom.id K) hroot
    simpa [map_sub, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, hd0, hev,
      MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0)] using hder
  · refine ⟨1, ?_⟩
    have hellK : (ell : K) ≠ 0 := by exact_mod_cast hell.ne'
    simpa [map_sub, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, hd1, and_assoc]
      using mul_ne_zero (mul_ne_zero hB hellK) (pow_ne_zero (ell - 1) hy)

theorem curvePolynomial_nonsingular {ell m : ℕ} (hell : 0 < ell)
    {B : ℤ} (hB : B ≠ 0) {C : Fin m → ℤ} (hC : Function.Injective C)
    (P : Fin 2 → AlgebraicClosure ℚ)
    (hP : MvPolynomial.eval₂ (Int.castRingHom _) P (curvePolynomial ell B C) = 0) :
    ∃ i : Fin 2, MvPolynomial.eval₂ (Int.castRingHom _) P
      (MvPolynomial.pderiv i (curvePolynomial ell B C)) ≠ 0 := by
  let K := AlgebraicClosure ℚ
  let f : K[X] := ∏ j : Fin m, (X - Polynomial.C (-(C j : K)))
  have hinj : Function.Injective (fun j => -(C j : K)) := by
    intro i j hij
    apply hC
    exact_mod_cast neg_injective hij
  have hsep : f.Separable := Polynomial.separable_prod_X_sub_C_iff.mpr hinj
  have heq : (curvePolynomial ell B C).map (Int.castRingHom K) =
      MvPolynomial.C (B : K) * MvPolynomial.X 1 ^ ell -
        Polynomial.aeval (MvPolynomial.X 0) f := by
    simp [curvePolynomial, f, map_prod]
  have hP' : MvPolynomial.eval P (MvPolynomial.C (B : K) * MvPolynomial.X 1 ^ ell -
      Polynomial.aeval (MvPolynomial.X 0) f) = 0 := by
    rw [← heq]
    simpa only [MvPolynomial.eval_map, RingHom.id_comp] using hP
  obtain ⟨i, hi⟩ := nonsingular_power_equation hell (by exact_mod_cast hB) hsep P hP'
  refine ⟨i, ?_⟩
  rw [← heq, MvPolynomial.pderiv_map, MvPolynomial.eval_map] at hi
  simpa only [RingHom.id_comp] using hi

/-- The actual affine equation equipped with its proved irreducibility
hypotheses, ready for the two external geometric inputs. -/
def superellipticAffineCurve {ell : ℕ} (hell : 2 ≤ ell) (B : ℤ)
    (C : Fin (branchCount ell) → ℤ) (hB : B ≠ 0) (hC : Function.Injective C) :
    AffinePlaneCurve where
  equation := curvePolynomial ell B C
  irreducible := curvePolynomial_irreducible_over (by omega)
    (by have h := branchCount_properties hell; omega) hB hC
  geometricallyIrreducible := curvePolynomial_irreducible_over (by omega)
    (by have h := branchCount_properties hell; omega) hB hC

theorem superellipticAffineCurve_nonsingular {ell : ℕ} (hell : 2 ≤ ell) (B : ℤ)
    (C : Fin (branchCount ell) → ℤ) (hB : B ≠ 0) (hC : Function.Injective C) :
    (superellipticAffineCurve hell B C hB hC).Nonsingular := by
  intro P hP
  exact curvePolynomial_nonsingular (by omega) hB hC P hP

end PerfectPowers
