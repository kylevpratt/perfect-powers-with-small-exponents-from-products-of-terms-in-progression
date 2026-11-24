module

public import PerfectPowers.Arithmetic.Decomposition
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic

/-! # Distinct products and rational coordinates from disjoint tuples -/

public section

namespace PerfectPowers

theorem prod_ne_of_cross_coprime {A B : Finset ℕ} {x : ℕ → ℕ}
    (hcop : ∀ i ∈ A, ∀ j ∈ B, Nat.Coprime (x i) (x j))
    (hlarge : ∃ i ∈ A, 1 < x i) : (∏ i ∈ A, x i) ≠ ∏ j ∈ B, x j := by
  intro heq
  have hprod : Nat.Coprime (∏ i ∈ A, x i) (∏ j ∈ B, x j) :=
    Nat.Coprime.prod_left (fun i hi => Nat.Coprime.prod_right (fun j hj => hcop i hi j hj))
  have hone : (∏ i ∈ A, x i) = 1 := by
    simpa only [Nat.Coprime, ← heq, Nat.gcd_self] using hprod
  obtain ⟨i, hi, hxi⟩ := hlarge
  have hdiv : x i ∣ 1 := hone ▸ Finset.dvd_prod_of_mem x hi
  have := Nat.dvd_one.mp hdiv
  omega

theorem quotient_products_ne_of_cross_coprime {A B : Finset ℕ} {x : ℕ → ℕ}
    (hcop : ∀ i ∈ A, ∀ j ∈ B, Nat.Coprime (x i) (x j))
    (hlarge : ∃ i ∈ A, 1 < x i) {denom : ℚ} (hd : denom ≠ 0) :
    (∏ i ∈ A, (x i : ℚ)) / denom ≠ (∏ j ∈ B, (x j : ℚ)) / denom := by
  intro heq
  have hnum := (div_left_inj₀ hd).mp heq
  apply prod_ne_of_cross_coprime hcop hlarge
  exact_mod_cast hnum

/-- The coordinate distinctness used in both applications of the curve bound.
Only the numerator supports need be disjoint; denominators may share primes. -/
theorem Decomposition.pointY_ne_of_disjoint {k ell d : ℕ} {n : ℤ} {S A B : Finset ℕ}
    (D : Decomposition k ell n d S) (hprimitive : Nat.Coprime n.natAbs d)
    (hell : 0 < ell) (hS : S ⊆ Finset.range k) (hA : A ⊆ S) (hB : B ⊆ S)
    (hdis : Disjoint A B) (hlarge : ∃ i ∈ A, 1 < D.x i)
    {denom : ℚ} (hd : denom ≠ 0) :
    (∏ i ∈ A, (D.x i : ℚ)) / denom ≠ (∏ j ∈ B, (D.x j : ℚ)) / denom := by
  apply quotient_products_ne_of_cross_coprime ?_ hlarge hd
  intro i hi j hj
  apply D.x_pairwise_coprime hprimitive hell hS (hA hi) (hB hj)
  intro hij
  subst j
  exact Finset.disjoint_left.mp hdis hi hj

end PerfectPowers
