module

public import PerfectPowers.Analytic.ElementaryEulerProduct
public import PerfectPowers.Combinatorics.MinimalDivisors
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic

/-!
# Finite inclusion--exclusion for rough integers

The error term counts subsets of the finite prime set. No asymptotic sieve
theorem is invoked.
-/

@[expose] public section

namespace PerfectPowers

noncomputable def siftedIntegers (k : ℕ) (P : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 k).filter (fun n => ∀ p ∈ P, ¬p ∣ n)

theorem primeProduct_dvd_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∏ p ∈ P, p) ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  classical
  constructor
  · intro hd p hp
    exact (Finset.dvd_prod_of_mem (fun q => q) hp).trans hd
  · intro hd
    induction P using Finset.induction_on with
    | empty => simp
    | @insert p P hp ih =>
      rw [Finset.prod_insert hp]
      have hprime : p.Prime := hP p (Finset.mem_insert_self _ _)
      have hcop : Nat.Coprime p (∏ q ∈ P, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hprime (hP q (Finset.mem_insert_of_mem hq))).mpr
        intro heq
        exact hp (heq.symm ▸ hq)
      exact hcop.mul_dvd_of_dvd_of_dvd (hd p (Finset.mem_insert_self _ _))
        (ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
          (fun q hq => hd q (Finset.mem_insert_of_mem hq)))

theorem card_multiples_Icc (k q : ℕ) :
    ((Finset.Icc 1 k).filter (fun n => q ∣ n)).card = k / q := by
  have heq : Finset.Icc 1 k = Finset.Ioc 0 k := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [heq]
  exact Nat.Ioc_filter_dvd_card_eq_div k q

theorem siftedIntegers_card_eq (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ((siftedIntegers k P).card : ℝ) =
      ∑ Q ∈ P.powerset, (-1 : ℝ) ^ Q.card * ((k / (∏ p ∈ Q, p) : ℕ) : ℝ) := by
  classical
  calc
    _ = ∑ n ∈ Finset.Icc 1 k, if ∀ p ∈ P, ¬p ∣ n then (1 : ℝ) else 0 :=
      Finset.natCast_card_filter _ _
    _ = ∑ n ∈ Finset.Icc 1 k, ∏ p ∈ P, (1 - if p ∣ n then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.prod_boole]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hpn : p ∣ n <;> simp [hpn]
    _ = ∑ n ∈ Finset.Icc 1 k,
        ∑ Q ∈ P.powerset, (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, (if p ∣ n then (1 : ℝ) else 0) := by
      simp only [Finset.prod_sub, Finset.prod_const_one, mul_one]
    _ = ∑ Q ∈ P.powerset, (-1 : ℝ) ^ Q.card *
        ∑ n ∈ Finset.Icc 1 k, (if (∏ p ∈ Q, p) ∣ n then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.prod_boole, primeProduct_dvd_iff Q
        (fun p hp => hP p (Finset.mem_powerset.mp hQ hp)) n]
    _ = _ := by simp only [Finset.sum_boole, card_multiples_Icc]

theorem sieve_main_term_eq (k : ℕ) (P : Finset ℕ) :
    (k : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) =
      ∑ Q ∈ P.powerset, (-1 : ℝ) ^ Q.card * ((k : ℝ) / (∏ p ∈ Q, p : ℕ)) := by
  classical
  rw [Finset.prod_sub, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  simp only [Finset.prod_const_one, mul_one, Finset.prod_inv_distrib, Nat.cast_prod,
    div_eq_mul_inv]
  ring

theorem abs_nat_div_sub_real_div_le_one (k : ℕ) {q : ℕ} (hq : 0 < q) :
    |((k / q : ℕ) : ℝ) - (k : ℝ) / (q : ℝ)| ≤ 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo : ((k / q : ℕ) : ℝ) ≤ (k : ℝ) / q := Nat.cast_div_le
  have hrem : ((k % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt k hq
  have hid : ((k % q : ℕ) : ℝ) + (q : ℝ) * (k / q : ℕ) = k := by
    exact_mod_cast Nat.mod_add_div k q
  have hhi : (k : ℝ) / q < (k / q : ℕ) + 1 := by
    apply (div_lt_iff₀ hqR).mpr
    nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith

theorem abs_siftedIntegers_card_sub_main_le (k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    |((siftedIntegers k P).card : ℝ) -
      (k : ℝ) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹))| ≤ (2 : ℝ) ^ P.card := by
  classical
  rw [siftedIntegers_card_eq k P hP, sieve_main_term_eq, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ Q ∈ P.powerset, |(-1 : ℝ) ^ Q.card * ((k / (∏ p ∈ Q, p) : ℕ) : ℝ) -
        (-1 : ℝ) ^ Q.card * ((k : ℝ) / (∏ p ∈ Q, p : ℕ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _Q ∈ P.powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro Q hQ
      rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      apply abs_nat_div_sub_real_div_le_one
      apply Finset.prod_pos
      intro p hp
      exact (hP p (Finset.mem_powerset.mp hQ hp)).pos
    _ = (2 : ℝ) ^ P.card := by simp

end PerfectPowers
