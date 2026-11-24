module

public import PerfectPowers.Main.PositiveClassification
public import PerfectPowers.Main.Statements
public import PerfectPowers.Analytic.ExponentRange
import Mathlib.Tactic

/-!
# Full-product classification once the step is one or two

Proof difference from the paper: the eventual prime interval `(x, 5*x/4]`
from mathlib's proved ordinary PNT replaces the particular prime-counting
error estimates used in the draft's proof of Theorem 1.4. The three exact
endpoint ranges are retained. See `PerfectPowers.PaperComparison`.
-/

public section

open Filter

namespace PerfectPowers

theorem full_classification_of_small_step {k p d : ℕ} {n : ℤ}
    (hk : 4 ≤ k) (hp : LeastPrimeAbove k p) (hn : n ≠ 0)
    (hprimitive : Nat.Coprime n.natAbs d) (hd : d = 1 ∨ d = 2)
    (hnbound : n.natAbs ≤ k * (d + 1))
    (hprime : ∀ x : ℝ, (k : ℝ) ≤ x → ∃ q : ℕ, q.Prime ∧ x < (q : ℝ) ∧ (q : ℝ) ≤ (5 / 4 : ℝ) * x)
    (hsmooth : ∀ i : ℕ, i < k → Smooth k (term n d i)) : AdmissiblePair k p n d := by
  rcases hd with rfl | rfl
  · have hN : |n| ≤ 2 * (k : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (show n.natAbs ≤ 2 * k by nlinarith)
    by_cases hnpos : 0 < n
    · exact Or.inl ⟨rfl, by omega, step_one_positive_classification hk hp hnpos
        (abs_le.mp hN).2 hprime hsmooth⟩
    · have hnneg : n < 0 := by omega
      have hend : n + ((k : ℤ) - 1) < 0 := by
        by_contra hnot
        obtain ⟨i, hi, heq⟩ := exists_index_step_one (show n ≤ 0 by omega) (show (0 : ℤ) ≤ n + ((k : ℤ) - 1) by omega)
        exact (hsmooth i hi).1 heq
      let v : ℤ := -n - ((k : ℤ) - 1)
      have hvpos : 0 < v := by dsimp [v]; omega
      have hvbound : v ≤ 2 * (k : ℤ) := by dsimp [v]; have := (abs_le.mp hN).1; omega
      have hvsmooth : ∀ i : ℕ, i < k → Smooth k (term v 1 i) := by
        simpa only [v, Nat.cast_one, mul_one] using smooth_terms_reflect hsmooth
      have hv := step_one_positive_classification hk hp hvpos hvbound hprime hvsmooth
      exact Or.inr (Or.inl ⟨rfl, by dsimp [v] at hv; omega, by omega⟩)
  · have hN : |n| ≤ 3 * (k : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (show n.natAbs ≤ 3 * k by nlinarith)
    have hodd : Odd n := Int.natAbs_odd.mp (Nat.coprime_two_right.mp hprimitive)
    by_cases hnpos : 0 < n
    · exact (step_two_positive_impossible hk hnpos (abs_le.mp hN).2 hodd hprime hsmooth).elim
    · have hnneg : n < 0 := by omega
      have hlast : k - 1 < k := by omega
      have hlastEq : term n 2 (k - 1) = n + 2 * ((k : ℤ) - 1) := by
        rw [term, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        norm_num
        ring
      have hendne : n + 2 * ((k : ℤ) - 1) ≠ 0 := by
        rw [← hlastEq]
        exact (hsmooth (k - 1) hlast).1
      have hend : 0 < n + 2 * ((k : ℤ) - 1) := by
        by_contra hnot
        let v : ℤ := -n - 2 * ((k : ℤ) - 1)
        have hvpos : 0 < v := by dsimp [v]; omega
        have hvbound : v ≤ 3 * (k : ℤ) := by dsimp [v]; have := (abs_le.mp hN).1; omega
        have hvodd : Odd v := by
          apply Int.odd_iff.mpr
          have hnmod := Int.odd_iff.mp hodd
          dsimp [v]
          omega
        have hvsmooth : ∀ i : ℕ, i < k → Smooth k (term v 2 i) := by
          simpa only [v, Nat.cast_ofNat, mul_comm] using smooth_terms_reflect hsmooth
        exact step_two_positive_impossible hk hvpos hvbound hvodd hprime hvsmooth
      have hpodd : Odd (p : ℤ) := Int.odd_natCast p |>.mpr (hp.1.odd_of_ne_two (by have := hp.2.1; omega))
      have hpnegodd : Odd (-(p : ℤ)) := by
        apply Int.odd_iff.mpr
        have hpmod := Int.odd_iff.mp hpodd
        omega
      have hnp : -(p : ℤ) < n := by
        by_contra hnot
        obtain ⟨i, hi, heq⟩ := exists_index_step_two hodd hpnegodd
          (show n ≤ -(p : ℤ) by omega) (show -(p : ℤ) ≤ n + 2 * ((k : ℤ) - 1) by omega)
        have hneg : Smooth k (-(p : ℤ)) := heq ▸ hsmooth i hi
        exact not_smooth_nat_prime hp.1 hp.2.1 ((smooth_neg_iff k (p : ℤ)).mp hneg)
      have hendp : n + 2 * ((k : ℤ) - 1) < (p : ℤ) := by
        by_contra hnot
        obtain ⟨i, hi, heq⟩ := exists_index_step_two hodd hpodd
          (show n ≤ (p : ℤ) by omega) (show (p : ℤ) ≤ n + 2 * ((k : ℤ) - 1) by omega)
        exact not_smooth_nat_prime hp.1 hp.2.1 (heq ▸ hsmooth i hi)
      have hnmod := Int.odd_iff.mp hodd
      have hpmod := Int.odd_iff.mp hpodd
      exact Or.inr (Or.inr ⟨rfl, by omega, by omega, hodd⟩)

theorem eventually_full_classification :
    ∀ᶠ k : ℕ in atTop, ∀ (ell : ℕ) (n : ℤ) (d : ℕ) (b y : ℤ),
      Solution k ell n d b y (Finset.range k) → Smooth k (progressionProduct n d (Finset.range k)) →
      (d = 1 ∨ d = 2) → n.natAbs ≤ k * (d + 1) →
      ∃ p : ℕ, LeastPrimeAbove k p ∧ AdmissiblePair k p n d := by
  filter_upwards [eventually_uniform_quarter_prime_interval, eventually_ge_atTop (4 : ℕ)] with k hprime hk
  intro ell n d b y hsol hsmooth hd hn
  obtain ⟨p, hp⟩ := exists_leastPrimeAbove k
  exact ⟨p, hp, full_classification_of_small_step hk hp hsol.n_ne_zero hsol.coprime hd hn hprime
    (fun i hi => hsmooth.progression_term hi)⟩

theorem eventually_theorem14_of_theorem15 :
    ∀ᶠ k : ℕ in atTop, Theorem15At k → Theorem14At k := by
  filter_upwards [eventually_full_classification] with k hclass
  intro h15 ell n d b y hell hsol
  have hratio : 0 ≤ (k : ℝ) / Real.log (k : ℝ) := div_nonneg (Nat.cast_nonneg k) hell.log_pos.le
  have hdense : Dense k (Finset.range k) := by
    unfold Dense
    rw [Finset.card_range]
    rw [mul_div_assoc]
    nlinarith
  have hver : VeryDense k (Finset.range k) := by
    unfold VeryDense
    rw [Finset.card_range]
    exact sub_le_self _ (div_nonneg (Nat.cast_nonneg k) (pow_nonneg hell.log_pos.le 3))
  obtain ⟨hsmooth, hstepbound, hn, hstep⟩ := h15 ell n d b y (Finset.range k) hell hdense hsol
  exact ⟨hsmooth, hstep hver, hn, hclass ell n d b y hsol hsmooth (hstep hver) hn⟩

end PerfectPowers
