module

public import PerfectPowers.Analytic.RoughCounting
public import PerfectPowers.Combinatorics.CommonDivisorTuples
import Mathlib.Tactic

/-!
# The elementary replacement for Lemma 4.4

This has the revised exponential constant `5` and the stronger size condition
`12u * 2^(exp(4u)) ≤ k`, where `u = m/c`. It does not assert the full original
Lemma 4.4. The extraction argument actually gives a denominator `3(m+1)`,
which also implies the denominator `6(m+1)` used in the paper.

Proof difference from the paper: finite inclusion-exclusion and a harmonic
Euler-product estimate replace the fundamental sieve lemma and the cited
Rosser--Schoenfeld bound. The draft uses `2.77` in place of `5` and a weaker
size condition; `Analytic.TupleThreshold` verifies the stronger condition
uniformly for every application here. See `PerfectPowers.PaperComparison`.
-/

public section

namespace PerfectPowers

theorem tuple_parameter_error_bound {m : ℕ} {c u : ℝ} (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hm : (m : ℝ) ≤ u) :
    (c / 3 * Real.exp (-5 * u)) * ((m : ℝ) * Real.exp (4 * u) + 1) ≤ c / 3 := by
  have hmono : Real.exp (-5 * u) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have hexp : Real.exp (-5 * u) * Real.exp (4 * u) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmall : Real.exp (-u) * ((m : ℝ) + 1) ≤ 1 := by
    have hbound : (m : ℝ) + 1 ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-u)).le
    simpa only [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero u)] using hmul
  calc
    _ = c / 3 * ((m : ℝ) * Real.exp (-u) + Real.exp (-5 * u)) := by
      calc
        _ = c / 3 * ((m : ℝ) *
            (Real.exp (-5 * u) * Real.exp (4 * u)) + Real.exp (-5 * u)) := by ring
        _ = _ := by rw [hexp]
    _ ≤ c / 3 * ((m : ℝ) * Real.exp (-u) + Real.exp (-u)) := by gcongr
    _ = c / 3 * (Real.exp (-u) * ((m : ℝ) + 1)) := by ring
    _ ≤ c / 3 * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = c / 3 := mul_one _

theorem tuple_rough_error_bound {k m : ℕ} {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hm : (m : ℝ) = c * u)
    (hsize : 12 * u * (2 : ℝ) ^ (Real.exp (4 * u)) ≤ (k : ℝ)) :
    (m : ℝ) * (roughIntegers k (Real.exp (4 * u))).card ≤ c * (k : ℝ) / 3 := by
  have hA : 1 < Real.exp (4 * u) := Real.one_lt_exp_iff.mpr (by positivity)
  have hrough := mul_le_mul_of_nonneg_left
    (roughIntegers_card_le_log (k := k) hA) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  rw [Real.log_exp] at hrough
  have hquarter : (m : ℝ) * ((k : ℝ) / (4 * u)) = c * (k : ℝ) / 4 := by
    rw [hm]
    field_simp
  have htwelfth : (m : ℝ) * (2 : ℝ) ^ (Real.exp (4 * u)) ≤ c * (k : ℝ) / 12 := by
    rw [hm]
    nlinarith [mul_le_mul_of_nonneg_left hsize hc.le]
  nlinarith

theorem exists_elementary_common_divisor_tuples {k m : ℕ} {c : ℝ}
    (hm : 1 ≤ m) (hc : 0 < c) (hc1 : c ≤ 1)
    (hsize : 12 * ((m : ℝ) / c) * (2 : ℝ) ^ (Real.exp (4 * ((m : ℝ) / c))) ≤ (k : ℝ))
    (B : Finset ℕ) (hB : B ⊆ Finset.Icc 1 k) (hdense : c * (k : ℝ) ≤ B.card) :
    ∃ family : Finset (Finset ℕ),
      (∀ U ∈ family, U ⊆ B ∧ U.card = m + 1 ∧
        ∃ f : ℕ, c / 3 * Real.exp (-5 * ((m : ℝ) / c)) * (k : ℝ) < (f : ℝ) ∧
          ∀ b ∈ U, f ∣ b) ∧
      (∀ U ∈ family, ∀ V ∈ family, U ≠ V → Disjoint U V) ∧
      c * (k : ℝ) / (6 * ((m : ℝ) + 1)) ≤ family.card := by
  let u : ℝ := (m : ℝ) / c
  let η : ℝ := c / 3 * Real.exp (-5 * u)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hu : 0 < u := div_pos hmpos hc
  have hmrel : (m : ℝ) = c * u := by dsimp [u]; field_simp
  have hmle : (m : ℝ) ≤ u := by
    dsimp [u]
    apply (le_div_iff₀ hc).mpr
    nlinarith
  have hη : 0 ≤ η := by dsimp [η]; positivity
  obtain ⟨family, hprop, hdis, hcard⟩ := exists_common_divisor_tuples_with_rough_error
    B m hB (mul_nonneg hη (Nat.cast_nonneg k)) (Real.exp_pos (4 * u)).le
  refine ⟨family, hprop, hdis, ?_⟩
  have hparam := mul_le_mul_of_nonneg_right (tuple_parameter_error_bound hc.le hu.le hmle)
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hrough := tuple_rough_error_bound hc hu hmrel hsize
  have hmass : c * (k : ℝ) / 3 ≤ ((m : ℝ) + 1) * family.card := by
    simp only [Nat.cast_add, Nat.cast_one] at hcard
    dsimp [η] at hcard
    nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * ((m : ℝ) + 1))).mpr
  have hnonneg : 0 ≤ ((m : ℝ) + 1) * family.card :=
    mul_nonneg (add_nonneg (Nat.cast_nonneg m) zero_le_one) (Nat.cast_nonneg _)
  nlinarith

end PerfectPowers
