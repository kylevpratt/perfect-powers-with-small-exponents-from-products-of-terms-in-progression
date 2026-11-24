module

public import PerfectPowers.Combinatorics.BoundedMultiplicity
public import PerfectPowers.Analytic.FactorialBounds
import Mathlib.Tactic

/-! # Logarithmic product bounds from bounded multiplicity -/

public section

namespace PerfectPowers

theorem log_prod_lower_of_multiplicity {ι : Type*} (S : Finset ι) (b : ι → ℕ)
    {m : ℕ} (hm : 0 < m) (hpos : ∀ i ∈ S, 0 < b i)
    (hcap : ∀ a : ℕ, (S.filter (fun i => b i = a)).card ≤ m) :
    (S.card : ℝ) * Real.log ((S.card : ℝ) / m) - S.card ≤
      Real.log ((∏ i ∈ S, b i : ℕ) : ℝ) := by
  have hprod : 0 < ∏ i ∈ S, b i := Finset.prod_pos hpos
  have hfac := factorial_le_pow_mul_prod_of_multiplicity S b m hpos hcap
  have hfacR : (S.card.factorial : ℝ) ≤ (m : ℝ) ^ S.card * (∏ i ∈ S, b i : ℕ) := by
    exact_mod_cast hfac
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < S.card.factorial) hfacR
  rw [Real.log_mul (by positivity) (by exact_mod_cast hprod.ne'), Real.log_pow] at hlog
  have hlow := log_factorial_lower S.card
  by_cases hS : S.card = 0
  · simp only [hS, Nat.cast_zero, zero_div, Real.log_zero, mul_zero, zero_sub, neg_zero]
    exact Real.log_nonneg (show (1 : ℝ) ≤ ((∏ i ∈ S, b i : ℕ) : ℝ) by
      exact_mod_cast (show 1 ≤ ∏ i ∈ S, b i from hprod))
  · rw [Real.log_div (by exact_mod_cast hS) (by exact_mod_cast hm.ne')]
    nlinarith

/-- A tangent-line inequality replaces all rounding and monotonicity arguments. -/
theorem entropy_tangent_lower {J N m : ℝ} (hJ : 0 < J) (hN : 0 < N) (hm : 0 < m)
    (hNJ : N ≤ J) (hmN : m ≤ N) :
    N * Real.log (N / m) - N ≤ J * Real.log (J / m) - J := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hN hJ)
  rw [Real.log_div hN.ne' hJ.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hJ.le
  have hid : J * (N / J - 1) = N - J := by field_simp
  rw [hid] at hmul
  have hlogNm : 0 ≤ Real.log (N / m) := Real.log_nonneg ((one_le_div hm).mpr hmN)
  have hnonneg := mul_nonneg (sub_nonneg.mpr hNJ) hlogNm
  rw [Real.log_div hN.ne' hm.ne'] at hnonneg
  rw [Real.log_div hN.ne' hm.ne', Real.log_div hJ.ne' hm.ne']
  nlinarith

theorem log_prod_lower_of_real_mass {ι : Type*} (S : Finset ι) (b : ι → ℕ)
    {m : ℕ} (hm : 0 < m) (hpos : ∀ i ∈ S, 0 < b i)
    (hcap : ∀ a : ℕ, (S.filter (fun i => b i = a)).card ≤ m)
    {N : ℝ} (hmN : (m : ℝ) ≤ N) (hN : N ≤ S.card) :
    N * Real.log (N / m) - N ≤ Real.log ((∏ i ∈ S, b i : ℕ) : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNpos : 0 < N := lt_of_lt_of_le hmR hmN
  exact (entropy_tangent_lower (lt_of_lt_of_le hNpos hN) hNpos hmR hN hmN).trans
    (log_prod_lower_of_multiplicity S b hm hpos hcap)

end PerfectPowers
