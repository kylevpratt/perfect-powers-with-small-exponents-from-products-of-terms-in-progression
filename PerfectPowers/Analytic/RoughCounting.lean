module

public import PerfectPowers.Analytic.FiniteSieve
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # The elementary rough-number estimate used in place of the analytic sieve -/

public section

namespace PerfectPowers

theorem roughIntegers_eq_sifted {k : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    roughIntegers k A = siftedIntegers k (Nat.primesLE ⌊A⌋₊) := by
  classical
  ext n
  simp only [roughIntegers, siftedIntegers, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hrough⟩
    refine ⟨hn, ?_⟩
    intro p hp
    obtain ⟨hpA, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact hrough p hpprime ((Nat.le_floor_iff hA).mp hpA)
  · rintro ⟨hn, hsift⟩
    refine ⟨hn, ?_⟩
    intro p hp hpA
    exact hsift p (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hA).mpr hpA, hp⟩)

theorem roughIntegers_card_le_eulerDensity {k : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    ((roughIntegers k A).card : ℝ) ≤
      (k : ℝ) * eulerDensity A + (2 : ℝ) ^ ((Nat.primesLE ⌊A⌋₊).card) := by
  rw [roughIntegers_eq_sifted hA]
  have h := abs_siftedIntegers_card_sub_main_le k (Nat.primesLE ⌊A⌋₊)
    (fun p hp => Nat.prime_of_mem_primesLE hp)
  have := (abs_le.mp h).2
  change _ ≤ (k : ℝ) * (∏ p ∈ Nat.primesLE ⌊A⌋₊, (1 - (p : ℝ)⁻¹)) + _
  linarith

theorem roughIntegers_card_le_log {k : ℕ} {A : ℝ} (hA : 1 < A) :
    ((roughIntegers k A).card : ℝ) ≤ (k : ℝ) / Real.log A + (2 : ℝ) ^ A := by
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA.le
  have hPcard : ((Nat.primesLE ⌊A⌋₊).card : ℝ) ≤ A := by
    apply card_positive_nat_below_real_le hA0
    intro p hp
    obtain ⟨hpN, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact ⟨hpprime.one_le, (Nat.le_floor_iff hA0).mp hpN⟩
  have hpower : (2 : ℝ) ^ ((Nat.primesLE ⌊A⌋₊).card) ≤ (2 : ℝ) ^ A := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hPcard
  have hmain := mul_le_mul_of_nonneg_left (eulerDensity_le_inverse_log hA)
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have h := roughIntegers_card_le_eulerDensity (k := k) hA0
  rw [mul_one_div] at hmain
  linarith

end PerfectPowers
