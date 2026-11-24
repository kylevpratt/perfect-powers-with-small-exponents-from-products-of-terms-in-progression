module

public import PerfectPowers.Combinatorics.TupleExtraction
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Minimal divisors above a threshold

This is the divisor construction in Lemma 4.4, shared by the proposed
elementary replacement. No sieve estimate is used in this file.
-/

@[expose] public section

namespace PerfectPowers

noncomputable def minimalLargeDivisors (k : ℕ) (t : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 k).filter (fun f => t < (f : ℝ) ∧
    ∀ g : ℕ, g ∣ f → g < f → (g : ℝ) ≤ t)

noncomputable def roughIntegers (k : ℕ) (A : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 k).filter (fun n => ∀ p : ℕ, p.Prime → (p : ℝ) ≤ A → ¬p ∣ n)

theorem exists_minimal_large_divisor {k n : ℕ} {t : ℝ}
    (hn : 0 < n) (hnk : n ≤ k) (htn : t < (n : ℝ)) :
    ∃ f ∈ minimalLargeDivisors k t, f ∣ n := by
  classical
  have hex : ∃ f : ℕ, f ∣ n ∧ t < (f : ℝ) := ⟨n, dvd_refl n, htn⟩
  let f := Nat.find hex
  have hf : f ∣ n ∧ t < (f : ℝ) := Nat.find_spec hex
  refine ⟨f, Finset.mem_filter.mpr ⟨?_, hf.2, ?_⟩, hf.1⟩
  · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hf.1 hn, (Nat.le_of_dvd hn hf.1).trans hnk⟩
  · intro g hgf hgf_lt
    by_contra hgt
    have hg : f ≤ g := Nat.find_min' hex ⟨hgf.trans hf.1, lt_of_not_ge hgt⟩
    omega

theorem minimalLargeDivisor_is_rough {k f : ℕ} {t A : ℝ}
    (ht : 0 ≤ t) (hf : f ∈ minimalLargeDivisors k t) (hlarge : A * t < (f : ℝ)) :
    f ∈ roughIntegers k A := by
  classical
  obtain ⟨hfk, hft, hminimal⟩ := Finset.mem_filter.mp hf
  refine Finset.mem_filter.mpr ⟨hfk, ?_⟩
  intro p hp hpA hpf
  have hfpos : 0 < f := (Finset.mem_Icc.mp hfk).1
  have hquot : (f / p : ℕ) ∣ f := Nat.div_dvd_of_dvd hpf
  have hquotlt : f / p < f := Nat.div_lt_self hfpos hp.one_lt
  have hqt := hminimal (f / p) hquot hquotlt
  have hcancel : ((f / p : ℕ) : ℝ) * (p : ℝ) = (f : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hpf
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hmult := mul_le_mul_of_nonneg_right hqt hp0
  have hAt := mul_le_mul_of_nonneg_right hpA ht
  nlinarith

theorem minimalLargeDivisors_subset_small_union_rough {k : ℕ} {t A : ℝ} (ht : 0 ≤ t) :
    minimalLargeDivisors k t ⊆
      ((Finset.Icc 1 k).filter (fun f => (f : ℝ) ≤ A * t)) ∪ roughIntegers k A := by
  classical
  intro f hf
  by_cases hsmall : (f : ℝ) ≤ A * t
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, hsmall⟩)
  · exact Finset.mem_union_right _ (minimalLargeDivisor_is_rough ht hf (lt_of_not_ge hsmall))

theorem card_positive_nat_below_real_le {B : Finset ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ (b : ℝ) ≤ t) : (B.card : ℝ) ≤ t := by
  classical
  have hsub : B ⊆ Finset.Icc 1 ⌊t⌋₊ := by
    intro b hb
    exact Finset.mem_Icc.mpr ⟨(hB b hb).1, (Nat.le_floor_iff ht).mpr (hB b hb).2⟩
  have hcard : B.card ≤ ⌊t⌋₊ := by
    simpa using Finset.card_le_card hsub
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le ht)

theorem card_minimalLargeDivisors_le {k : ℕ} {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) :
    ((minimalLargeDivisors k t).card : ℝ) ≤ A * t + (roughIntegers k A).card := by
  classical
  have hsmall : (((Finset.Icc 1 k).filter (fun f : ℕ => (f : ℝ) ≤ A * t)).card : ℝ) ≤ A * t := by
    apply card_positive_nat_below_real_le (mul_nonneg hA ht)
    intro b hb
    obtain ⟨hbk, hbsmall⟩ := Finset.mem_filter.mp hb
    exact ⟨(Finset.mem_Icc.mp hbk).1, hbsmall⟩
  have hcard := (Finset.card_le_card (minimalLargeDivisors_subset_small_union_rough
    (k := k) (A := A) ht)).trans
    (Finset.card_union_le _ _)
  have hcast : ((minimalLargeDivisors k t).card : ℝ) ≤
      (((Finset.Icc 1 k).filter (fun f : ℕ => (f : ℝ) ≤ A * t)).card : ℝ) +
        (roughIntegers k A).card := by exact_mod_cast hcard
  linarith

end PerfectPowers
