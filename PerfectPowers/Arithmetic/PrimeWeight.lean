module

public import PerfectPowers.Arithmetic.FullProductTools
public import PerfectPowers.External.PrimeAP
import Mathlib.Tactic

/-!
# Prime weights forced into the omitted indices

These finite inequalities connect smooth progression terms with the precise
prime-AP sum in Lemma 3.3. All endpoint and congruence-to-index maps are proved
explicitly. No prime-distribution hypothesis is needed for the upper bounds.
-/

public section

namespace PerfectPowers

theorem exists_index_of_modEq {k d : ℕ} {n z : ℤ} (hd : 0 < d)
    (hmod : Int.ModEq (d : ℤ) z n) (hlo : n ≤ z) (hhi : z < n + (k : ℤ) * (d : ℤ)) :
    ∃ i : ℕ, i < k ∧ term n d i = z := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hmod.symm
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by nlinarith
  let i := t.toNat
  have hcast : (i : ℤ) = t := Int.toNat_of_nonneg ht0
  have htk : t < (k : ℤ) := by nlinarith
  refine ⟨i, by omega, ?_⟩
  simp only [term, hcast]
  nlinarith

theorem smooth_prime_log_sum_le_missing {k d : ℕ} {n : ℤ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range k) (hsmooth : Smooth k (progressionProduct n d S))
    (P : Finset ℕ) {X : ℝ} (hX : 1 ≤ X)
    (hP : ∀ p ∈ P, p.Prime ∧ k < p ∧ (p : ℝ) ≤ X)
    (hocc : ∀ p ∈ P, ∃ i : ℕ, i < k ∧ (term n d i).natAbs = p) :
    ∑ p ∈ P, Real.log (p : ℝ) ≤ ((k : ℝ) - S.card) * Real.log X := by
  classical
  let J := Finset.range k \ S
  have himage : P ⊆ J.image (fun i => (term n d i).natAbs) := by
    intro p hp
    obtain ⟨i, hik, hip⟩ := hocc p hp
    have hiS : i ∉ S := by
      intro hiS
      have hterm : Smooth k (term n d i) := hsmooth.of_dvd
        ((Finset.prod_ne_zero_iff.mp hsmooth.1) i hiS) (Finset.dvd_prod_of_mem (term n d) hiS)
      have hle := hterm.2 p (hP p hp).1 (by rw [hip])
      exact (not_le_of_gt (hP p hp).2.1) hle
    exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hik, hiS⟩, hip⟩
  have hcard : P.card ≤ J.card := (Finset.card_le_card himage).trans Finset.card_image_le
  have hsplit : J.card + S.card = k := by simpa only [J, Finset.card_range] using Finset.card_sdiff_add_card_eq_card hS
  have hcardR : (P.card : ℝ) ≤ (k : ℝ) - S.card := by
    have hc : (P.card : ℝ) ≤ J.card := by exact_mod_cast hcard
    have hs : (J.card : ℝ) + S.card = k := by exact_mod_cast hsplit
    linarith
  have hsum : ∑ p ∈ P, Real.log (p : ℝ) ≤ (P.card : ℝ) * Real.log X := by
    calc
      _ ≤ ∑ _p ∈ P, Real.log X := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log (by exact_mod_cast (hP p hp).1.pos) (hP p hp).2.2
      _ = _ := by simp
  exact hsum.trans (mul_le_mul_of_nonneg_right hcardR (Real.log_nonneg hX))

theorem thetaAP_le_missing_log {k d : ℕ} {n a : ℤ} {S : Finset ℕ} {x y : ℝ}
    (hS : S ⊆ Finset.range k) (hsmooth : Smooth k (progressionProduct n d S))
    (hx : 1 ≤ x) (hy : (k : ℝ) ≤ y)
    (hocc : ∀ p : ℕ, p.Prime → y < (p : ℝ) → (p : ℝ) ≤ x → Int.ModEq (d : ℤ) (p : ℤ) a →
      ∃ i : ℕ, i < k ∧ (term n d i).natAbs = p) :
    External.thetaAP x y d a ≤ ((k : ℝ) - S.card) * Real.log x := by
  classical
  unfold External.thetaAP
  apply smooth_prime_log_sum_le_missing hS hsmooth _ hx
  · intro p hp
    obtain ⟨hpK, hpy, hpmod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpxN, hpprime⟩ := Nat.mem_primesLE.mp hpK
    have hpx : (p : ℝ) ≤ x := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mp hpxN
    refine ⟨hpprime, ?_, hpx⟩
    exact_mod_cast (lt_of_le_of_lt hy hpy)
  · intro p hp
    obtain ⟨hpK, hpy, hpmod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpxN, hpprime⟩ := Nat.mem_primesLE.mp hpK
    exact hocc p hpprime hpy ((Nat.le_floor_iff (by linarith : 0 ≤ x)).mp hpxN) hpmod

theorem thetaAP_positive_window_le_missing {k d : ℕ} {n : ℤ} {S : Finset ℕ} {x y : ℝ}
    (hd : 0 < d) (hS : S ⊆ Finset.range k) (hsmooth : Smooth k (progressionProduct n d S))
    (hx : 1 ≤ x) (hy : (k : ℝ) ≤ y) (hny : (n : ℝ) ≤ y)
    (hxend : x < (n : ℝ) + (k : ℝ) * (d : ℝ)) :
    External.thetaAP x y d n ≤ ((k : ℝ) - S.card) * Real.log x := by
  apply thetaAP_le_missing_log hS hsmooth hx hy
  intro p hp hpy hpx hpmod
  have hnP : n ≤ (p : ℤ) := by exact_mod_cast (lt_of_le_of_lt hny hpy).le
  have hpEnd : (p : ℤ) < n + (k : ℤ) * (d : ℤ) := by exact_mod_cast (lt_of_le_of_lt hpx hxend)
  obtain ⟨i, hi, heq⟩ := exists_index_of_modEq hd hpmod hnP hpEnd
  exact ⟨i, hi, by rw [heq, Int.natAbs_natCast]⟩

theorem thetaAP_negative_window_le_missing {k d : ℕ} {n : ℤ} {S : Finset ℕ} {x y : ℝ}
    (hd : 0 < d) (hS : S ⊆ Finset.range k) (hsmooth : Smooth k (progressionProduct n d S))
    (hx : 1 ≤ x) (hy : (k : ℝ) ≤ y) (hxn : x ≤ -(n : ℝ))
    (hyend : -y ≤ (n : ℝ) + (k : ℝ) * (d : ℝ)) :
    External.thetaAP x y d (-n) ≤ ((k : ℝ) - S.card) * Real.log x := by
  apply thetaAP_le_missing_log hS hsmooth hx hy
  intro p hp hpy hpx hpmod
  have hnP : n ≤ -(p : ℤ) := by exact_mod_cast (show (n : ℝ) ≤ -(p : ℝ) by linarith)
  have hpEnd : -(p : ℤ) < n + (k : ℤ) * (d : ℤ) := by
    exact_mod_cast (show -(p : ℝ) < (n : ℝ) + (k : ℝ) * (d : ℝ) by linarith)
  have hmod : Int.ModEq (d : ℤ) (-(p : ℤ)) n := by simpa only [neg_neg] using hpmod.neg
  obtain ⟨i, hi, heq⟩ := exists_index_of_modEq hd hmod hnP hpEnd
  exact ⟨i, hi, by rw [heq, Int.natAbs_neg, Int.natAbs_natCast]⟩

end PerfectPowers
