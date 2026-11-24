module

public import PerfectPowers.Arithmetic.PrimeWeight
public import PerfectPowers.Analytic.PrimeAPEnvelope
import Mathlib.Tactic

/-!
# The small-step conclusion in Theorem 1.5

Only the permitted Lemma 3.3 is used for prime distribution here. Its constant
is chosen before the absolute threshold; neither depends on the exponent.
-/

public section

open Filter

namespace PerfectPowers

theorem PrimeAPEnvelope.small_step {k d : ℕ} {n : ℤ} {S : Finset ℕ} {C : ℝ}
    (hE : PrimeAPEnvelope k C) (hC : 0 ≤ C)
    (hAP : ∀ (x y : ℝ) (a : ℤ), 5 ≤ y → y ≤ x →
      (d : ℝ) ≤ (Real.log x) ^ (199 / 100 : ℝ) → Nat.Coprime a.natAbs d →
      |External.thetaAP x y d a - (x - y) / (Nat.totient d : ℝ)| ≤ C * x / (Real.log x) ^ 5)
    (hd : 0 < d) (hcoprime : Nat.Coprime n.natAbs d)
    (hS : S ⊆ Finset.range k) (hsmooth : Smooth k (progressionProduct n d S))
    (hdense : VeryDense k S)
    (hdbound : (d : ℝ) ≤ 3 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ))
    (hnbound : n.natAbs ≤ k * (d + 1)) : d = 1 ∨ d = 2 := by
  by_contra hsmall
  have hd3 : 3 ≤ d := by omega
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hE.k_ge
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  have hkpos : (0 : ℝ) < k := by linarith
  have hLpos : 0 < Real.log (k : ℝ) := by linarith [hE.log_ge]
  let R := (Real.log (k : ℝ)) ^ (3 / 2 : ℝ)
  have hR : 0 < R := Real.rpow_pos_of_pos hLpos _
  have hR1 : 1 ≤ R := Real.one_le_rpow hE.log_ge (by norm_num)
  have hN : |n| ≤ (k : ℤ) * ((d : ℤ) + 1) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnbound
  have hNlo : -(k : ℝ) * ((d : ℝ) + 1) ≤ (n : ℝ) := by
    have h : -((k : ℝ) * ((d : ℝ) + 1)) ≤ (n : ℝ) := by
      exact_mod_cast (abs_le.mp hN).1
    linarith
  have hNhi : (n : ℝ) ≤ (k : ℝ) * ((d : ℝ) + 1) := by
    exact_mod_cast (abs_le.mp hN).2
  have hphi : (0 : ℝ) < Nat.totient d := by exact_mod_cast (Nat.totient_pos.mpr hd)
  have hphiLe : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have impossible : ∀ (x y : ℝ) (a : ℤ), 5 ≤ y → y ≤ x →
      (k : ℝ) ≤ x → x ≤ 7 * (k : ℝ) * R → Nat.Coprime a.natAbs d →
      External.thetaAP x y d a ≤ ((k : ℝ) - S.card) * Real.log x →
      (k : ℝ) / (12 * R) ≤ (x - y) / (Nat.totient d : ℝ) → False := by
    intro x y a hy hyx hxlo hxhi hcop hupper hmain
    have hlog : Real.log (k : ℝ) ≤ Real.log x := Real.log_le_log hkpos hxlo
    have hmod : (d : ℝ) ≤ (Real.log x) ^ (199 / 100 : ℝ) := by
      exact hdbound.trans (hE.modulus.trans (Real.rpow_le_rpow hLpos.le hlog (by norm_num)))
    have herr := hAP x y a hy hyx hmod hcop
    have hxquad : x ≤ (k : ℝ) ^ 2 := by nlinarith [hE.seven]
    exact prime_weight_estimate_contradiction (by have := hE.k_ge; omega : 5 ≤ k) hC hR
      (log_three_halves_square hLpos.le) hE.cost hxlo hxhi hxquad hdense hupper herr hmain
  by_cases hn : -(3 / 2 : ℝ) * (k : ℝ) < (n : ℝ)
  · let x : ℝ := (n : ℝ) + ((k : ℝ) - 1) * (d : ℝ)
    let y : ℝ := (n : ℝ) + (5 / 2 : ℝ) * (k : ℝ)
    have hyk : (k : ℝ) ≤ y := by dsimp [y]; linarith
    have hwidth : (d : ℝ) * (k : ℝ) / 12 ≤ x - y := by
      have hmul := mul_le_mul_of_nonneg_right hdR (by linarith : 0 ≤ 11 * (k : ℝ) / 12 - 1)
      dsimp [x, y]
      nlinarith
    have hyx : y ≤ x := by have := div_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ d) hkpos.le) (by norm_num : (0 : ℝ) ≤ 12); linarith
    have hxhi : x ≤ 7 * (k : ℝ) * R := by
      have hdR' : (d : ℝ) ≤ 3 * R := hdbound
      have hmul := mul_le_mul_of_nonneg_left hdR' hkpos.le
      dsimp [x]
      nlinarith
    have hupper := thetaAP_positive_window_le_missing hd hS hsmooth
      (by linarith : 1 ≤ x) hyk (by dsimp [y]; linarith)
      (by dsimp [x]; nlinarith : x < (n : ℝ) + (k : ℝ) * (d : ℝ))
    have hmain0 : (k : ℝ) / 12 ≤ (x - y) / (Nat.totient d : ℝ) := by
      apply (le_div_iff₀ hphi).mpr
      have := mul_le_mul_of_nonneg_right hphiLe hkpos.le
      nlinarith
    have hmain : (k : ℝ) / (12 * R) ≤ (x - y) / (Nat.totient d : ℝ) := by
      exact (div_le_div_of_nonneg_left hkpos.le (by norm_num : (0 : ℝ) < 12)
        (by nlinarith : (12 : ℝ) ≤ 12 * R)).trans hmain0
    exact impossible x y n (by linarith) hyx (hyk.trans hyx) hxhi hcoprime hupper hmain
  · let x : ℝ := -(n : ℝ)
    let y : ℝ := (k : ℝ)
    have hwidth : (k : ℝ) / 2 ≤ x - y := by dsimp [x, y]; linarith
    have hyx : y ≤ x := by dsimp [x, y]; linarith
    have hxhi : x ≤ 7 * (k : ℝ) * R := by
      have hdR' : (d : ℝ) ≤ 3 * R := hdbound
      have hmul := mul_le_mul_of_nonneg_left hdR' hkpos.le
      dsimp [x]
      nlinarith
    have hupper := thetaAP_negative_window_le_missing hd hS hsmooth
      (by dsimp [x]; linarith : 1 ≤ x) (by rfl : (k : ℝ) ≤ y)
      (by rfl : x ≤ -(n : ℝ)) (by dsimp [y]; linarith : -y ≤ (n : ℝ) + (k : ℝ) * (d : ℝ))
    have hmain : (k : ℝ) / (12 * R) ≤ (x - y) / (Nat.totient d : ℝ) := by
      apply (le_div_iff₀ hphi).mpr
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 12 * R)).mpr
      have hphiR : (Nat.totient d : ℝ) ≤ 3 * R := hphiLe.trans hdbound
      have hmul := mul_le_mul_of_nonneg_left hphiR hkpos.le
      have hwidth' := mul_le_mul_of_nonneg_right hwidth (by positivity : 0 ≤ 12 * R)
      nlinarith
    exact impossible x y (-n) (by dsimp [y]; linarith) hyx hyx hxhi
      (by simpa only [Int.natAbs_neg] using hcoprime) hupper hmain

theorem eventually_small_step_of_primeAP (hAP : External.PrimeAPStatement) :
    ∀ᶠ k : ℕ in atTop, ∀ (n : ℤ) (d : ℕ) (S : Finset ℕ),
      0 < d → Nat.Coprime n.natAbs d → S ⊆ Finset.range k →
      Smooth k (progressionProduct n d S) → VeryDense k S →
      (d : ℝ) ≤ 3 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) →
      n.natAbs ≤ k * (d + 1) → d = 1 ∨ d = 2 := by
  obtain ⟨C, hC, hAPC⟩ := hAP 5 (by norm_num)
  filter_upwards [eventually_primeAPEnvelope hC.le] with k hE
  intro n d S hd hcop hS hsmooth hdense hdb hnb
  by_cases hd2 : 2 ≤ d
  · apply hE.small_step hC.le (fun x y a hy hyx hmod hcop => ?_) hd hcop hS hsmooth hdense hdb hnb
    simpa only [Real.rpow_ofNat] using hAPC x y d a hy hyx hd2 hmod hcop
  · left
    omega

end PerfectPowers
