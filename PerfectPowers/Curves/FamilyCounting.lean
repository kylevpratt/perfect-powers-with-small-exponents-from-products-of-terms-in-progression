module

public import PerfectPowers.Curves.Counting
public import PerfectPowers.Curves.FiniteFamilies
import Mathlib.Tactic

/-!
# Counting distinct points spread over finitely many curve equations

One descriptor-counting argument handles every signed coefficient box. The
unit-coefficient and power-sized boxes used in the two main applications
are specializations. Finiteness is needed only for actual equations in the
family and is supplied from the agreed geometric inputs in the final theorem.
-/

public section

namespace PerfectPowers

theorem card_le_card_mul_of_real_fiber_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (K : Finset κ) (key : ι → κ) {U : ℝ}
    (hmap : ∀ i ∈ s, key i ∈ K)
    (hbound : ∀ c ∈ K, ((s.filter (fun i => key i = c)).card : ℝ) ≤ U) :
    (s.card : ℝ) ≤ (K.card : ℝ) * U := by
  classical
  have heq := Finset.card_eq_sum_card_fiberwise (s := s) (t := K) (f := key) hmap
  have heqR : (s.card : ℝ) = ∑ c ∈ K, ((s.filter (fun i => key i = c)).card : ℝ) := by
    exact_mod_cast heq
  rw [heqR]
  calc
    _ ≤ ∑ _c ∈ K, U := Finset.sum_le_sum hbound
    _ = (K.card : ℝ) * U := by simp

theorem card_le_coefficient_box_of_finite {ι : Type*}
    (hRemond : External.RemondStatement) {ell m L M : ℕ} (hell : 0 < ell)
    (hM : M ≤ (L + 1) ^ m)
    (s : Finset ι) (B : ι → ℤ) (C : ι → Fin m → ℤ) (P : ι → ℚ × ℚ)
    (hB : ∀ i ∈ s, (B i).natAbs ≤ M)
    (hC : ∀ i ∈ s, ∀ j, 1 ≤ C i j ∧ C i j ≤ (L : ℤ))
    (hpoint : ∀ i ∈ s, OnCurve ell (B i) (C i) (P i))
    (hinj : Set.InjOn P (↑s : Set ι))
    (hfinite : ∀ i ∈ s, (External.RationalZeros (curvePolynomial ell (B i) (C i))).Finite) :
    (s.card : ℝ) ≤ (((2 * M + 1) * L ^ m : ℕ) : ℝ) *
      External.remondBound (max ell m) (3 * (L + 1) ^ m) := by
  classical
  let key : ι → ℤ × (Fin m → ℤ) := fun i => (B i, C i)
  let K := boundedCurveDescriptors m M L
  have hmap : ∀ i ∈ s, key i ∈ K := by
    intro i hi
    apply mem_boundedCurveDescriptors.mpr
    have habs : |B i| ≤ (M : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hB i hi
    exact ⟨abs_le.mp habs, hC i hi⟩
  have hbound (bc : ℤ × (Fin m → ℤ)) (hbc : bc ∈ K) :
      ((s.filter (fun i => key i = bc)).card : ℝ) ≤
        External.remondBound (max ell m) (3 * (L + 1) ^ m) := by
    let fiber := s.filter (fun i => key i = bc)
    by_cases hne : fiber.Nonempty
    · obtain ⟨i0, hi0⟩ := hne
      obtain ⟨hi0s, hi0key⟩ := Finset.mem_filter.mp hi0
      let points := fiber.image P
      have hcard : points.card = fiber.card := Finset.card_image_of_injOn
        (fun i hi j hj hij => hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij)
      have hpoints : ∀ Q ∈ points, OnCurve ell (B i0) (C i0) Q := by
        intro Q hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨his, hikey⟩ := Finset.mem_filter.mp hi
        have hkeys := hikey.trans hi0key.symm
        have hBs : B i = B i0 := congrArg Prod.fst hkeys
        have hCs : C i = C i0 := congrArg Prod.snd hkeys
        simpa only [hBs, hCs] using hpoint i his
      have h := curve_rational_points_bound_of_finite hRemond hell ((hB i0 hi0s).trans hM)
        (fun j => le_trans (by norm_num) (hC i0 hi0s j).1) (fun j => (hC i0 hi0s j).2)
        (hfinite i0 hi0s) points hpoints
      rw [hcard] at h
      exact h
    · change (fiber.card : ℝ) ≤ _
      rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.card_empty, Nat.cast_zero]
      unfold External.remondBound
      exact (Real.exp_pos _).le
  have h := card_le_card_mul_of_real_fiber_bound s K key hmap hbound
  have hK : K.card = (2 * M + 1) * L ^ m := card_boundedCurveDescriptors m M L
  rwa [hK] at h

/-- The unit-coefficient box used for heavy fibers. -/
theorem card_le_curve_family_bound_of_finite {ι : Type*}
    (hRemond : External.RemondStatement) {ell m L : ℕ} (hell : 0 < ell)
    (s : Finset ι) (B : ι → ℤ) (C : ι → Fin m → ℤ) (P : ι → ℚ × ℚ)
    (hB : ∀ i ∈ s, (B i).natAbs ≤ 1)
    (hC : ∀ i ∈ s, ∀ j, 1 ≤ C i j ∧ C i j ≤ (L : ℤ))
    (hpoint : ∀ i ∈ s, OnCurve ell (B i) (C i) (P i))
    (hinj : Set.InjOn P (↑s : Set ι))
    (hfinite : ∀ i ∈ s, (External.RationalZeros (curvePolynomial ell (B i) (C i))).Finite) :
    (s.card : ℝ) ≤ (3 * L ^ m : ℕ) * External.remondBound (max ell m) (3 * (L + 1) ^ m) := by
  simpa using card_le_coefficient_box_of_finite hRemond hell
    (Nat.one_le_pow m (L + 1) (by omega)) s B C P hB hC hpoint hinj hfinite

/-- The coefficient box used for common-divisor tuples in Proposition 3.5. -/
theorem card_le_power_curve_family_bound_of_finite {ι : Type*}
    (hRemond : External.RemondStatement) {ell m L : ℕ} (hell : 0 < ell) (hL : 1 ≤ L)
    (s : Finset ι) (B : ι → ℤ) (C : ι → Fin m → ℤ) (P : ι → ℚ × ℚ)
    (hB : ∀ i ∈ s, (B i).natAbs ≤ L ^ m)
    (hC : ∀ i ∈ s, ∀ j, 1 ≤ C i j ∧ C i j ≤ (L : ℤ))
    (hpoint : ∀ i ∈ s, OnCurve ell (B i) (C i) (P i))
    (hinj : Set.InjOn P (↑s : Set ι))
    (hfinite : ∀ i ∈ s, (External.RationalZeros (curvePolynomial ell (B i) (C i))).Finite) :
    (s.card : ℝ) ≤ ((3 * L ^ (2 * m) : ℕ) : ℝ) *
      External.remondBound (max ell m) (3 * (L + 1) ^ m) := by
  have h := card_le_coefficient_box_of_finite hRemond hell
    (Nat.pow_le_pow_left (Nat.le_succ L) m) s B C P hB hC hpoint hinj hfinite
  have hpow : 1 ≤ L ^ m := Nat.one_le_pow m L hL
  have hnum : (2 * L ^ m + 1) * L ^ m ≤ 3 * L ^ (2 * m) := by
    rw [show 2 * m = m + m by omega, pow_add]
    nlinarith
  have hnumR : (((2 * L ^ m + 1) * L ^ m : ℕ) : ℝ) ≤ (3 * L ^ (2 * m) : ℕ) := by exact_mod_cast hnum
  exact h.trans (mul_le_mul_of_nonneg_right hnumR (by unfold External.remondBound; positivity))

end PerfectPowers
