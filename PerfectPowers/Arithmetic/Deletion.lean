module

public import PerfectPowers.Arithmetic.FactorialDistances
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
# Maximal-valuation deletion (Lemma 3.2)

The core result is stated for positive natural coefficients. It gives the
stronger divisibility by `(k - 1)!` and includes the empty-set case.
-/

public section

namespace PerfectPowers

theorem valuation_bound_after_deleting_max {k p j : ℕ} {S I : Finset ℕ} {b : ℕ → ℕ}
    (hS : S ⊆ Finset.range k) (hI : I ⊆ S) (hj : j ∈ S) (hjI : j ∉ I)
    (hb : ∀ i ∈ S, b i ≠ 0)
    (hmax : ∀ i ∈ S, (b i).factorization p ≤ (b j).factorization p)
    (hgcd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.gcd (b i) (b j) ∣ Nat.dist i j) :
    (∏ i ∈ I, b i).factorization p ≤ (k - 1).factorial.factorization p := by
  classical
  have hjk := Finset.mem_range.mp (hS hj)
  have hsub : I ⊆ (Finset.range k).erase j := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨by intro hij; exact hjI (hij ▸ hi), hS (hI hi)⟩
  have hgap0 (i : ℕ) (hi : i ∈ (Finset.range k).erase j) : Nat.dist i j ≠ 0 :=
    (Nat.dist_pos_of_ne (Finset.mem_erase.mp hi).1).ne'
  have hprod0 : (∏ i ∈ (Finset.range k).erase j, Nat.dist i j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hgap0
  rw [Nat.factorization_prod_apply (fun i hi => hb i (hI hi))]
  calc
    (∑ i ∈ I, (b i).factorization p) ≤ ∑ i ∈ I, (Nat.dist i j).factorization p := by
      apply Finset.sum_le_sum
      intro i hi
      have his := hI hi
      have hij : i ≠ j := (Finset.mem_erase.mp (hsub hi)).1
      have hdiv := hgcd i his j hj hij
      have hdist0 := (Nat.dist_pos_of_ne hij).ne'
      have hgcd0 : Nat.gcd (b i) (b j) ≠ 0 := by
        intro hz
        have : Nat.dist i j = 0 := by simpa [hz] using hdiv
        exact hdist0 this
      have hv : (b i).factorization p = (Nat.gcd (b i) (b j)).factorization p := by
        rw [Nat.factorization_gcd (hb i his) (hb j hj)]
        change (b i).factorization p = min ((b i).factorization p) ((b j).factorization p)
        exact (min_eq_left (hmax i his)).symm
      rw [hv]
      exact (Nat.factorization_le_iff_dvd hgcd0 hdist0).mpr hdiv p
    _ ≤ ∑ i ∈ (Finset.range k).erase j, (Nat.dist i j).factorization p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = (∏ i ∈ (Finset.range k).erase j, Nat.dist i j).factorization p :=
      (Nat.factorization_prod_apply hgap0).symm
    _ ≤ (k - 1).factorial.factorization p :=
      (Nat.factorization_le_iff_dvd hprod0 (Nat.factorial_ne_zero _)).mpr
        (prod_dist_erase_dvd_factorial hjk) p

/-- Delete at most one maximal-valuation index for each prime at most `k`. -/
theorem exists_factorial_deletion {k : ℕ} {S : Finset ℕ} {b : ℕ → ℕ}
    (hS : S ⊆ Finset.range k) (hb : ∀ i ∈ S, b i ≠ 0)
    (hsmooth : ∀ i ∈ S, ∀ p : ℕ, p.Prime → p ∣ b i → p ≤ k)
    (hgcd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.gcd (b i) (b j) ∣ Nat.dist i j) :
    ∃ I : Finset ℕ, I ⊆ S ∧ S.card ≤ I.card + Nat.primeCounting k ∧
      (∏ i ∈ I, b i) ∣ (k - 1).factorial := by
  classical
  by_cases hne : S.Nonempty
  · have hmax : ∀ p : ℕ, ∃ j ∈ S, ∀ i ∈ S,
        (b i).factorization p ≤ (b j).factorization p := by
      intro p
      exact Finset.exists_max_image S (fun i => (b i).factorization p) hne
    choose j hj hjmax using hmax
    let P := Nat.primesLE k
    let removed := P.image j
    let I := S \ removed
    have hIS : I ⊆ S := Finset.sdiff_subset
    refine ⟨I, hIS, ?_, ?_⟩
    · calc
        S.card ≤ I.card + removed.card := Finset.card_le_card_sdiff_add_card
        _ ≤ I.card + P.card := Nat.add_le_add_left Finset.card_image_le _
        _ = I.card + Nat.primeCounting k := by rw [Nat.primesLE_card_eq_primeCounting]
    · have hprod0 : (∏ i ∈ I, b i) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i hi => hb i (hIS hi))
      apply (Nat.factorization_le_iff_dvd hprod0 (Nat.factorial_ne_zero _)).mp
      intro p
      by_cases hp : p.Prime
      · by_cases hpk : p ≤ k
        · have hpP : p ∈ P := Nat.mem_primesLE.mpr ⟨hpk, hp⟩
          have hjI : j p ∉ I := by
            intro hmem
            exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_image.mpr ⟨p, hpP, rfl⟩)
          exact valuation_bound_after_deleting_max hS hIS (hj p) hjI hb (hjmax p) hgcd
        · have hzero : (∏ i ∈ I, b i).factorization p = 0 := by
            rw [Nat.factorization_prod_apply (fun i hi => hb i (hIS hi))]
            apply Finset.sum_eq_zero
            intro i hi
            apply Nat.factorization_eq_zero_of_not_dvd
            intro hdiv
            exact hpk (hsmooth i (hIS hi) p hp hdiv)
          rw [hzero]
          exact Nat.zero_le _
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    exact ⟨∅, by simp, by simp, by simp⟩

end PerfectPowers
