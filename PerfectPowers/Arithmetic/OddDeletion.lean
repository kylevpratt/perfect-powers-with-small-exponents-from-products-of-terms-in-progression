module

public import PerfectPowers.Arithmetic.GoodIndices
public import PerfectPowers.Arithmetic.PrimeParts
import Mathlib.Tactic

/-!
# Odd-prime deletion for the auxiliary prime fact in Lemma 3.6

Omitting the prime two saves one deletion. The remaining product divides the
odd part of the factorial. `Squares.OddLongStartPrime` uses this conclusion
with the quantitative bounds to prove the large-prime fact.
-/

@[expose] public section

namespace PerfectPowers

def oddPart (N : ℕ) : ℕ := primePart (fun p => p ≠ 2) N

theorem oddPart_pos (N : ℕ) : 0 < oddPart N := primePart_pos _ _

theorem odd_dvd_oddPart {a N : ℕ} (ha : a ≠ 0) (hN : N ≠ 0)
    (hodd : Odd a) (hdiv : a ∣ N) : a ∣ oddPart N := by
  apply (Nat.factorization_le_iff_dvd ha (oddPart_pos N).ne').mp
  intro p
  change a.factorization p ≤ (primePart (fun p => p ≠ 2) N).factorization p
  rw [factorization_primePart, Finsupp.filter_apply]
  split_ifs with hp
  · exact (Nat.factorization_le_iff_dvd ha hN).mpr hdiv p
  · have hp2 : p = 2 := by tauto
    subst p
    simp [Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat]

theorem exists_odd_factorial_deletion {k : ℕ} {S : Finset ℕ} {b : ℕ → ℕ}
    (hk : 2 ≤ k) (hS : S ⊆ Finset.range k) (hb : ∀ i ∈ S, b i ≠ 0)
    (hodd : ∀ i ∈ S, Odd (b i))
    (hsmooth : ∀ i ∈ S, ∀ p : ℕ, p.Prime → p ∣ b i → p ≤ k)
    (hgcd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.gcd (b i) (b j) ∣ Nat.dist i j) :
    ∃ I : Finset ℕ, I ⊆ S ∧ S.card + 1 ≤ I.card + Nat.primeCounting k ∧
      (∏ i ∈ I, b i) ∣ oddPart (k - 1).factorial := by
  classical
  have htwo : 2 ∈ Nat.primesLE k := Nat.mem_primesLE.mpr ⟨hk, Nat.prime_two⟩
  have hpi : 1 ≤ Nat.primeCounting k := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_pos.mpr ⟨2, htwo⟩
  by_cases hne : S.Nonempty
  · have hmax : ∀ p : ℕ, ∃ j ∈ S, ∀ i ∈ S,
        (b i).factorization p ≤ (b j).factorization p := by
      intro p
      exact Finset.exists_max_image S (fun i => (b i).factorization p) hne
    choose j hj hjmax using hmax
    let P := (Nat.primesLE k).erase 2
    let removed := P.image j
    let I := S \ removed
    have hIS : I ⊆ S := Finset.sdiff_subset
    have hPcard : P.card + 1 = Nat.primeCounting k := by
      simpa only [P, Nat.primesLE_card_eq_primeCounting] using Finset.card_erase_add_one htwo
    have hprod0 : (∏ i ∈ I, b i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i hi => hb i (hIS hi))
    have hprodOdd : Odd (∏ i ∈ I, b i) := by
      exact Finset.prod_induction b (fun z : ℕ => Odd z)
        (fun _ _ ha hb => ha.mul hb) (by decide) (fun i hi => hodd i (hIS hi))
    refine ⟨I, hIS, ?_, odd_dvd_oddPart hprod0 (Nat.factorial_ne_zero _) hprodOdd ?_⟩
    · have hcard := Finset.card_le_card_sdiff_add_card (s := S) (t := removed)
      have hrem : removed.card ≤ P.card := Finset.card_image_le
      change S.card ≤ I.card + removed.card at hcard
      omega
    · apply (Nat.factorization_le_iff_dvd hprod0 (Nat.factorial_ne_zero _)).mp
      intro p
      by_cases hp2 : p = 2
      · subst p
        rw [Nat.factorization_eq_zero_of_not_dvd hprodOdd.not_two_dvd_nat]
        exact Nat.zero_le _
      by_cases hp : p.Prime
      · by_cases hpk : p ≤ k
        · have hpP : p ∈ P := Finset.mem_erase.mpr ⟨hp2, Nat.mem_primesLE.mpr ⟨hpk, hp⟩⟩
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
    exact ⟨∅, by simp, by simpa using hpi, by simp⟩

/-- The deletion conclusion used by the quantitative proof of the long-start
auxiliary prime fact. -/
theorem exists_odd_progression_deletion {k m : ℕ} (hk : 2 ≤ k)
    (hm : 0 < m) (hodd : Odd m)
    (hsmooth : ∀ p : ℕ, p.Prime →
      p ∣ (∏ i ∈ Finset.range k, (m + 2 * i)) → p ≤ k) :
    ∃ I : Finset ℕ, I ⊆ Finset.range k ∧ k + 1 ≤ I.card + Nat.primeCounting k ∧
      (∏ i ∈ I, (m + 2 * i)) ∣ oddPart (k - 1).factorial := by
  have hnat (i : ℕ) : (term (m : ℤ) 2 i).natAbs = m + 2 * i := by
    have heq : term (m : ℤ) 2 i = ((m + 2 * i : ℕ) : ℤ) := by simp [term]; ring
    rw [heq, Int.natAbs_natCast]
  have hcoprime : Nat.Coprime (m : ℤ).natAbs 2 := by
    simpa only [Int.natAbs_natCast] using Nat.coprime_two_right.mpr hodd
  have h := exists_odd_factorial_deletion (b := fun i => m + 2 * i) hk (Finset.Subset.refl _)
    (by intro i hi; omega)
    (by intro i hi; exact hodd.add_even ⟨i, by omega⟩)
    (by
      intro i hi p hp hdiv
      exact hsmooth p hp (hdiv.trans (Finset.dvd_prod_of_mem (fun i => m + 2 * i) hi)))
    (by
      intro i hi j hj hne
      have hgcd := gcd_natAbs_dvd_dist (gcd_terms_dvd_index_sub hcoprime i j)
      simpa only [hnat] using hgcd)
  simpa only [Finset.card_range] using h

end PerfectPowers
