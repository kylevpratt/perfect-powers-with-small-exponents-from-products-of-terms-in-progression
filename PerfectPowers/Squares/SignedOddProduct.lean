module

public import PerfectPowers.Squares.OddNonsquare
public import PerfectPowers.Basic.Products
import Mathlib.Tactic

/-! # Splitting a signed odd progression into its two positive prefixes -/

public section

namespace PerfectPowers

theorem progressionProduct_one_two (N : ℕ) :
    progressionProduct 1 2 (Finset.range N) = (oddPrefix N : ℤ) := by
  simp [progressionProduct, term, oddPrefix, Nat.cast_prod, Nat.cast_add, Nat.cast_mul, add_comm, mul_comm]

theorem signed_odd_product (N P : ℕ) :
    progressionProduct (1 - 2 * (N : ℤ)) 2 (Finset.range (N + P)) =
      (-1 : ℤ) ^ N * (oddPrefix N : ℤ) * (oddPrefix P : ℤ) := by
  have hsplit : progressionProduct (1 - 2 * (N : ℤ)) 2 (Finset.range (N + P)) =
      progressionProduct (1 - 2 * (N : ℤ)) 2 (Finset.range N) * progressionProduct 1 2 (Finset.range P) := by
    unfold progressionProduct
    rw [Finset.prod_range_add]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp only [term, Nat.cast_add, Nat.cast_ofNat]
    ring
  have hreflect := progressionProduct_reflect (1 - 2 * (N : ℤ)) 2 N
  have hstart : -(1 - 2 * (N : ℤ)) - ((N : ℤ) - 1) * (2 : ℕ) = 1 := by ring
  rw [hstart, progressionProduct_one_two] at hreflect
  rw [hsplit, hreflect, progressionProduct_one_two]

theorem even_negative_count_of_square {N P : ℕ}
    (hs : IsSquare (progressionProduct (1 - 2 * (N : ℤ)) 2 (Finset.range (N + P)))) : Even N := by
  have hnonneg := hs.nonneg
  rw [signed_odd_product] at hnonneg
  rcases Nat.even_or_odd N with hEven | hOdd
  · exact hEven
  · rw [hOdd.neg_one_pow] at hnonneg
    have hN : (0 : ℤ) < oddPrefix N := by exact_mod_cast oddPrefix_pos N
    have hP : (0 : ℤ) < oddPrefix P := by exact_mod_cast oddPrefix_pos P
    nlinarith

theorem oddPrefix_pair_square_of_signed_square {N P : ℕ}
    (hs : IsSquare (progressionProduct (1 - 2 * (N : ℤ)) 2 (Finset.range (N + P)))) :
    IsSquare (oddPrefix N * oddPrefix P) := by
  have hEven := even_negative_count_of_square hs
  rw [signed_odd_product, hEven.neg_one_pow, one_mul] at hs
  apply Int.isSquare_natCast_iff.mp
  simpa only [Nat.cast_mul] using hs

theorem exists_signed_odd_counts {k : ℕ} {n : ℤ} (hodd : Odd n)
    (hnlo : -2 * ((k : ℤ) - 1) < n) (hnhi : n < 0) :
    ∃ N P : ℕ, 0 < N ∧ 0 < P ∧ N + P = k ∧ n = 1 - 2 * (N : ℤ) := by
  obtain ⟨a, ha⟩ := hodd
  let N := (-a).toNat
  have hNcast : (N : ℤ) = -a := Int.toNat_of_nonneg (by omega)
  have hNpos : 0 < N := by omega
  have hNk : N < k := by omega
  refine ⟨N, k - N, hNpos, by omega, by omega, by omega⟩

/-- Pairing the two odd prefixes, using the proved Lemma 3.6. -/
theorem oddPrefix_pair_classification {N P : ℕ}
    (hN : Even N) (hs : IsSquare (oddPrefix N * oddPrefix P)) :
    (4 ∣ N + P ∧ 1 - 2 * (N : ℤ) = 1 - ((N + P : ℕ) : ℤ)) ∨
      (Odd (N + P) ∧ IsSquare (N + P) ∧ 1 - 2 * (N : ℤ) = 2 - ((N + P : ℕ) : ℤ)) := by
  have hNP : N ≤ P + 1 := by
    by_contra hn
    have hPN : P ≤ N := by omega
    have hsq : IsSquare (oddPrefix P * oddPrefix N) := by simpa only [mul_comm] using hs
    exact oddProgressionNonsquare (2 * P + 1) (N - P) (by omega) ⟨P, by omega⟩
      (by omega) (oddPrefix_gap_isSquare hPN hsq)
  have hPN : P ≤ N + 1 := by
    by_contra hn
    exact oddProgressionNonsquare (2 * N + 1) (P - N) (by omega) ⟨N, by omega⟩ (by omega)
      (oddPrefix_gap_isSquare (by omega) hs)
  rcases lt_trichotomy N P with hlt | heq | hgt
  · have hP : P = N + 1 := by omega
    have hdiff : P - N = 1 := by omega
    have hgap := oddPrefix_gap_isSquare (by omega : N ≤ P) hs
    rw [hdiff] at hgap
    have hlast : IsSquare (2 * N + 1) := by simpa using hgap
    have hsum : N + P = 2 * N + 1 := by omega
    refine Or.inr ⟨⟨N, by omega⟩, ?_, ?_⟩
    · rwa [hsum]
    · omega
  · obtain ⟨t, ht⟩ := hN
    refine Or.inl ⟨⟨t, by omega⟩, ?_⟩
    omega
  · have hN' : N = P + 1 := by omega
    have hdiff : N - P = 1 := by omega
    have hsq : IsSquare (oddPrefix P * oddPrefix N) := by simpa only [mul_comm] using hs
    have hgap := oddPrefix_gap_isSquare (by omega : P ≤ N) hsq
    rw [hdiff] at hgap
    have hlast : IsSquare (2 * P + 1) := by simpa using hgap
    obtain ⟨z, hz⟩ := hlast
    obtain ⟨t, ht⟩ := hN
    have hz4 : (z * z) % 4 = 3 := by rw [← hz]; omega
    exact (square_mod_four_ne_three z hz4).elim

theorem step_two_square_classification
    {k : ℕ} {n : ℤ} (hodd : Odd n) (hnlo : -2 * ((k : ℤ) - 1) < n) (hnhi : n < 0)
    (hs : IsSquare (progressionProduct n 2 (Finset.range k))) :
    (4 ∣ k ∧ n = 1 - (k : ℤ)) ∨ (Odd k ∧ IsSquare k ∧ n = 2 - (k : ℤ)) := by
  obtain ⟨N, P, hN, hP, hsum, hn⟩ := exists_signed_odd_counts hodd hnlo hnhi
  have hsq : IsSquare (progressionProduct (1 - 2 * (N : ℤ)) 2 (Finset.range (N + P))) := by
    simpa only [hsum, ← hn] using hs
  have hclass := oddPrefix_pair_classification (even_negative_count_of_square hsq)
    (oddPrefix_pair_square_of_signed_square hsq)
  rwa [← hn, hsum] at hclass

end PerfectPowers
