module

public import PerfectPowers.Squares.OddProductBounds
public import PerfectPowers.Combinatorics.SpacedSets
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-! # The valuation upper bound for squarefree parts of an odd progression -/

public section

namespace PerfectPowers

theorem odd_prime_pow_dvd_oddPrefix {p h k : ℕ} (hp : 0 < p) (hodd : Odd p)
    (hbound : (2 * h - 1) * p ≤ k - 1) : p ^ h ∣ oddPrefix (k / 2) := by
  classical
  by_cases hh : h = 0
  · simp [hh]
  obtain ⟨t, ht⟩ := hodd
  let f : ℕ → ℕ := fun j => p * j + t
  have hinj : Set.InjOn f (↑(Finset.range h) : Set ℕ) := by
    intro i hi j hj hij
    dsimp [f] at hij
    nlinarith
  have hsub : (Finset.range h).image f ⊆ Finset.range (k / 2) := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hjh : j < h := Finset.mem_range.mp hj
    have hmul := Nat.mul_le_mul_right p (show 2 * j + 1 ≤ 2 * h - 1 by omega)
    apply Finset.mem_range.mpr
    dsimp [f]
    have hsmall := hmul.trans hbound
    have hsmall' : 2 * (p * j + t) + 1 ≤ k - 1 := by nlinarith
    omega
  have hdiv : (∏ _j ∈ Finset.range h, p) ∣ ∏ j ∈ Finset.range h, (2 * f j + 1) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    refine ⟨2 * j + 1, ?_⟩
    dsimp [f]
    nlinarith
  have himage : (∏ j ∈ Finset.range h, (2 * f j + 1)) =
      ∏ z ∈ (Finset.range h).image f, (2 * z + 1) :=
    (Finset.prod_image (f := fun z => 2 * z + 1) hinj).symm
  rw [himage] at hdiv
  have hsubdiv := Finset.prod_dvd_prod_of_subset ((Finset.range h).image f)
    (Finset.range (k / 2)) (fun z => 2 * z + 1) hsub
  simpa only [Finset.prod_const, Finset.card_range, oddPrefix] using hdiv.trans hsubdiv

theorem half_card_pow_dvd_oddPrefix {J : Finset ℕ} {p k : ℕ}
    (hp : 0 < p) (hodd : Odd p) (hJ : J ⊆ Finset.range k) (heven : Even J.card)
    (hspace : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → p ≤ Nat.dist i j) :
    p ^ (J.card / 2) ∣ oddPrefix (k / 2) := by
  have hcard := card_le_pred_div_add_one_of_spacing hp hJ hspace
  have hsub : J.card - 1 ≤ (k - 1) / p := Nat.sub_le_of_le_add hcard
  have hmul := (Nat.le_div_iff_mul_le hp).mp hsub
  apply odd_prime_pow_dvd_oddPrefix hp hodd
  have heq : 2 * (J.card / 2) = J.card := by obtain ⟨h, hh⟩ := heven; omega
  rwa [heq]

theorem squarefree_odd_product_dvd_oddPrefix_square {k : ℕ} {a : ℕ → ℕ}
    (ha : ∀ i < k, Squarefree (a i) ∧ Odd (a i))
    (hsq : IsSquare (∏ i ∈ Finset.range k, a i))
    (hspace : ∀ p : ℕ, p.Prime → ∀ i < k, p ∣ a i →
      ∀ j < k, p ∣ a j → i ≠ j → p ≤ Nat.dist i j) :
    (∏ i ∈ Finset.range k, a i) ∣ oddPrefix (k / 2) ^ 2 := by
  classical
  have hA : (∏ i ∈ Finset.range k, a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => (ha i (Finset.mem_range.mp hi)).1.ne_zero)
  apply (Nat.factorization_le_iff_dvd hA (pow_ne_zero _ (oddPrefix_pos _).ne')).mp
  intro p
  by_cases hp : p.Prime
  · let J := (Finset.range k).filter (fun i => p ∣ a i)
    have hJ : J ⊆ Finset.range k := Finset.filter_subset _ _
    have hcount : (∏ i ∈ Finset.range k, a i).factorization p = J.card := by
      rw [Nat.factorization_prod_apply (fun i hi => (ha i (Finset.mem_range.mp hi)).1.ne_zero)]
      simp only [J, Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hpi : p ∣ a i
      · simp only [ite_eq_left hpi]
        exact Nat.factorization_eq_one_of_squarefree (ha i (Finset.mem_range.mp hi)).1 hp hpi
      · simp [hpi, Nat.factorization_eq_zero_of_not_dvd hpi]
    by_cases hzero : J.card = 0
    · rw [hcount, hzero]
      exact Nat.zero_le _
    have hnonempty : J.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hnonempty
    have hi' := Finset.mem_filter.mp hi
    have hpodd : Odd p := hp.odd_of_ne_two (by
      intro hp2
      exact (ha i (Finset.mem_range.mp hi'.1)).2.not_two_dvd_nat (hp2 ▸ hi'.2))
    have heven : Even J.card := by
      obtain ⟨z, hz⟩ := hsq
      have hval := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_pow z 2)
      have heq : z ^ 2 = ∏ i ∈ Finset.range k, a i := by simpa only [pow_two] using hz.symm
      rw [heq, hcount] at hval
      exact ⟨z.factorization p, by simpa only [Finsupp.smul_apply, smul_eq_mul, two_mul] using hval⟩
    have hpow := half_card_pow_dvd_oddPrefix hp.pos hpodd hJ heven (by
      intro i hi j hj hne
      exact hspace p hp i (Finset.mem_range.mp (hJ hi)) (Finset.mem_filter.mp hi).2
        j (Finset.mem_range.mp (hJ hj)) (Finset.mem_filter.mp hj).2 hne)
    have hv : J.card / 2 ≤ (oddPrefix (k / 2)).factorization p :=
      (hp.pow_dvd_iff_le_factorization (oddPrefix_pos _).ne').mp hpow
    rw [hcount, Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    obtain ⟨h, hh⟩ := heven
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

end PerfectPowers
