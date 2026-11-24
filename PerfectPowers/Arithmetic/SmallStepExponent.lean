module

public import PerfectPowers.Arithmetic.LargePrimes
public import PerfectPowers.Combinatorics.SpacedSets
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Exponent two for full products with step one or two

A prime between `k/2` and `k` divides one or two terms. Every term has
absolute value below its square, so its product valuation is one or two.
The equation with `b = 1` then forces the exponent to equal two.
-/

public section

namespace PerfectPowers

theorem exists_prime_dividing_progression_term {p k d : ℕ} (hp : p.Prime)
    (hd : 0 < d) (hdp : d < p) (hpk : p ≤ k) (n : ℤ) :
    ∃ i : ℕ, i < k ∧ p ∣ (term n d i).natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  have hd0 : (d : ZMod p) ≠ 0 := by
    intro hz
    have hdiv := (ZMod.natCast_eq_zero_iff d p).mp hz
    have hle := Nat.le_of_dvd hd hdiv
    omega
  let z : ZMod p := -(n : ZMod p) / (d : ZMod p)
  refine ⟨z.val, (ZMod.val_lt z).trans_le hpk, ?_⟩
  apply Int.ofNat_dvd_left.mp
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (term n d z.val) p).mp
  simp only [term, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  dsimp [z]
  field_simp
  ring

theorem exists_prime_large_square (k : ℕ) (hk : 21 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ p ≤ k ∧ k < 2 * p ∧ 5 * k < p ^ 2 ∧ 2 < p := by
  obtain ⟨p, hp, hplow, hphigh⟩ := Nat.bertrand (k / 2) (by omega)
  have hpk : p ≤ k := by omega
  have hk2p : k < 2 * p := by omega
  have hp11 : 11 ≤ p := by omega
  have hmul := Nat.mul_le_mul_left p hp11
  refine ⟨p, hp, hpk, hk2p, ?_, by omega⟩
  nlinarith

theorem factorization_eq_indicator_of_lt_square {N p : ℕ} (hN : N ≠ 0) (hp : p.Prime)
    (hlt : N < p ^ 2) : N.factorization p = if p ∣ N then 1 else 0 := by
  by_cases hdiv : p ∣ N
  · rw [ite_eq_left hdiv]
    have hpos := (hp.dvd_iff_one_le_factorization hN).mp hdiv
    have hltv : N.factorization p < 2 := by
      by_contra hn
      have hpow : p ^ 2 ∣ N := (hp.pow_dvd_iff_le_factorization hN).mpr (by omega)
      exact (not_le_of_gt hlt) (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hpow)
    omega
  · rw [ite_eq_right hdiv]
    exact Nat.factorization_eq_zero_of_not_dvd hdiv

theorem Solution.exponent_eq_two_of_small_step {k ell d : ℕ} {n y : ℤ}
    (h : Solution k ell n d 1 y (Finset.range k)) (hk : 21 ≤ k) (hell : 2 ≤ ell)
    (hd : d = 1 ∨ d = 2) (hn : n.natAbs ≤ 3 * k) : ell = 2 := by
  classical
  obtain ⟨p, hp, hpk, hk2p, hpsq, hp2⟩ := exists_prime_large_square k hk
  have hd2 : d ≤ 2 := by omega
  obtain ⟨i0, hi0, hpi0⟩ := exists_prime_dividing_progression_term hp h.d_pos (by omega) hpk n
  let J := (Finset.range k).filter (fun i => p ∣ (term n d i).natAbs)
  have hJpos : 0 < J.card := Finset.card_pos.mpr ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi0, hpi0⟩⟩
  have hJbound : J.card ≤ 2 := by
    have hcount : J.card ≤ k / p + 1 := by
      apply card_le_div_add_one_of_spacing hp.pos (Finset.filter_subset _ _)
      intro i hi j hj hne
      obtain ⟨hiK, hpi⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjK, hpj⟩ := Finset.mem_filter.mp hj
      rcases lt_or_gt_of_ne hne with hij | hji
      · rw [Nat.dist_eq_sub_of_le hij.le]
        exact common_divisor_le_index_gap h.coprime hij hpi hpj
      · rw [Nat.dist_eq_sub_of_le_right hji.le]
        exact common_divisor_le_index_gap h.coprime hji hpj hpi
    have hquot : k / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
    omega
  have hterm (i : ℕ) (hi : i ∈ Finset.range k) : (term n d i).natAbs < p ^ 2 := by
    have hik := Finset.mem_range.mp hi
    have htri := Int.natAbs_add_le n ((i : ℤ) * (d : ℤ))
    change (term n d i).natAbs ≤ _ at htri
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at htri
    nlinarith
  have hval : (progressionProduct n d (Finset.range k)).natAbs.factorization p = J.card := by
    rw [natAbs_progressionProduct, Nat.factorization_prod_apply
      (fun i hi => Int.natAbs_ne_zero.mpr (h.term_ne_zero hi))]
    calc
      _ = ∑ i ∈ Finset.range k, (if p ∣ (term n d i).natAbs then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact factorization_eq_indicator_of_lt_square
          (Int.natAbs_ne_zero.mpr (h.term_ne_zero hi)) hp (hterm i hi)
      _ = J.card := Finset.sum_boole _ _
  have hnat : (progressionProduct n d (Finset.range k)).natAbs = y.natAbs ^ ell := by
    rw [h.equation, one_mul, Int.natAbs_pow]
  have hvaleq : J.card = ell * y.natAbs.factorization p := by
    rw [← hval, hnat]
    simp [Nat.factorization_pow]
  have hyone : 1 ≤ y.natAbs.factorization p := by
    by_contra hn
    have hzero : y.natAbs.factorization p = 0 := by omega
    rw [hzero, mul_zero] at hvaleq
    omega
  have hellle : ell ≤ J.card := by
    rw [hvaleq]
    simpa only [mul_one] using Nat.mul_le_mul_left ell hyone
  omega

end PerfectPowers
