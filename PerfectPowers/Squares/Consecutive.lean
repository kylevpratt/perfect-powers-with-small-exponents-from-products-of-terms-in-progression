module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
# The square obstruction for short starting points

The result here is restricted to `1 ≤ a ≤ k`. It is the consecutive-integer
obstruction needed after the full-product classification in the paper.
-/

public section

namespace PerfectPowers

/-- A natural number with an odd prime-factor multiplicity is not a square. -/
theorem not_isSquare_of_factorization_eq_one {N p : ℕ}
    (h : N.factorization p = 1) : ¬ IsSquare N := by
  rintro ⟨x, rfl⟩
  have hpow : (x * x).factorization p = 2 * x.factorization p := by
    simpa [pow_two] using congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_pow x 2)
  omega

/-- Bertrand supplies a prime in the interval, with no other positive multiple
of that prime in the interval. The endpoint argument includes `a = 1, k = 2`. -/
theorem exists_prime_in_short_start_interval (k a : ℕ)
    (hk : 2 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) :
    ∃ p : ℕ, p.Prime ∧ a ≤ p ∧ p < a + k ∧ a + k ≤ 2 * p := by
  let t := (a + k) / 2
  have ht : t ≠ 0 := by dsimp [t]; omega
  obtain ⟨p, hp, htp, hpt⟩ := Nat.bertrand t ht
  have hat : a ≤ t := by dsimp [t]; omega
  have hpsum : p < a + k := by
    by_contra h
    have hpeq : p = 2 * t := by dsimp [t] at *; omega
    have htdvd : t ∣ p := ⟨2, by omega⟩
    rcases hp.eq_one_or_self_of_dvd t htdvd with h1 | h1
    · dsimp [t] at *
      omega
    · omega
  refine ⟨p, hp, by omega, hpsum, ?_⟩
  dsimp [t] at *
  omega

/-- A positive number smaller than `2 * p` divisible by `p` must equal `p`. -/
theorem eq_of_dvd_of_lt_two_mul {p N : ℕ} (_hp : 0 < p) (hN : 0 < N)
    (hlt : N < 2 * p) (hdvd : p ∣ N) : N = p := by
  obtain ⟨q, hq⟩ := hdvd
  have hqpos : 0 < q := by nlinarith
  have hqone : q = 1 := by nlinarith
  simpa [hqone] using hq

/-- The prime from Bertrand has multiplicity exactly one in the product. -/
theorem exists_prime_factorization_consecutive_eq_one (k a : ℕ)
    (hk : 2 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) :
    ∃ p : ℕ, p.Prime ∧ (∏ i ∈ Finset.range k, (a + i)).factorization p = 1 := by
  obtain ⟨p, hp, hap, hpk, h2p⟩ := exists_prime_in_short_start_interval k a hk ha hak
  have hmem : p - a ∈ Finset.range k := by simp only [Finset.mem_range]; omega
  refine ⟨p, hp, ?_⟩
  rw [Nat.factorization_prod_apply (fun i hi => by omega)]
  rw [Finset.sum_eq_single (p - a)]
  · simpa [Nat.add_sub_of_le hap] using hp.factorization_self
  · intro i hi hne
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    have heq : a + i = p := eq_of_dvd_of_lt_two_mul hp.pos (by omega)
      (by have := Finset.mem_range.mp hi; omega) hdvd
    omega
  · exact fun h => (h hmem).elim

/-- The restricted consecutive-product nonsquareness used in Theorem 1.2.
This theorem makes no claim for starting points `a > k`. -/
theorem not_isSquare_consecutive_of_start_le_length (k a : ℕ)
    (hk : 2 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) :
    ¬ IsSquare (∏ i ∈ Finset.range k, (a + i)) := by
  obtain ⟨p, _, hp⟩ := exists_prime_factorization_consecutive_eq_one k a hk ha hak
  exact not_isSquare_of_factorization_eq_one hp

end PerfectPowers
