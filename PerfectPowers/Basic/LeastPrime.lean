module

public import PerfectPowers.Basic.PrimeSupport
public import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-! # The least prime above the progression length -/

public section

namespace PerfectPowers

theorem exists_leastPrimeAbove (k : ℕ) : ∃ p : ℕ, LeastPrimeAbove k p := by
  have hex : ∃ p : ℕ, k < p ∧ p.Prime := by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (k + 1)
    exact ⟨p, by omega, hprime⟩
  exact ⟨Nat.find hex, (Nat.find_spec hex).2, (Nat.find_spec hex).1,
    fun q hq hkq => Nat.find_min' hex ⟨hkq, hq⟩⟩

theorem LeastPrimeAbove.unique {k p q : ℕ} (hp : LeastPrimeAbove k p)
    (hq : LeastPrimeAbove k q) : p = q :=
  Nat.le_antisymm (hp.2.2 q hq.1 hq.2.1) (hq.2.2 p hp.1 hp.2.1)

theorem LeastPrimeAbove.lt_two_mul {k p : ℕ} (hp : LeastPrimeAbove k p) (hk : 2 ≤ k) :
    p < 2 * k := by
  obtain ⟨q, hq, hkq, hqk⟩ := Nat.bertrand k (by omega)
  have hqstrict : q < 2 * k := by
    by_contra hn
    have heq : q = 2 * k := by omega
    have hdiv : k ∣ q := ⟨2, by omega⟩
    rcases hq.eq_one_or_self_of_dvd k hdiv with h1 | h1 <;> omega
  exact (hp.2.2 q hq hkq).trans_lt hqstrict

theorem smooth_of_natAbs_lt_leastPrime {k p : ℕ} (hp : LeastPrimeAbove k p)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs < p) : Smooth k z := by
  refine ⟨hz, ?_⟩
  intro q hq hqz
  by_contra hn
  have hpq := hp.2.2 q hq (Nat.lt_of_not_ge hn)
  have hqbound := Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hqz
  omega

end PerfectPowers
