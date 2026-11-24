module

public import PerfectPowers.Squares.OddFromLargePrime
public import PerfectPowers.Squares.OddLongStartPrime
public import PerfectPowers.Squares.OddShortStart
import Mathlib.Tactic

/-! # Lemma 3.6: a product of consecutive positive odd terms is not a square

The short-start case follows from Bertrand. Odd-prime deletion and elementary
Chebyshev estimates supply the large prime for every remaining start. The
squarefree-parts argument then proves nonsquareness, without extra hypotheses.

Proof difference from the paper: this elementary argument replaces its
appeal to Saradha for lengths at least three (and also covers length two).
See `PerfectPowers.PaperComparison` for the comparison and dependency map.
-/

public section

namespace PerfectPowers

theorem exists_large_prime_dvd_odd_progression
    (m k : ℕ) (hm : 0 < m) (hodd : Odd m) (hk : 2 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ i ∈ Finset.range k, (m + 2 * i) := by
  by_cases hshort : m ≤ 2 * k - 1
  · obtain ⟨p, hp, hkp, hmp, hpmax, _, hpodd⟩ :=
      exists_prime_in_odd_short_start_interval k m hk hm hodd hshort
    obtain ⟨s, hs⟩ := hodd
    obtain ⟨r, hr⟩ := hpodd
    have hi : r - s ∈ Finset.range k := by simp only [Finset.mem_range]; omega
    have heq : m + 2 * (r - s) = p := by omega
    exact ⟨p, hp, hkp, heq ▸ Finset.dvd_prod_of_mem (fun i => m + 2 * i) hi⟩
  · have hlong : 2 * k < m := by obtain ⟨s, hs⟩ := hodd; omega
    exact exists_large_prime_dvd_odd_progression_of_long_start m k hm hodd hk hlong

/-- Lemma 3.6, with its auxiliary prime-divisor fact fully discharged. -/
theorem oddProgressionNonsquare (m k : ℕ) (hm : 0 < m) (hodd : Odd m) (hk : 2 ≤ k) :
    ¬IsSquare (∏ i ∈ Finset.range k, (m + 2 * i)) := by
  obtain ⟨p, hp, hpk, hdiv⟩ := exists_large_prime_dvd_odd_progression m k hm hodd hk
  exact not_isSquare_odd_progression_of_large_prime hk hm hodd hp hpk hdiv

end PerfectPowers
