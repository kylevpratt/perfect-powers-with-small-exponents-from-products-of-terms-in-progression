module

public import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
# The large prime for short odd progressions

Bertrand handles `m ≤ 2k - 1`. `OddNonsquare` combines this interval
with the long-start prime theorem and the shared squarefree-parts argument.
-/

public section

namespace PerfectPowers

theorem exists_prime_in_odd_short_start_interval (k m : ℕ)
    (hk : 2 ≤ k) (hm : 0 < m) (hodd : Odd m) (hshort : m ≤ 2 * k - 1) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ m ≤ p ∧ p < m + 2 * k - 1 ∧
      m + 2 * k - 1 ≤ 2 * p ∧ Odd p := by
  obtain ⟨s, hs⟩ := hodd
  let t := s + k
  have ht : t ≠ 0 := by dsimp [t]; omega
  obtain ⟨p, hp, htp, hpt⟩ := Nat.bertrand t ht
  have hkp : k < p := by dsimp [t] at htp; omega
  have hpodd := hp.odd_of_ne_two (by omega)
  have hmlow : m ≤ t := by dsimp [t]; omega
  have hsum : m + 2 * k - 1 = 2 * t := by dsimp [t]; omega
  have hpless : p < 2 * t := by
    have hne : p ≠ 2 * t := by
      obtain ⟨r, hr⟩ := hpodd
      omega
    omega
  exact ⟨p, hp, hkp, by omega, by omega, by omega, hpodd⟩

end PerfectPowers
