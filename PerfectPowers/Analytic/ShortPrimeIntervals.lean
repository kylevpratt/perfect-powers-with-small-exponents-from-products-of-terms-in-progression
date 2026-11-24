module

public import PerfectPowers.Analytic.PrimeCounting
import Mathlib.Tactic

/-! # A uniform short-interval prime consequence of mathlib's proved PNT -/

public section

open Filter

namespace PerfectPowers

theorem eventually_uniform_quarter_prime_interval :
    ∀ᶠ k : ℕ in atTop, ∀ x : ℝ, (k : ℝ) ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ (5 / 4 : ℝ) * x := by
  have h := Nat.eventually_exists_prime_mem_Ioc (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp h
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop X0)] with k hk
  intro x hx
  obtain ⟨p, hp, hl, hu⟩ := hX0 x (hk.trans hx)
  refine ⟨p, hp, hl, ?_⟩
  norm_num at hu ⊢
  exact hu

end PerfectPowers
