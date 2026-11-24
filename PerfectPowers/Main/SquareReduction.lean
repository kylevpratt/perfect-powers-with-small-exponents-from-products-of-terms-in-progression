module

public import PerfectPowers.Main.FullClassification
public import PerfectPowers.Main.StepOneObstruction
public import PerfectPowers.Arithmetic.SmallStepExponent
import Mathlib.Tactic

/-! # The exponent and step reductions in Theorem 1.2 -/

public section

namespace PerfectPowers

theorem square_reduction_of_theorem14 {k ell d : ℕ} {n y : ℤ} (hk : 21 ≤ k)
    (h14 : Theorem14At k) (hell : SmallExponent k ell)
    (h : Solution k ell n d 1 y (Finset.range k)) :
    ell = 2 ∧ d = 2 ∧ Odd n ∧ -2 * ((k : ℤ) - 1) < n ∧ n < 0 := by
  obtain ⟨hsmooth, hstep, hn, p, hp, hpair⟩ := h14 ell n d 1 y hell h
  have hd2 : d ≤ 2 := by omega
  have hn3 : n.natAbs ≤ 3 * k := by nlinarith
  have hell2 := h.exponent_eq_two_of_small_step hk hell.2.1 hstep hn3
  have hdTwo : d = 2 := by
    rcases hstep with hdOne | hdTwo
    · subst d
      exact (even_exponent_step_one_impossible (by omega) hp hpair h
        (by simpa only [hell2] using (show Even (2 : ℕ) by decide))).elim
    · exact hdTwo
  have hpk := hp.lt_two_mul (by omega : 2 ≤ k)
  subst d
  rcases hpair with ⟨hbad, _⟩ | ⟨hbad, _⟩ | ⟨_, hlow, hupp, hodd⟩
  · omega
  · omega
  · exact ⟨hell2, rfl, hodd, by omega, by omega⟩

end PerfectPowers
