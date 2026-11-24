module

import Challenge
import PerfectPowers.Main.Conditional

/- Specification compatibility checks, not a Solution or Comparator run.
None of these proofs uses a Challenge target or its placeholder proof.
Run after building Challenge:
  lake env lean scripts/CheckChallengeInterfaces.lean
-/

noncomputable section

namespace ChallengeInterfaceCheck

def toChallenge (C : PerfectPowers.AffinePlaneCurve) :
    PerfectPowersChallenge.AffinePlaneCurve :=
  ⟨C.equation, C.irreducible, C.geometricallyIrreducible⟩

def toInternal (C : PerfectPowersChallenge.AffinePlaneCurve) :
    PerfectPowers.AffinePlaneCurve :=
  ⟨C.equation, C.irreducible, C.geometricallyIrreducible⟩

theorem faltings_iff :
    PerfectPowersChallenge.AffineFaltingsStatement ↔
      PerfectPowers.External.AffineFaltingsStatement := by
  constructor
  · intro h C hns hg
    exact h (toChallenge C) hns hg
  · intro h C hns hg
    exact h (toInternal C) hns hg

theorem genus_iff :
    PerfectPowersChallenge.SuperellipticGenusStatement ↔
      PerfectPowers.External.SuperellipticGenusStatement := by
  constructor
  · intro h ell hell B C hB hC hpos
    exact h ell B C hell hB hC hpos
      (toChallenge (PerfectPowers.superellipticAffineCurve hell B C hB hC)) rfl
  · intro h ell B C hell hB hC hpos curve heq
    have hcurve : toInternal curve =
        PerfectPowers.superellipticAffineCurve hell B C hB hC := by
      cases curve with
      | mk F hQ hQbar =>
        change F = PerfectPowersChallenge.curvePolynomial ell B C at heq
        cases heq
        rfl
    change 2 ≤ (toInternal curve).geometricGenus
    rw [hcurve]
    exact h ell hell B C hB hC hpos

theorem remond_iff :
    PerfectPowersChallenge.RemondStatement ↔ PerfectPowers.External.RemondStatement :=
  Iff.rfl

theorem primeAP_iff :
    PerfectPowersChallenge.PrimeAPStatement ↔ PerfectPowers.External.PrimeAPStatement :=
  Iff.rfl

theorem exponent_iff (k ell : ℕ) (hk : 3 ≤ k) :
    PerfectPowersChallenge.SmallExponent k ell ↔ PerfectPowers.SmallExponent k ell := by
  have hkReal : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog : 1 ≤ Real.log (k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (k : ℝ))]
    exact Real.exp_one_lt_d9.le.trans (by norm_num; linarith)
  have hT : 0 ≤ Real.log (Real.log (k : ℝ)) := Real.log_nonneg hlog
  constructor
  · intro h
    exact (PerfectPowers.smallExponent_iff_paper_range hk h.2.1 hT).mpr h.2.2
  · intro h
    exact ⟨h.1, h.2.1,
      (PerfectPowers.smallExponent_iff_paper_range hk h.2.1 hT).mp h⟩

#print axioms faltings_iff
#print axioms genus_iff
#print axioms remond_iff
#print axioms primeAP_iff
#print axioms exponent_iff

end ChallengeInterfaceCheck
