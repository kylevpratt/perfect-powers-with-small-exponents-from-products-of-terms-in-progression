module

public import PerfectPowers.External.AffineFaltings
public import PerfectPowers.External.Genus
public import PerfectPowers.Curves.Counting

/-! # Affine finiteness from the two agreed geometric inputs -/

public section

namespace PerfectPowers

theorem curve_family_finite (hFaltings : External.AffineFaltingsStatement)
    (hGenus : External.SuperellipticGenusStatement)
    {ell : ℕ} (hell : 2 ≤ ell) : CurveFamilyFinite ell (branchCount ell) := by
  intro B C hB hC hpos
  exact hFaltings (superellipticAffineCurve hell B C hB hC)
    (superellipticAffineCurve_nonsingular hell B C hB hC)
    (hGenus ell hell B C hB hC hpos)

end PerfectPowers
