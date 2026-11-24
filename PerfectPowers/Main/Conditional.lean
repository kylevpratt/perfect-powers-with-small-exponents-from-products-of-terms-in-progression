module

public import PerfectPowers.Main.SmoothBounds
public import PerfectPowers.Main.StepRestriction
public import PerfectPowers.Main.SquareClassification
public import PerfectPowers.Curves.AffineFiniteness
import Mathlib.Tactic

/-!
# The main proof chain from the four agreed external inputs

The final entry point uses affine Faltings, the superelliptic genus lower
bound, Remond, and Lemma 3.3. Affine finiteness and Lemma 3.6 are supplied by
their internal proofs. The modular finiteness premise is kept separate from
the final four-input theorem. No mathematical axiom is declared here.
-/

public section

open Filter

namespace PerfectPowers

theorem eventually_theorem15_of_finite (hRemond : External.RemondStatement)
    (hAP : External.PrimeAPStatement)
    (hfinite : ∀ ell : ℕ, 2 ≤ ell → CurveFamilyFinite ell (branchCount ell)) :
    ∀ᶠ k : ℕ in atTop, Theorem15At k := by
  filter_upwards [eventually_smooth_bounds_of_finite hRemond,
    eventually_small_step_of_primeAP hAP] with k hbounds hstep
  intro ell n d b y S hell hdense hsol
  obtain ⟨hsmooth, hd, hn⟩ := hbounds ell n d b y S hell hdense hsol (hfinite ell hell.2.1)
  exact ⟨hsmooth, hd, hn, fun hvery =>
    hstep n d S hsol.d_pos hsol.coprime hsol.index_subset hsmooth hvery hd hn⟩

/-- The modular main-result deduction with affine finiteness supplied. -/
theorem mainResults_of_finite (hRemond : External.RemondStatement)
    (hAP : External.PrimeAPStatement)
    (hfinite : ∀ ell : ℕ, 2 ≤ ell → CurveFamilyFinite ell (branchCount ell)) : MainResults := by
  exact mainResults_of_eventually_theorem15 (eventually_theorem15_of_finite hRemond hAP hfinite)

/-- The main results from exactly the four agreed external statements, using
the accepted affine formulation of Faltings. No additional finiteness or
odd-progression hypothesis remains. -/
theorem mainResults_of_external_inputs
    (hFaltings : External.AffineFaltingsStatement)
    (hGenus : External.SuperellipticGenusStatement)
    (hRemond : External.RemondStatement) (hAP : External.PrimeAPStatement) : MainResults := by
  exact mainResults_of_finite hRemond hAP (fun _ hell => curve_family_finite hFaltings hGenus hell)

end PerfectPowers
