module

public import PerfectPowers.Main.SmallTrivialParts
public import PerfectPowers.Main.SmoothnessReduction
import Mathlib.Tactic

/-!
# Smoothness and size conclusions of Theorem 1.5

`Main.StepRestriction` supplies the stronger-density conclusion `d = 1 or
d = 2` using prime-AP. The family-finiteness premise here is supplied by
`Curves.AffineFiniteness` in the final theorem.
-/

public section

open Filter

namespace PerfectPowers

theorem eventually_smooth_bounds_of_finite (hRemond : External.RemondStatement) :
    ∀ᶠ k : ℕ in atTop, ∀ (ell : ℕ) (n : ℤ) (d : ℕ) (b y : ℤ) (S : Finset ℕ),
      SmallExponent k ell → Dense k S → Solution k ell n d b y S →
      CurveFamilyFinite ell (branchCount ell) →
      Smooth k (progressionProduct n d S) ∧
        (d : ℝ) ≤ 3 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) ∧ n.natAbs ≤ k * (d + 1) := by
  filter_upwards [eventually_many_trivial_parts_of_finite hRemond,
    eventually_smooth_of_many_small_trivial_parts] with k htriv hboot
  intro ell n d b y S hell hdense hsol hfinite
  let D := hsol.decomposition (by have := hell.2.1; omega)
  let I := D.goodIndices hsol.coprime hsol.index_subset
  have hmass := htriv ell d n S D I hell hsol.coprime hsol.d_pos hsol.index_subset hdense hfinite
  exact hboot ell d n S I.indices D hell.2.1 hsol.index_subset I.subset hmass

end PerfectPowers
