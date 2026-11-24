module

public import PerfectPowers.Fibers.HeavyCurveBound
public import PerfectPowers.Fibers.MassExpansion
public import PerfectPowers.Analytic.HeavyBudget
import Mathlib.Tactic

/-!
# Heavy-fiber mass and distinct coefficients, conditional on curve finiteness

The heavy-fiber bound is stronger than Lemma 5.4 and does not require a bound
on the number of trivial power parts. Affine finiteness is kept as an explicit
premise here and is supplied by `Curves.AffineFiniteness` in the final theorem.

Proof difference from the paper: coefficient-dependent blocks and a harmonic
sum replace dyadic pigeonholing and its two size cases. Numerator supports
contain a nontrivial part even when the whole fiber has trivial parts, so
the good/bad-fiber removal is unnecessary. The result is `0.02*k/log k`,
implying the draft's `0.049*k/log k`. See `PerfectPowers.PaperComparison`.
-/

public section

open Filter

namespace PerfectPowers

theorem eventually_heavy_mass_le_of_finite (hRemond : External.RemondStatement) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (ell d : ℕ) (n : ℤ) (S : Finset ℕ) (D : Decomposition k ell n d S) (I : GoodIndices D),
        SmallExponent k ell → Nat.Coprime n.natAbs d → 0 < d → S ⊆ Finset.range k →
        CurveFamilyFinite ell (branchCount ell) →
        ((D.heavyIndices I (branchCount ell)).card : ℝ) ≤
          (1 / 50 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) := by
  filter_upwards [eventually_heavy_counting_budget] with k hbudget
  intro ell d n S D I hell hprimitive hd hS hfinite
  have hm := branchCount_properties hell.2.1
  have hL := (logBlockSize_properties hell).1
  exact (D.heavy_mass_le_curve_bound hRemond I (by have := hell.2.1; omega)
    hm.2.1 hm.2.2.1 (by omega) hprimitive hd hS hL hfinite).trans (hbudget ell hell)

theorem eventually_many_distinct_small_of_finite (hRemond : External.RemondStatement) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (ell d : ℕ) (n : ℤ) (S : Finset ℕ) (D : Decomposition k ell n d S) (I : GoodIndices D),
        SmallExponent k ell → Nat.Coprime n.natAbs d → 0 < d → S ⊆ Finset.range k → Dense k S →
        CurveFamilyFinite ell (branchCount ell) →
        (k : ℝ) / (1000 * (branchCount ell : ℝ) * Real.log (branchCount ell : ℝ)) <
          (D.representedSmall I).card := by
  filter_upwards [eventually_heavy_mass_le_of_finite hRemond,
    eventually_many_distinct_small_of_heavy_bound, eventually_branchCount_sq_le] with k hheavy hmany hmrange
  intro ell d n S D I hell hprimitive hd hS hdense hfinite
  have hH := hheavy ell d n S D I hell hprimitive hd hS hfinite
  have hratio : 0 ≤ (k : ℝ) / Real.log (k : ℝ) := div_nonneg (Nat.cast_nonneg k) hell.log_pos.le
  have hH' : ((D.heavyIndices I (branchCount ell)).card : ℝ) ≤
      (49 / 1000 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) := by nlinarith
  exact hmany ell d (branchCount ell) n S D I hprimitive hS hdense
    (branchCount_properties hell.2.1).1 (hmrange ell hell) hH'

end PerfectPowers
