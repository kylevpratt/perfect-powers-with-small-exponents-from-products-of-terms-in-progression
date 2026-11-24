module

public import PerfectPowers.Fibers.HeavyMass
public import PerfectPowers.Fibers.NontrivialCoefficients
public import PerfectPowers.Curves.CoefficientTupleFamily
public import PerfectPowers.Combinatorics.UniformTuples
public import PerfectPowers.Analytic.TupleCountGrowth
import Mathlib.Tactic

/-!
# Proposition 3.5, with the geometric finiteness bridge explicit

The elementary tuple replacement, its stronger threshold, the changed constant
`5`, the curve height/count bounds, and distinctness of points are all used
here as proved lemmas. No unspecified analytic input is absorbed into Remond.
-/

public section

open Filter

namespace PerfectPowers

theorem eventually_many_trivial_parts_of_finite (hRemond : External.RemondStatement) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (ell d : ℕ) (n : ℤ) (S : Finset ℕ) (D : Decomposition k ell n d S) (I : GoodIndices D),
        SmallExponent k ell → Nat.Coprime n.natAbs d → 0 < d → S ⊆ Finset.range k → Dense k S →
        CurveFamilyFinite ell (branchCount ell) →
        (k : ℝ) / (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) < (smallTrivialIndices D I.indices).card := by
  classical
  filter_upwards [eventually_many_distinct_small_of_finite hRemond,
    eventually_trivial_count_le_tuple_density, eventually_uniform_common_divisor_tuples,
    eventually_uniform_curve_family_budget, eventually_tupleSide_log_bound,
    eventually_tuple_count_gt_quarter_power] with k hmany htriv htuples hbudget hside hgrowth
  intro ell d n S D I hell hprimitive hd hS hdense hfinite
  let m := branchCount ell
  let c := tupleDensity m
  have hm4 : 4 ≤ m := (branchCount_properties hell.2.1).1
  have hm2 : 2 ≤ m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hc : 0 < c := tupleDensity_pos hm2
  have hM := hmany ell d n S D I hell hprimitive hd hS hdense hfinite
  have hid : (k : ℝ) / (1000 * (m : ℝ) * Real.log (m : ℝ)) = 2 * c * (k : ℝ) := by
    dsimp [c]
    unfold tupleDensity
    field_simp
    ring
  change (k : ℝ) / (1000 * (m : ℝ) * Real.log (m : ℝ)) < (D.representedSmall I).card at hM
  rw [hid] at hM
  by_contra hnot
  have hG : ((smallTrivialIndices D I.indices).card : ℝ) ≤ c * (k : ℝ) :=
    (le_of_not_gt hnot).trans (htriv ell hell)
  have hcard : ((D.representedSmall I).card : ℝ) ≤ (D.nontrivialCoefficients I).card +
      (smallTrivialIndices D I.indices).card := by exact_mod_cast D.represented_card_le_nontrivial_add_trivial I
  have hA : c * (k : ℝ) ≤ (D.nontrivialCoefficients I).card := by linarith
  obtain ⟨r, hr⟩ := D.exists_nontrivial_representatives I
  obtain ⟨family, hprop, hdis, hcount⟩ := htuples ell hell (D.nontrivialCoefficients I)
    (D.nontrivialCoefficients_subset I) hA
  have hprop' : ∀ U ∈ family, U ⊆ D.nontrivialCoefficients I ∧ U.card = m + 1 ∧
      ∃ f : ℕ, tupleEta m * (k : ℝ) < (f : ℝ) ∧ ∀ a ∈ U, f ∣ a := by
    simpa only [m, tupleEta] using hprop
  have hupper := coefficient_tuple_family_card_bound hRemond D (by have := hell.2.1; omega)
    (branchCount_properties hell.2.1).2.1 (branchCount_properties hell.2.1).2.2.1 hm2
    hprimitive hd hS (D.nontrivialCoefficients_subset I) r hr family hprop' hdis hfinite
  have hbudget' := hbudget ell hell (tupleSide m) (tupleSide_pos hm2) (hside ell hell)
  have htotal := hupper.trans hbudget'
  have hlarge := (hgrowth ell hell).trans_le hcount
  linarith

end PerfectPowers
