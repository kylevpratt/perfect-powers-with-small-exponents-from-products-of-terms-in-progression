module

public import PerfectPowers.Combinatorics.ElementaryTuples
public import PerfectPowers.Analytic.TupleThreshold
import Mathlib.Tactic

/-! # The common-divisor tuples uniformly in the allowed exponent range -/

public section

open Filter

namespace PerfectPowers

theorem eventually_uniform_common_divisor_tuples :
    ∀ᶠ k : ℕ in atTop, ∀ ell : ℕ, SmallExponent k ell →
      ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 k →
        tupleDensity (branchCount ell) * (k : ℝ) ≤ B.card →
        ∃ family : Finset (Finset ℕ),
          (∀ U ∈ family, U ⊆ B ∧ U.card = branchCount ell + 1 ∧
            ∃ f : ℕ, tupleDensity (branchCount ell) / 3 *
              Real.exp (-5 * tupleScale (branchCount ell)) * (k : ℝ) < (f : ℝ) ∧
              ∀ b ∈ U, f ∣ b) ∧
          (∀ U ∈ family, ∀ V ∈ family, U ≠ V → Disjoint U V) ∧
          tupleDensity (branchCount ell) * (k : ℝ) /
            (6 * ((branchCount ell : ℝ) + 1)) ≤ family.card := by
  filter_upwards [eventually_uniform_tuple_size_condition] with k hk
  intro ell hell B hB hdense
  have hm : 2 ≤ branchCount ell := by have := (branchCount_properties hell.2.1).1; omega
  have hsize : 12 * ((branchCount ell : ℝ) / tupleDensity (branchCount ell)) *
      (2 : ℝ) ^ (Real.exp (4 * ((branchCount ell : ℝ) / tupleDensity (branchCount ell)))) ≤ k := by
    simpa only [tupleDensity_scale] using hk ell hell
  simpa only [tupleDensity_scale] using exists_elementary_common_divisor_tuples
    (by omega : 1 ≤ branchCount ell) (tupleDensity_pos hm) (tupleDensity_le_one hm)
    hsize B hB hdense

end PerfectPowers
