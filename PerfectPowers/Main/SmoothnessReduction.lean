module

public import PerfectPowers.Arithmetic.ManySmallTerms
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The elementary part of Theorem 1.5, conditional on Proposition 3.5

The cardinality hypothesis below is exactly the conclusion still to be proved
in Proposition 3.5. The threshold is absolute and independent of the exponent.
The final `d = 1 or d = 2` conclusion needs the separate prime-AP argument.
-/

public section

open Filter

namespace PerfectPowers

theorem eventually_smooth_of_many_small_trivial_parts :
    ∀ᶠ k : ℕ in atTop, ∀ (ell d : ℕ) (n : ℤ) (S I : Finset ℕ)
      (D : Decomposition k ell n d S), 2 ≤ ell →
      S ⊆ Finset.range k → I ⊆ S →
      (k : ℝ) / (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) < (smallTrivialIndices D I).card →
      Smooth k (progressionProduct n d S) ∧
        (d : ℝ) ≤ 3 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) ∧ n.natAbs ≤ k * (d + 1) := by
  have hlim : Tendsto
      (fun k : ℕ => (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) / (k : ℝ)) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa only [Real.rpow_one, Function.comp_def] using h
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 6),
    eventually_ge_atTop (2 : ℕ)] with k hsmall hk
  intro ell d n S I D hell hS hI hmany
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hL : 0 < (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hLk : 6 * (Real.log (k : ℝ)) ^ (3 / 2 : ℝ) ≤ (k : ℝ) := by
    have h := (div_lt_iff₀ hkpos).mp hsmall
    linarith
  exact bootstrap_of_many_small_terms D hell hS hI hL hLk hmany

end PerfectPowers
