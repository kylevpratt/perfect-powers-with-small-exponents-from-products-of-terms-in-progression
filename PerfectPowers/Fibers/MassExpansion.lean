module

public import PerfectPowers.Fibers.InitialMass
public import PerfectPowers.Fibers.MassIncrement
import Mathlib.Tactic

/-!
# Mass expansion and many distinct small coefficients

These are the elementary deductions in Proposition 5.1 and Proposition 4.5,
with the heavy-fiber bound of Lemma 5.4 supplied as an explicit hypothesis.
That bound is a theorem still to prove, not an added external input.
-/

@[expose] public section

open Filter

namespace PerfectPowers

def Decomposition.representedSmall {k ell d : ℕ} {n : ℤ} {S : Finset ℕ}
    (D : Decomposition k ell n d S) (I : GoodIndices D) : Finset ℕ :=
  (D.smallIndices I).image (fun i => (D.a i).natAbs)

theorem eventually_light_mass_large_of_heavy_bound :
    ∀ᶠ k : ℕ in atTop,
      ∀ (ell d m : ℕ) (n : ℤ) (S : Finset ℕ) (D : Decomposition k ell n d S) (I : GoodIndices D),
        Nat.Coprime n.natAbs d → S ⊆ Finset.range k → Dense k S →
        4 ≤ m → (m : ℝ) ^ 2 ≤ k →
        ((D.heavyIndices I m).card : ℝ) ≤ (49 / 1000 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) →
        rho m * (k : ℝ) < (D.lightIndices I m).card := by
  filter_upwards [eventually_initial_small_mass, eventually_mass_increment,
    eventually_ge_atTop (2 : ℕ)] with k hinitial hincr hk
  intro ell d m n S D I hprimitive hS hdense hm hmk hheavy
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hratio : 0 < (k : ℝ) / Real.log (k : ℝ) := div_pos hkpos hLpos
  have hstart := hinitial ell d n S D I hprimitive hS hdense
  have hsplit : ((D.lightIndices I m).card : ℝ) + (D.heavyIndices I m).card =
      (D.smallIndices I).card := by exact_mod_cast D.light_heavy_card I m
  have hlight : (51 / 1000 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) ≤
      (D.lightIndices I m).card := by linarith
  by_contra hn
  have hle : ((D.lightIndices I m).card : ℝ) ≤ rho m * (k : ℝ) := le_of_not_gt hn
  let δ : ℝ := ((D.lightIndices I m).card : ℝ) / ((k : ℝ) / Real.log (k : ℝ))
  have hδlow : (1 / 1000 : ℝ) ≤ δ := by
    dsimp [δ]
    apply (le_div_iff₀ hratio).mpr
    nlinarith
  have hδupper : δ ≤ rho m * Real.log (k : ℝ) := by
    dsimp [δ]
    apply (div_le_iff₀ hratio).mpr
    convert hle using 1; field_simp [hLpos.ne']
  have hδmass : δ * ((k : ℝ) / Real.log (k : ℝ)) = (D.lightIndices I m).card := by
    dsimp [δ]
    field_simp
  have hinc := hincr ell d m n S D I hprimitive hS hdense hm hmk δ hδlow hδupper hδmass.le
  have hinc' : ((D.lightIndices I m).card : ℝ) +
      (1 / 10 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) ≤ (D.smallIndices I).card := by
    rw [add_mul, hδmass] at hinc
    exact hinc
  nlinarith

theorem Decomposition.light_card_le_mul_represented {k ell d : ℕ} {n : ℤ} {S : Finset ℕ}
    (D : Decomposition k ell n d S) (I : GoodIndices D) (m : ℕ) :
    (D.lightIndices I m).card ≤ m * (D.representedSmall I).card := by
  classical
  apply card_le_mul_of_fiber_bound (D.lightIndices I m) (D.representedSmall I)
    (fun i => (D.a i).natAbs) m
  · intro i hi
    exact Finset.mem_image.mpr ⟨i, D.lightIndices_subset_small I m hi, rfl⟩
  · intro a ha
    exact D.light_fiber_card_le I m a

theorem eventually_many_distinct_small_of_heavy_bound :
    ∀ᶠ k : ℕ in atTop,
      ∀ (ell d m : ℕ) (n : ℤ) (S : Finset ℕ) (D : Decomposition k ell n d S) (I : GoodIndices D),
        Nat.Coprime n.natAbs d → S ⊆ Finset.range k → Dense k S →
        4 ≤ m → (m : ℝ) ^ 2 ≤ k →
        ((D.heavyIndices I m).card : ℝ) ≤ (49 / 1000 : ℝ) * ((k : ℝ) / Real.log (k : ℝ)) →
        (k : ℝ) / (1000 * (m : ℝ) * Real.log (m : ℝ)) < (D.representedSmall I).card := by
  filter_upwards [eventually_light_mass_large_of_heavy_bound] with k hk
  intro ell d m n S D I hprimitive hS hdense hm hmk hheavy
  have hmass := hk ell d m n S D I hprimitive hS hdense hm hmk hheavy
  have hcard : ((D.lightIndices I m).card : ℝ) ≤ (m : ℝ) * (D.representedSmall I).card := by
    exact_mod_cast D.light_card_le_mul_represented I m
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogpos : 0 < Real.log (m : ℝ) := by linarith [log_ge_one_of_four_le hm]
  have hlt : rho m * (k : ℝ) < ((D.representedSmall I).card : ℝ) * (m : ℝ) := by
    nlinarith
  have h := (div_lt_iff₀ hmpos).mpr hlt
  convert h using 1
  unfold rho
  field_simp

end PerfectPowers
