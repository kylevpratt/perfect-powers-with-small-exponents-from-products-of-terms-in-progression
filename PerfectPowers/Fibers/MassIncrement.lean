module

public import PerfectPowers.Fibers.LightMass
public import PerfectPowers.Analytic.SmallMassEntropy
public import PerfectPowers.Analytic.MassThreshold
public import PerfectPowers.Analytic.FactorialDeficit
public import PerfectPowers.Analytic.PrimeCounting
import Mathlib.Tactic

/-!
# The mass increment (Lemma 5.5)

The multiplicity estimate gives a logarithmic product bound directly, without
floor errors. The entropy loss is bounded by `0.01`, and the factorial deficit
uses `1.35`; together with the `1.05` PNT bound and the `0.2` density loss,
this gives exactly the draft's `0.1` increment. All parameters are quantified
inside the eventual assertion, so the threshold is uniform.

Proof difference from the paper: `N! <= m^N * product` replaces the sorted
floor-factorial estimate, and explicit log-factorial inequalities replace
Stirling error terms. The draft uses entropy `0.007` and a different deficit
calculation; the constants above preserve its conclusion. See
`PerfectPowers.PaperComparison`.
-/

public section

open Filter

namespace PerfectPowers

theorem Decomposition.small_product_log_lower_of_light_mass
    {k ell d m : ℕ} {n : ℤ} {S : Finset ℕ}
    (D : Decomposition k ell n d S) (I : GoodIndices D)
    (hk : 2 ≤ k) (hm : 4 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (hδρ : δ ≤ rho m * Real.log (k : ℝ))
    (hmN : (m : ℝ) ≤ δ * ((k : ℝ) / Real.log (k : ℝ)))
    (hmass : δ * ((k : ℝ) / Real.log (k : ℝ)) ≤ (D.lightIndices I m).card) :
    (δ - 1 / 100) * (k : ℝ) ≤
      Real.log ((∏ i ∈ D.smallIndices I, (D.a i).natAbs : ℕ) : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let y : ℝ := δ / Real.log (k : ℝ)
  have hy : 0 < y := div_pos hδ hLpos
  have hyρ : y ≤ rho m := (div_le_iff₀ hLpos).mpr hδρ
  have hentropy := mul_le_mul_of_nonneg_right (small_mass_entropy_le hm hy hyρ) hkpos.le
  have hbound := D.light_mass_log_bound I (by omega : 0 < m) hmN hmass
  have hNrepr : δ * ((k : ℝ) / Real.log (k : ℝ)) = y * (k : ℝ) := by dsimp [y]; ring
  have hlogid : Real.log ((y * (k : ℝ)) / (m : ℝ)) =
      Real.log (k : ℝ) - Real.log ((m : ℝ) / y) := by
    rw [Real.log_div (mul_ne_zero hy.ne' hkpos.ne') hmpos.ne',
      Real.log_mul hy.ne' hkpos.ne', Real.log_div hmpos.ne' hy.ne']
    ring
  rw [hNrepr, hlogid] at hbound
  have hyδ : y * Real.log (k : ℝ) = δ := by dsimp [y]; field_simp
  have hid : (y * (k : ℝ)) * (Real.log (k : ℝ) - Real.log ((m : ℝ) / y)) - y * (k : ℝ) =
      δ * (k : ℝ) - (y * (Real.log ((m : ℝ) / y) + 1)) * (k : ℝ) := by
    rw [← hyδ]
    ring
  rw [hid] at hbound
  nlinarith

theorem eventually_mass_increment :
    ∀ᶠ k : ℕ in atTop,
      ∀ (ell d m : ℕ) (n : ℤ) (S : Finset ℕ) (D : Decomposition k ell n d S) (I : GoodIndices D),
        Nat.Coprime n.natAbs d → S ⊆ Finset.range k → Dense k S →
        4 ≤ m → (m : ℝ) ^ 2 ≤ k → ∀ δ : ℝ,
        (1 / 1000 : ℝ) ≤ δ → δ ≤ rho m * Real.log (k : ℝ) →
        δ * ((k : ℝ) / Real.log (k : ℝ)) ≤ (D.lightIndices I m).card →
        (δ + 1 / 10) * ((k : ℝ) / Real.log (k : ℝ)) ≤ (D.smallIndices I).card := by
  filter_upwards [eventually_weighted_factorial_deficit, eventually_mass_exceeds_multiplicity,
    eventually_primeCounting_le_twenty_one_twentieths, eventually_ge_atTop (2 : ℕ)]
    with k hdef hthreshold hpi hk
  intro ell d m n S D I hprimitive hS hdense hm hmk δ hδlow hδupper hmass
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLpos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hδpos : 0 < δ := by linarith
  have hmN := hthreshold m δ hmk hδlow
  have hlogP := D.small_product_log_lower_of_light_mass I hk hm hδpos hδupper hmN hmass
  have hP : 0 < ∏ i ∈ D.smallIndices I, (D.a i).natAbs := by
    apply Finset.prod_pos
    intro i hi
    exact Int.natAbs_pos.mpr (D.smooth i (I.subset (Finset.mem_filter.mp hi).1)).1
  have hδbound : δ ≤ Real.log (k : ℝ) / 1000 := by
    have h := mul_le_mul_of_nonneg_right (rho_le_one_thousandth hm) hLpos.le
    linarith
  have hR := hdef (D.largeIndices I).card (∏ i ∈ D.smallIndices I, (D.a i).natAbs) δ hP
    (D.small_product_weighted_factorial_le_square I hprimitive hS) hδpos.le hδbound hlogP
  have hcardNat : S.card ≤ (D.smallIndices I).card + (D.largeIndices I).card + Nat.primeCounting k := by
    rw [D.small_large_card]
    exact I.card_bound
  have hcard : (S.card : ℝ) ≤ (D.smallIndices I).card + (D.largeIndices I).card +
      (Nat.primeCounting k : ℝ) := by exact_mod_cast hcardNat
  change (k : ℝ) - (1 / 5 : ℝ) * (k : ℝ) / Real.log (k : ℝ) ≤ (S.card : ℝ) at hdense
  rw [mul_div_assoc] at hdense
  nlinarith

end PerfectPowers
