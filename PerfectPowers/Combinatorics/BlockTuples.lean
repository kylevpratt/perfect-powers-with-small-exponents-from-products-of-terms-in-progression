module

public import PerfectPowers.Combinatorics.TupleExtraction
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Tuples in coefficient-dependent short blocks

Grouping a fiber with label `a` into blocks of length `a*L` allows all scales
to be counted at once. The number of extra blocks is controlled by a harmonic
sum. This avoids dyadic pigeonholing and its two size cases.
-/

@[expose] public section

namespace PerfectPowers

def coefficientBlocks (A : Finset ℕ) (k L : ℕ) : Finset (ℕ × ℕ) :=
  A.biUnion (fun a => ({a} : Finset ℕ).product (Finset.range (k / (a * L) + 1)))

theorem mem_coefficientBlocks {A : Finset ℕ} {k L a r : ℕ} :
    (a, r) ∈ coefficientBlocks A k L ↔ a ∈ A ∧ r ≤ k / (a * L) := by
  simp [coefficientBlocks]

theorem reciprocal_sum_le_log {A : Finset ℕ} {k : ℕ} (hA : A ⊆ Finset.Icc 1 k) :
    ∑ a ∈ A, (a : ℝ)⁻¹ ≤ 1 + Real.log (k : ℝ) := by
  have hsum : ∑ a ∈ A, (a : ℝ)⁻¹ ≤ ∑ a ∈ Finset.Icc 1 k, (a : ℝ)⁻¹ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hA (fun a _ _ => inv_nonneg.mpr (Nat.cast_nonneg a))
  have hH : ∑ a ∈ Finset.Icc 1 k, (a : ℝ)⁻¹ ≤ 1 + Real.log (k : ℝ) := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log k
  exact hsum.trans hH

theorem card_coefficientBlocks_le {A : Finset ℕ} {k L : ℕ} (hA : A ⊆ Finset.Icc 1 k) :
    ((coefficientBlocks A k L).card : ℝ) ≤
      (A.card : ℝ) + ((k : ℝ) / L) * (1 + Real.log (k : ℝ)) := by
  have hcard : (coefficientBlocks A k L).card ≤ ∑ a ∈ A, (k / (a * L) + 1) := by
    simpa [coefficientBlocks] using Finset.card_biUnion_le
      (s := A) (t := fun a => ({a} : Finset ℕ).product (Finset.range (k / (a * L) + 1)))
  have hcast : ((coefficientBlocks A k L).card : ℝ) ≤
      ∑ a ∈ A, (((k / (a * L) : ℕ) : ℝ) + 1) := by exact_mod_cast hcard
  have hfloor : ∑ a ∈ A, (((k / (a * L) : ℕ) : ℝ) + 1) ≤
      ∑ a ∈ A, (((k : ℝ) / L) * (a : ℝ)⁻¹ + 1) := by
    apply Finset.sum_le_sum
    intro a ha
    have h : ((k / (a * L) : ℕ) : ℝ) ≤ (k : ℝ) / (a * L : ℕ) := Nat.cast_div_le
    have hid : (k : ℝ) / (a * L : ℕ) = ((k : ℝ) / L) * (a : ℝ)⁻¹ := by
      simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hid] at h
    linarith
  have hsum : (∑ a ∈ A, (((k : ℝ) / L) * (a : ℝ)⁻¹ + 1)) =
      (A.card : ℝ) + ((k : ℝ) / L) * ∑ a ∈ A, (a : ℝ)⁻¹ := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [add_comm]
  rw [hsum] at hfloor
  have hlog := mul_le_mul_of_nonneg_left (reciprocal_sum_le_log hA)
    (div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg L) : (0 : ℝ) ≤ (k : ℝ) / L)
  linarith

theorem dist_lt_of_div_eq_div {i j q : ℕ} (hq : 0 < q) (heq : i / q = j / q) : Nat.dist i j < q := by
  have hi := Nat.div_add_mod i q
  have hj := Nat.div_add_mod j q
  have hmi := Nat.mod_lt i hq
  have hmj := Nat.mod_lt j hq
  rw [heq] at hi
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hji]
    omega

theorem exists_disjoint_short_block_tuples
    (J : Finset ℕ) (b : ℕ → ℕ) {k L m : ℕ}
    (hJ : J ⊆ Finset.range k) (hb : ∀ i ∈ J, 1 ≤ b i ∧ b i ≤ k) (hL : 0 < L)
    (hheavy : ∀ a ∈ J.image b, m + 1 ≤ (J.filter (fun i => b i = a)).card) :
    ∃ family : Finset (Finset ℕ),
      (∀ U ∈ family, U ⊆ J ∧ U.card = m + 1 ∧
        ∃ a : ℕ, 1 ≤ a ∧ a ≤ k ∧ (∀ i ∈ U, b i = a) ∧
          ∀ i ∈ U, ∀ j ∈ U, Nat.dist i j < a * L) ∧
      (∀ U ∈ family, ∀ V ∈ family, U ≠ V → Disjoint U V) ∧
      (J.card : ℝ) ≤ ((m : ℝ) + 1) ^ 2 * family.card +
        (m : ℝ) * ((m : ℝ) + 1) * ((k : ℝ) / L) * (1 + Real.log (k : ℝ)) := by
  classical
  let A := J.image b
  let F := coefficientBlocks A k L
  let g : ℕ → ℕ × ℕ := fun i => (b i, i / (b i * L))
  have hA : A ⊆ Finset.Icc 1 k := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_Icc.mpr (hb i hi)
  have hmap : ∀ i ∈ J, g i ∈ F := by
    intro i hi
    exact mem_coefficientBlocks.mpr ⟨Finset.mem_image_of_mem b hi,
      Nat.div_le_div_right (Finset.mem_range.mp (hJ hi)).le⟩
  obtain ⟨family, hprop, hdis, hcard⟩ := exists_disjoint_monochromatic_tuples J F g m hmap
  refine ⟨family, ?_, hdis, ?_⟩
  · intro U hU
    obtain ⟨hUJ, hUc, ar, har, hcolor⟩ := hprop U hU
    obtain ⟨haA, harbound⟩ := mem_coefficientBlocks.mp har
    obtain ⟨ha1, hak⟩ := Finset.mem_Icc.mp (hA haA)
    refine ⟨hUJ, hUc, ar.1, ha1, hak, ?_, ?_⟩
    · intro i hi
      exact congrArg Prod.fst (hcolor i hi)
    · intro i hi j hj
      have hiA : b i = ar.1 := congrArg Prod.fst (hcolor i hi)
      have hjA : b j = ar.1 := congrArg Prod.fst (hcolor j hj)
      have hiq : i / (ar.1 * L) = ar.2 := by simpa only [g, hiA] using congrArg Prod.snd (hcolor i hi)
      have hjq : j / (ar.1 * L) = ar.2 := by simpa only [g, hjA] using congrArg Prod.snd (hcolor j hj)
      exact dist_lt_of_div_eq_div (Nat.mul_pos ha1 hL) (hiq.trans hjq.symm)
  · have hcardA : (m + 1) * A.card ≤ J.card := by
      rw [Finset.card_eq_sum_card_fiberwise (s := J) (t := A) (f := b)
        (fun i hi => Finset.mem_image_of_mem b hi)]
      calc
        _ = ∑ _a ∈ A, (m + 1) := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum hheavy
    have hcardAR : ((m : ℝ) + 1) * A.card ≤ (J.card : ℝ) := by exact_mod_cast hcardA
    have hcardR : (J.card : ℝ) ≤ ((m : ℝ) + 1) * family.card + (m : ℝ) * F.card := by
      exact_mod_cast hcard
    have hF := card_coefficientBlocks_le hA (L := L)
    change ((F.card : ℕ) : ℝ) ≤ _ at hF
    have hFmul := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hmain := mul_le_mul_of_nonneg_left (hcardR.trans (by linarith :
      ((m : ℝ) + 1) * family.card + (m : ℝ) * F.card ≤
      ((m : ℝ) + 1) * family.card + (m : ℝ) *
        (A.card + ((k : ℝ) / L) * (1 + Real.log (k : ℝ)))))
      (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)
    have hAmul := mul_le_mul_of_nonneg_left hcardAR (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith

end PerfectPowers
