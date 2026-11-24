module

public import PerfectPowers.Arithmetic.Bootstrap
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Bounding the step from many small terms -/

@[expose] public section

namespace PerfectPowers

noncomputable def smallTrivialIndices {k ell d : ℕ} {n : ℤ} {S : Finset ℕ}
    (D : Decomposition k ell n d S) (I : Finset ℕ) : Finset ℕ :=
  I.filter (fun i => (D.a i).natAbs ≤ k ∧ D.x i = 1)

theorem exists_card_separated_pair (A : Finset ℕ) (hA : A.Nonempty) :
    ∃ i ∈ A, ∃ j ∈ A, i ≤ j ∧ A.card ≤ j - i + 1 := by
  let i := A.min' hA
  let j := A.max' hA
  have hi : i ∈ A := A.min'_mem hA
  have hj : j ∈ A := A.max'_mem hA
  have hij : i ≤ j := A.min'_le j hj
  refine ⟨i, hi, j, hj, hij, ?_⟩
  have hsub : A ⊆ Finset.Icc i j := by
    intro a ha
    exact Finset.mem_Icc.mpr ⟨A.min'_le a ha, A.le_max' a ha⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  omega

theorem step_gap_bound_of_small_terms {k d i j : ℕ} {n : ℤ} (hij : i ≤ j)
    (hi : (term n d i).natAbs ≤ k) (hj : (term n d j).natAbs ≤ k) :
    (j - i) * d ≤ 2 * k := by
  have hiZ : |term n d i| ≤ (k : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hi
  have hjZ : |term n d j| ≤ (k : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hj
  obtain ⟨hilo, hihi⟩ := abs_le.mp hiZ
  obtain ⟨hjlo, hjhi⟩ := abs_le.mp hjZ
  have hdiff := term_sub_term n d i j
  have hZ : ((j : ℤ) - (i : ℤ)) * (d : ℤ) ≤ 2 * (k : ℤ) := by linarith
  rw [← Nat.cast_sub hij] at hZ
  exact_mod_cast hZ

theorem bootstrap_of_many_small_terms {k ell d : ℕ} {n : ℤ} {S I : Finset ℕ}
    (D : Decomposition k ell n d S) (hell : 2 ≤ ell)
    (hS : S ⊆ Finset.range k) (hI : I ⊆ S) {L : ℝ} (hL : 0 < L)
    (hLk : 6 * L ≤ (k : ℝ))
    (hmany : (k : ℝ) / L < (smallTrivialIndices D I).card) :
    Smooth k (progressionProduct n d S) ∧ (d : ℝ) ≤ 3 * L ∧ n.natAbs ≤ k * (d + 1) := by
  classical
  let G := smallTrivialIndices D I
  have hG : G.Nonempty := Finset.card_pos.mp (by
    have hkL : 0 ≤ (k : ℝ) / L := div_nonneg (Nat.cast_nonneg k) hL.le
    have hcard : (0 : ℝ) < G.card := lt_of_le_of_lt hkL hmany
    exact_mod_cast hcard)
  obtain ⟨i, hi, j, hj, hij, hcard⟩ := exists_card_separated_pair G hG
  have hi' : i ∈ I ∧ (D.a i).natAbs ≤ k ∧ D.x i = 1 := Finset.mem_filter.mp hi
  have hj' : j ∈ I ∧ (D.a j).natAbs ≤ k ∧ D.x j = 1 := Finset.mem_filter.mp hj
  have hti : (term n d i).natAbs ≤ k := by rw [D.factor i (hI hi'.1), hi'.2.2]; simpa using hi'.2.1
  have htj : (term n d j).natAbs ≤ k := by rw [D.factor j (hI hj'.1), hj'.2.2]; simpa using hj'.2.1
  have hgap := step_gap_bound_of_small_terms hij hti htj
  have hgapR : ((j - i : ℕ) : ℝ) * (d : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hgap
  have hcardR : ((G.card : ℕ) : ℝ) ≤ (j - i : ℕ) + 1 := by exact_mod_cast hcard
  have hmany' : (k : ℝ) < (G.card : ℝ) * L := (div_lt_iff₀ hL).mp hmany
  have hsep : 2 * (k : ℝ) ≤ 3 * L * ((j - i : ℕ) : ℝ) := by nlinarith
  have hsepD := mul_le_mul_of_nonneg_right hsep (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hgapL := mul_le_mul_of_nonneg_left hgapR (by positivity : (0 : ℝ) ≤ 3 * L)
  have hkpos : (0 : ℝ) < k := by linarith
  have hdL : (d : ℝ) ≤ 3 * L := by nlinarith
  have hstepR : (k : ℝ) * (2 * (d : ℝ) + 1) < ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hstep : k * (2 * d + 1) < (k + 1) ^ 2 := by exact_mod_cast hstepR
  exact ⟨D.product_smooth_of_step_bound hell hS (hI hi'.1) hi'.2.1 hi'.2.2 hstep,
    hdL, D.start_bound_of_small_trivial_term hS (hI hi'.1) hi'.2.1 hi'.2.2⟩

end PerfectPowers
