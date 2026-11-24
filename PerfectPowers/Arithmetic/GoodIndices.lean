module

public import PerfectPowers.Arithmetic.Decomposition
public import PerfectPowers.Arithmetic.Deletion
public import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic

/-! # Signed deletion and the retained index set used throughout the paper -/

@[expose] public section

namespace PerfectPowers

theorem gcd_natAbs_dvd_dist {b : ℕ → ℤ} {i j : ℕ}
    (h : (Int.gcd (b i) (b j) : ℤ) ∣ (j : ℤ) - (i : ℤ)) :
    Nat.gcd (b i).natAbs (b j).natAbs ∣ Nat.dist i j := by
  have hn := Int.ofNat_dvd_left.mp h
  by_cases hij : i ≤ j
  · simpa only [Int.gcd_def, Int.natAbs_natCast_sub_natCast_of_ge hij,
      Nat.dist_eq_sub_of_le hij] using hn
  · have hji := Nat.le_of_lt (Nat.lt_of_not_ge hij)
    simpa only [Int.gcd_def, Int.natAbs_natCast_sub_natCast_of_le hji,
      Nat.dist_eq_sub_of_le_right hji] using hn

/-- Signed form of Lemma 3.2, with divisibility by `(k - 1)!`. -/
theorem exists_smooth_factorial_deletion {k : ℕ} {S : Finset ℕ} {b : ℕ → ℤ}
    (hS : S ⊆ Finset.range k) (hb : ∀ i ∈ S, Smooth k (b i))
    (hgcd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (Int.gcd (b i) (b j) : ℤ) ∣ (j : ℤ) - (i : ℤ)) :
    ∃ I : Finset ℕ, I ⊆ S ∧ S.card ≤ I.card + Nat.primeCounting k ∧
      (∏ i ∈ I, (b i).natAbs) ∣ (k - 1).factorial := by
  apply exists_factorial_deletion hS
  · exact fun i hi => Int.natAbs_ne_zero.mpr (hb i hi).1
  · exact fun i hi p hp hdiv => (hb i hi).2 p hp hdiv
  · exact fun i hi j hj hne => gcd_natAbs_dvd_dist (hgcd i hi j hj hne)

/-- The only retained-set properties required by subsequent arguments. -/
structure GoodIndices {k ell : ℕ} {n : ℤ} {d : ℕ} {S : Finset ℕ}
    (D : Decomposition k ell n d S) where
  indices : Finset ℕ
  subset : indices ⊆ S
  card_bound : S.card ≤ indices.card + Nat.primeCounting k
  product_dvd : (∏ i ∈ indices, (D.a i).natAbs) ∣ (k - 1).factorial

noncomputable def Decomposition.goodIndices {k ell : ℕ} {n : ℤ} {d : ℕ} {S : Finset ℕ}
    (D : Decomposition k ell n d S) (hprimitive : Nat.Coprime n.natAbs d)
    (hS : S ⊆ Finset.range k) : GoodIndices D := by
  classical
  let hex := exists_smooth_factorial_deletion hS D.smooth
    (fun i hi j hj _ => D.gcd_a_dvd_index_sub hprimitive hi hj)
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2.1, (Classical.choose_spec hex).2.2⟩

theorem GoodIndices.product_le_factorial {k ell : ℕ} {n : ℤ} {d : ℕ} {S : Finset ℕ}
    {D : Decomposition k ell n d S} (I : GoodIndices D) :
    (∏ i ∈ I.indices, (D.a i).natAbs) ≤ k.factorial := by
  exact (Nat.le_of_dvd (Nat.factorial_pos _) I.product_dvd).trans
    (Nat.factorial_le (Nat.sub_le k 1))

end PerfectPowers
