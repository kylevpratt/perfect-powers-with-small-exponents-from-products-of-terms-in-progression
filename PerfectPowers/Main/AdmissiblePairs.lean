module

public import PerfectPowers.Basic.LeastPrime
public import PerfectPowers.Basic.Products
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

/-!
# The easy direction of the full-product classification

Every pair in the three ranges (1.4) gives a solution with `y = 1` and the
product itself as `b`, for every exponent. The converse is a later main result.
-/

public section

namespace PerfectPowers

theorem AdmissiblePair.step_pos {k p d : ℕ} {n : ℤ} (h : AdmissiblePair k p n d) :
    0 < d := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num

theorem AdmissiblePair.coprime {k p d : ℕ} {n : ℤ} (h : AdmissiblePair k p n d) :
    Nat.Coprime n.natAbs d := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _, _, hodd⟩
  · simp
  · simp
  · exact Nat.coprime_two_right.mpr hodd.natAbs

theorem AdmissiblePair.term_nonzero_and_natAbs_lt {k p d i : ℕ} {n : ℤ}
    (h : AdmissiblePair k p n d) (hi : i < k) :
    term n d i ≠ 0 ∧ (term n d i).natAbs < p := by
  have hbounds : term n d i ≠ 0 ∧ -(p : ℤ) < term n d i ∧ term n d i < (p : ℤ) := by
    rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2, hodd⟩
    · simp only [term, Nat.cast_one, mul_one]
      omega
    · simp only [term, Nat.cast_one, mul_one]
      omega
    · obtain ⟨t, ht⟩ := hodd
      simp only [term, Nat.cast_ofNat]
      omega
  refine ⟨hbounds.1, ?_⟩
  have hcast : ((term n d i).natAbs : ℤ) < (p : ℤ) := by
    rw [Int.natCast_natAbs]
    exact abs_lt.mpr hbounds.2
  exact_mod_cast hcast

theorem AdmissiblePair.term_smooth {k p d i : ℕ} {n : ℤ}
    (h : AdmissiblePair k p n d) (hp : LeastPrimeAbove k p) (hi : i < k) :
    Smooth k (term n d i) := by
  obtain ⟨hne, hbound⟩ := h.term_nonzero_and_natAbs_lt hi
  exact smooth_of_natAbs_lt_leastPrime hp hne hbound

theorem AdmissiblePair.product_smooth {k p d : ℕ} {n : ℤ}
    (h : AdmissiblePair k p n d) (hp : LeastPrimeAbove k p) :
    Smooth k (progressionProduct n d (Finset.range k)) := by
  apply smooth_prod
  intro i hi
  exact h.term_smooth hp (Finset.mem_range.mp hi)

theorem AdmissiblePair.solution {k p d ell : ℕ} {n : ℤ}
    (h : AdmissiblePair k p n d) (hp : LeastPrimeAbove k p) (hk : 0 < k) :
    Solution k ell n d (progressionProduct n d (Finset.range k)) 1 (Finset.range k) := by
  have hsmooth := h.product_smooth hp
  exact {
    index_subset := Finset.Subset.refl _
    n_ne_zero := by simpa using (h.term_nonzero_and_natAbs_lt (i := 0) hk).1
    d_pos := h.step_pos
    b_ne_zero := hsmooth.1
    y_ne_zero := by decide
    coprime := h.coprime
    b_smooth := hsmooth
    equation := by simp }

end PerfectPowers
