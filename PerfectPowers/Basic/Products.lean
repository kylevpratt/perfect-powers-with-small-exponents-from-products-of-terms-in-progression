module

public import PerfectPowers.Basic.Definitions
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # Elementary identities and nonvanishing for progression products -/

public section

namespace PerfectPowers

@[simp] theorem term_zero (n : ℤ) (d : ℕ) : term n d 0 = n := by simp [term]

theorem term_sub_term (n : ℤ) (d i j : ℕ) :
    term n d j - term n d i = ((j : ℤ) - (i : ℤ)) * (d : ℤ) := by
  simp only [term]
  ring

theorem term_strictMono (n : ℤ) {d : ℕ} (hd : 0 < d) : StrictMono (term n d) := by
  intro i j hij
  dsimp [term]
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hij' : (i : ℤ) < j := by exact_mod_cast hij
  nlinarith

theorem term_injective (n : ℤ) {d : ℕ} (hd : 0 < d) :
    Function.Injective (term n d) := (term_strictMono n hd).injective

theorem Solution.product_ne_zero {k ell d : ℕ} {n b y : ℤ} {S : Finset ℕ}
    (h : Solution k ell n d b y S) : progressionProduct n d S ≠ 0 := by
  rw [h.equation]
  exact mul_ne_zero h.b_ne_zero (pow_ne_zero _ h.y_ne_zero)

theorem Solution.term_ne_zero {k ell d : ℕ} {n b y : ℤ} {S : Finset ℕ}
    (h : Solution k ell n d b y S) {i : ℕ} (hi : i ∈ S) : term n d i ≠ 0 := by
  exact (Finset.prod_ne_zero_iff.mp h.product_ne_zero) i hi

theorem natAbs_progressionProduct (n : ℤ) (d : ℕ) (S : Finset ℕ) :
    (progressionProduct n d S).natAbs = ∏ i ∈ S, (term n d i).natAbs := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [progressionProduct]
  | @insert i S hi ih =>
      simp [progressionProduct, Finset.prod_insert, hi, Int.natAbs_mul]

/-- Reverse the full progression and negate its terms. The identity includes
the empty product and places the sign in the explicit factor `(-1)^k`. -/
theorem progressionProduct_reflect (n : ℤ) (d k : ℕ) :
    progressionProduct n d (Finset.range k) =
      (-1 : ℤ) ^ k *
        progressionProduct (-n - ((k : ℤ) - 1) * (d : ℤ)) d (Finset.range k) := by
  classical
  unfold progressionProduct
  calc
    (∏ i ∈ Finset.range k, term n d i) =
        ∏ i ∈ Finset.range k,
          (-1 : ℤ) * term (-n - ((k : ℤ) - 1) * (d : ℤ)) d (k - 1 - i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hcast : ((k - 1 - i : ℕ) : ℤ) = (k : ℤ) - 1 - (i : ℤ) := by omega
      simp only [term, hcast]
      ring
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_range_reflect]

end PerfectPowers
