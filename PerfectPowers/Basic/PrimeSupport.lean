module

public import PerfectPowers.Basic.Definitions
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-! # Small and large prime support, including the units and nonzero conditions -/

@[expose] public section

namespace PerfectPowers

/-- A positive natural number all of whose prime divisors exceed `k`. -/
def Rough (k N : ℕ) : Prop :=
  N ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ N → k < p

@[simp] theorem smooth_one (k : ℕ) : Smooth k 1 := by
  refine ⟨by decide, ?_⟩
  intro p hp hdiv
  have : p = 1 := Nat.dvd_one.mp hdiv
  exact False.elim (hp.ne_one this)

@[simp] theorem smooth_neg_iff (k : ℕ) (z : ℤ) : Smooth k (-z) ↔ Smooth k z := by
  simp [Smooth]

theorem Smooth.mono {k K : ℕ} {z : ℤ} (h : Smooth k z) (hk : k ≤ K) : Smooth K z :=
  ⟨h.1, fun p hp hdvd => (h.2 p hp hdvd).trans hk⟩

theorem Smooth.of_dvd {k : ℕ} {a b : ℤ} (hb : Smooth k b)
    (ha : a ≠ 0) (hab : a ∣ b) : Smooth k a := by
  refine ⟨ha, fun p hp hpa => hb.2 p hp ?_⟩
  exact dvd_trans hpa (Int.natAbs_dvd_natAbs.mpr hab)

theorem Smooth.mul {k : ℕ} {a b : ℤ} (ha : Smooth k a) (hb : Smooth k b) :
    Smooth k (a * b) := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  intro p hp hdiv
  rw [Int.natAbs_mul] at hdiv
  rcases hp.dvd_mul.mp hdiv with hpa | hpb
  · exact ha.2 p hp hpa
  · exact hb.2 p hp hpb

theorem smooth_prod {k : ℕ} {ι : Type*} (S : Finset ι) (f : ι → ℤ)
    (h : ∀ i ∈ S, Smooth k (f i)) :
    Smooth k (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact (h i (by simp)).mul (ih (fun j hj => h j (by simp [hj])))

@[simp] theorem rough_one (k : ℕ) : Rough k 1 := by
  refine ⟨by decide, ?_⟩
  intro p hp hdiv
  exact False.elim (hp.ne_one (Nat.dvd_one.mp hdiv))

theorem Rough.of_dvd {k a b : ℕ} (hb : Rough k b) (ha : a ≠ 0) (hab : a ∣ b) :
    Rough k a := ⟨ha, fun p hp hpa => hb.2 p hp (dvd_trans hpa hab)⟩

theorem Rough.eq_one_or_gt {k N : ℕ} (h : Rough k N) : N = 1 ∨ k < N := by
  by_cases h1 : N = 1
  · exact Or.inl h1
  · obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd h1
    exact Or.inr ((h.2 p hp hpN).trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero h.1) hpN))

end PerfectPowers
