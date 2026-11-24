module

public import PerfectPowers.Basic.Products
public import PerfectPowers.Basic.PrimeSupport
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic

/-! # Termwise smoothness, reflection, and exact progression endpoints -/

public section

namespace PerfectPowers

theorem Smooth.progression_term {k d : ℕ} {n : ℤ}
    (h : Smooth k (progressionProduct n d (Finset.range k))) {i : ℕ} (hi : i < k) :
    Smooth k (term n d i) := by
  have himem : i ∈ Finset.range k := Finset.mem_range.mpr hi
  exact h.of_dvd ((Finset.prod_ne_zero_iff.mp h.1) i himem)
    (Finset.dvd_prod_of_mem (term n d) himem)

theorem not_smooth_nat_prime {k p : ℕ} (hp : p.Prime) (hkp : k < p) : ¬Smooth k (p : ℤ) := by
  intro h
  have hle := h.2 p hp (by simpa only [Int.natAbs_natCast] using dvd_refl p)
  omega

theorem exists_index_step_one {k : ℕ} {n z : ℤ}
    (hlo : n ≤ z) (hhi : z ≤ n + ((k : ℤ) - 1)) :
    ∃ i : ℕ, i < k ∧ term n 1 i = z := by
  let i := (z - n).toNat
  have hcast : (i : ℤ) = z - n := Int.toNat_of_nonneg (sub_nonneg.mpr hlo)
  refine ⟨i, by omega, ?_⟩
  simp only [term, Nat.cast_one, mul_one]
  omega

theorem exists_index_step_two {k : ℕ} {n z : ℤ} (hn : Odd n) (hz : Odd z)
    (hlo : n ≤ z) (hhi : z ≤ n + 2 * ((k : ℤ) - 1)) :
    ∃ i : ℕ, i < k ∧ term n 2 i = z := by
  obtain ⟨a, ha⟩ := hn
  obtain ⟨b, hb⟩ := hz
  let t := b - a
  have ht : 0 ≤ t := by dsimp [t]; omega
  let i := t.toNat
  have hcast : (i : ℤ) = t := Int.toNat_of_nonneg ht
  refine ⟨i, by dsimp [t] at hcast; omega, ?_⟩
  simp only [term, Nat.cast_ofNat]
  dsimp [t] at hcast
  omega

theorem smooth_terms_reflect {k d : ℕ} {n : ℤ}
    (h : ∀ i : ℕ, i < k → Smooth k (term n d i)) :
    ∀ i : ℕ, i < k → Smooth k (term (-n - ((k : ℤ) - 1) * (d : ℤ)) d i) := by
  intro i hi
  have hj : k - 1 - i < k := by omega
  have hcast : ((k - 1 - i : ℕ) : ℤ) = (k : ℤ) - 1 - (i : ℤ) := by omega
  have heq : term (-n - ((k : ℤ) - 1) * (d : ℤ)) d i = -term n d (k - 1 - i) := by
    simp only [term, hcast]
    ring
  rw [heq]
  exact (smooth_neg_iff _ _).mpr (h _ hj)

end PerfectPowers
