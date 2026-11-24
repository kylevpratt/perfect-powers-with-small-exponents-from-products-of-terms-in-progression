module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# The elementary Euler-product estimate for the tuple lemma

This uses the proved Euler-product development in mathlib, not a Mertens or
Rosser--Schoenfeld input. A harmonic partial sum is a subsum of the series
over integers supported on the finitely many primes under consideration.
-/

@[expose] public section

namespace PerfectPowers

noncomputable def eulerDensity (A : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊A⌋₊, (1 - (p : ℝ)⁻¹)

theorem harmonic_le_inverse_euler_product (N : ℕ) :
    (harmonic N : ℝ) ≤ ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ)⁻¹
      map_one' := by simp
      map_mul' := by intro a b; simp [mul_inv_rev, mul_comm] }
  have hf {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hHas := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := f) (fun {_} hp => hf hp) (Nat.primesLE N)).2
  have hfilter : (Nat.primesLE N).filter Nat.Prime = Nat.primesLE N :=
    Finset.filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primesLE hp)
  rw [hfilter] at hHas
  have hmem (n : {n // n ∈ Finset.Icc 1 N}) :
      n.val ∈ Nat.factoredNumbers (Nat.primesLE N) := by
    obtain ⟨hn0, hnN⟩ := Finset.mem_Icc.mp n.property
    apply Nat.mem_factoredNumbers_of_primeFactors_subset (by omega)
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hnN,
      Nat.prime_of_mem_primeFactors hp⟩
  let e : {n // n ∈ Finset.Icc 1 N} ↪ Nat.factoredNumbers (Nat.primesLE N) :=
    ⟨fun n => ⟨n.val, hmem n⟩, fun a b hab => Subtype.ext
      (congrArg (fun x : Nat.factoredNumbers (Nat.primesLE N) => (x : ℕ)) hab)⟩
  let terms := (Finset.Icc 1 N).attach.map e
  calc
    (harmonic N : ℝ) = ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ = ∑ n ∈ terms, f n := by
      rw [Finset.sum_map]
      change _ = ∑ x ∈ (Finset.Icc 1 N).attach, ((x.val : ℕ) : ℝ)⁻¹
      exact (Finset.sum_attach (Finset.Icc 1 N) (fun n : ℕ => (n : ℝ)⁻¹)).symm
    _ ≤ ∑' n : Nat.factoredNumbers (Nat.primesLE N), f n := by
      exact hHas.summable.sum_le_tsum terms (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n.val))
    _ = _ := hHas.tsum_eq

theorem eulerDensity_pos {A : ℝ} : 0 < eulerDensity A := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)

theorem log_mul_eulerDensity_le_one {A : ℝ} (hA : 0 ≤ A) :
    Real.log A * eulerDensity A ≤ 1 := by
  have hH := harmonic_le_inverse_euler_product ⌊A⌋₊
  have hprod : (∏ p ∈ Nat.primesLE ⌊A⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) = (eulerDensity A)⁻¹ := by
    simp only [eulerDensity, Finset.prod_inv_distrib]
  rw [hprod] at hH
  have hlog := (log_le_harmonic_floor A hA).trans hH
  exact (le_div_iff₀ eulerDensity_pos).mp (by simpa only [one_div] using hlog)

theorem eulerDensity_le_inverse_log {A : ℝ} (hA : 1 < A) :
    eulerDensity A ≤ 1 / Real.log A := by
  apply (le_div_iff₀ (Real.log_pos hA)).mpr
  simpa [mul_comm] using log_mul_eulerDensity_le_one (le_trans (by norm_num) hA.le)

end PerfectPowers
