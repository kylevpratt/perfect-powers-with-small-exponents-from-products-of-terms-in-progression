module

public import PerfectPowers.Basic.PrimeSupport
import Mathlib.Tactic

/-! # Canonical parts of a natural number selected by its prime support -/

@[expose] public section

namespace PerfectPowers

/-- Retain precisely the prime-power factors whose bases satisfy `P`. -/
def primePart (P : ℕ → Prop) [DecidablePred P] (N : ℕ) : ℕ :=
  (N.factorization.filter P).prod (· ^ ·)

theorem primePart_pos (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    0 < primePart P N := by
  unfold primePart Finsupp.prod
  apply Finset.prod_pos
  intro p hp
  have hpN : p ∈ N.factorization.support := (Finset.mem_filter.mp hp).1
  exact pow_pos (Nat.prime_of_mem_primeFactors hpN).pos _

theorem factorization_primePart (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    (primePart P N).factorization = N.factorization.filter P := by
  apply Nat.factorization_prod_pow_eq_self
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem primePart_mul_compl (P : ℕ → Prop) [DecidablePred P] {N : ℕ} (hN : N ≠ 0) :
    primePart P N * primePart (fun p => ¬ P p) N = N := by
  unfold primePart
  rw [Finsupp.prod_filter_mul_prod_filter_not, Nat.prod_factorization_pow_eq_self hN]

theorem prime_dvd_primePart_iff (P : ℕ → Prop) [DecidablePred P] (N : ℕ)
    {p : ℕ} (hp : p.Prime) : p ∣ primePart P N ↔ p ∣ N ∧ N ≠ 0 ∧ P p := by
  rw [hp.dvd_iff_one_le_factorization (primePart_pos P N).ne', factorization_primePart]
  by_cases hP : P p
  · simp only [Finsupp.filter_apply_pos _ _ hP, hP, and_true]
    rw [Nat.one_le_iff_ne_zero, ne_eq, Nat.factorization_eq_zero_iff]
    tauto
  · simp [Finsupp.filter_apply_neg _ _ hP, hP]

def smallPart (k N : ℕ) : ℕ := primePart (· ≤ k) N

def largePart (k N : ℕ) : ℕ := primePart (fun p => ¬ p ≤ k) N

theorem smallPart_pos (k N : ℕ) : 0 < smallPart k N := primePart_pos _ _

theorem largePart_pos (k N : ℕ) : 0 < largePart k N := primePart_pos _ _

theorem smallPart_mul_largePart (k : ℕ) {N : ℕ} (hN : N ≠ 0) :
    smallPart k N * largePart k N = N := primePart_mul_compl _ hN

theorem smallPart_smooth (k N : ℕ) : Smooth k (smallPart k N : ℤ) := by
  refine ⟨by exact_mod_cast (smallPart_pos k N).ne', ?_⟩
  intro p hp hdiv
  exact ((prime_dvd_primePart_iff (· ≤ k) N hp).mp hdiv).2.2

theorem largePart_rough (k N : ℕ) : Rough k (largePart k N) := by
  refine ⟨(largePart_pos k N).ne', ?_⟩
  intro p hp hdiv
  exact Nat.lt_of_not_ge ((prime_dvd_primePart_iff (fun p => ¬ p ≤ k) N hp).mp hdiv).2.2

/-- Divisibility of all prime multiplicities characterizes positive perfect powers. -/
theorem exists_eq_pow_iff_factorization_dvd {N ell : ℕ} (hN : N ≠ 0) :
    (∃ x : ℕ, N = x ^ ell) ↔ ∀ p : ℕ, p.Prime → ell ∣ N.factorization p := by
  constructor
  · rintro ⟨x, rfl⟩ p hp
    simp [Nat.factorization_pow]
  · intro h
    let f := N.factorization.mapRange (· / ell) (Nat.zero_div ell)
    let x := f.prod (· ^ ·)
    have hf : ∀ p ∈ f.support, p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
    have hx : x ≠ 0 := by
      apply Finsupp.prod_ne_zero_iff.mpr
      intro p hp
      exact pow_ne_zero _ (hf p hp).ne_zero
    refine ⟨x, Nat.eq_of_factorization_eq hN (pow_ne_zero _ hx) ?_⟩
    intro p
    rw [Nat.factorization_pow, Nat.factorization_prod_pow_eq_self hf]
    by_cases hp : p.Prime
    · simpa [f, Finsupp.smul_apply, smul_eq_mul] using (Nat.mul_div_cancel' (h p hp)).symm
    · simp [f, Nat.factorization_eq_zero_of_not_prime N hp]

end PerfectPowers
