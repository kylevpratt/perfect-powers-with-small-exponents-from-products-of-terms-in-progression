module

public import PerfectPowers.Arithmetic.LargePrimes
import Mathlib.Tactic

/-! # The smooth / large-prime-power decomposition in Lemma 3.1 -/

@[expose] public section

namespace PerfectPowers

/-- The factorization data on the selected indices. Coprimality and uniqueness
are proved from these fields; they are not assumptions of the structure. -/
structure Decomposition (k ell : ℕ) (n : ℤ) (d : ℕ) (S : Finset ℕ) where
  a : ℕ → ℤ
  x : ℕ → ℕ
  x_pos : ∀ i ∈ S, 0 < x i
  factor : ∀ i ∈ S, term n d i = a i * (x i : ℤ) ^ ell
  smooth : ∀ i ∈ S, Smooth k (a i)
  rough : ∀ i ∈ S, Rough k (x i)

theorem Solution.exists_term_decomposition {k ell d : ℕ} {n b y : ℤ} {S : Finset ℕ}
    (h : Solution k ell n d b y S) (hell : 0 < ell) {i : ℕ} (hi : i ∈ S) :
    ∃ a : ℤ, ∃ x : ℕ, 0 < x ∧ term n d i = a * (x : ℤ) ^ ell ∧
      Smooth k a ∧ Rough k x := by
  let z := term n d i
  let N := z.natAbs
  have hz : z ≠ 0 := h.term_ne_zero hi
  have hN : N ≠ 0 := Int.natAbs_ne_zero.mpr hz
  obtain ⟨x, hx⟩ := h.largePart_is_power hi
  have hx0 : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow hell.ne'] at hx
    exact (largePart_pos k N).ne' hx
  have hxr : Rough k x := by
    apply (largePart_rough k N).of_dvd hx0
    rw [hx]
    exact dvd_pow_self x hell.ne'
  have hsign : Smooth k (Int.sign z) := by
    refine ⟨by simpa using hz, ?_⟩
    intro p hp hdiv
    rw [Int.natAbs_sign_of_ne_zero hz] at hdiv
    exact False.elim (hp.ne_one (Nat.dvd_one.mp hdiv))
  refine ⟨Int.sign z * (smallPart k N : ℤ), x, Nat.pos_of_ne_zero hx0, ?_,
    hsign.mul (smallPart_smooth k N), hxr⟩
  calc
    z = Int.sign z * (N : ℤ) := (Int.sign_mul_natAbs z).symm
    _ = Int.sign z * ((smallPart k N : ℤ) * (largePart k N : ℤ)) := by
      congr 1
      exact_mod_cast (smallPart_mul_largePart k hN).symm
    _ = _ := by
      change Int.sign z * ((smallPart k N : ℤ) * (largePart k z.natAbs : ℤ)) = _
      rw [hx]
      push_cast
      ring

/-- Choose the decomposition on `S`. Values off `S` carry no assertions. -/
noncomputable def Solution.decomposition {k ell d : ℕ} {n b y : ℤ} {S : Finset ℕ}
    (h : Solution k ell n d b y S) (hell : 0 < ell) : Decomposition k ell n d S := by
  classical
  have hlocal : ∀ i : ℕ, ∃ a : ℤ, ∃ x : ℕ, i ∈ S →
      0 < x ∧ term n d i = a * (x : ℤ) ^ ell ∧ Smooth k a ∧ Rough k x := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨a, x, hax⟩ := h.exists_term_decomposition hell hi
      exact ⟨a, x, fun _ => hax⟩
    · exact ⟨1, 1, fun hi' => (hi hi').elim⟩
  choose a x hax using hlocal
  exact {
    a := a
    x := x
    x_pos := fun i hi => (hax i hi).1
    factor := fun i hi => (hax i hi).2.1
    smooth := fun i hi => (hax i hi).2.2.1
    rough := fun i hi => (hax i hi).2.2.2 }

namespace Decomposition

variable {k ell d : ℕ} {n : ℤ} {S : Finset ℕ} (D : Decomposition k ell n d S)

theorem a_dvd_term {i : ℕ} (hi : i ∈ S) : D.a i ∣ term n d i :=
  ⟨_, D.factor i hi⟩

theorem natAbs_a_dvd_term {i : ℕ} (hi : i ∈ S) : (D.a i).natAbs ∣ (term n d i).natAbs :=
  Int.natAbs_dvd_natAbs.mpr (D.a_dvd_term hi)

theorem x_dvd_term (hell : 0 < ell) {i : ℕ} (hi : i ∈ S) :
    D.x i ∣ (term n d i).natAbs := by
  apply Int.ofNat_dvd_left.mp
  rw [D.factor i hi]
  exact dvd_mul_of_dvd_right (dvd_pow_self (D.x i : ℤ) hell.ne') _

theorem a_coprime_step (hprimitive : Nat.Coprime n.natAbs d) {i : ℕ} (hi : i ∈ S) :
    Nat.Coprime (D.a i).natAbs d :=
  Nat.Coprime.of_dvd_left (D.natAbs_a_dvd_term hi) (term_coprime_step hprimitive i)

theorem x_coprime_step (hprimitive : Nat.Coprime n.natAbs d) (hell : 0 < ell)
    {i : ℕ} (hi : i ∈ S) : Nat.Coprime (D.x i) d :=
  Nat.Coprime.of_dvd_left (D.x_dvd_term hell hi) (term_coprime_step hprimitive i)

theorem gcd_a_dvd_index_sub (hprimitive : Nat.Coprime n.natAbs d)
    {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) :
    (Int.gcd (D.a i) (D.a j) : ℤ) ∣ (j : ℤ) - (i : ℤ) := by
  apply common_divisor_dvd_index_sub hprimitive
  · exact dvd_trans (Int.gcd_dvd_left _ _) (D.a_dvd_term hi)
  · exact dvd_trans (Int.gcd_dvd_right _ _) (D.a_dvd_term hj)

theorem x_pairwise_coprime (hprimitive : Nat.Coprime n.natAbs d) (hell : 0 < ell)
    (hS : S ⊆ Finset.range k) {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hne : i ≠ j) :
    Nat.Coprime (D.x i) (D.x j) := by
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  have hpk := (D.rough i hi).2 p hp hpi
  apply hne
  exact index_eq_of_large_common_divisor hprimitive
    (Finset.mem_range.mp (hS hi)) (Finset.mem_range.mp (hS hj)) hpk.le
    (dvd_trans hpi (D.x_dvd_term hell hi)) (dvd_trans hpj (D.x_dvd_term hell hj))

/-- The smooth coefficient is canonical even before a sign is chosen. -/
theorem natAbs_a_eq_smallPart {i : ℕ} (hi : i ∈ S) :
    (D.a i).natAbs = smallPart k (term n d i).natAbs := by
  have ha0 : (D.a i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (D.smooth i hi).1
  have hx0 : D.x i ≠ 0 := (D.x_pos i hi).ne'
  have hprod : (term n d i).natAbs = (D.a i).natAbs * D.x i ^ ell := by
    rw [D.factor i hi, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  apply Nat.eq_of_factorization_eq ha0 (smallPart_pos _ _).ne'
  intro p
  change (D.a i).natAbs.factorization p =
    (primePart (· ≤ k) (term n d i).natAbs).factorization p
  rw [factorization_primePart, Finsupp.filter_apply]
  by_cases hp : p.Prime
  · by_cases hpk : p ≤ k
    · rw [ite_eq_left hpk]
      have hxval : (D.x i).factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hdiv
        exact (not_lt_of_ge hpk) ((D.rough i hi).2 p hp hdiv)
      rw [hprod, Nat.factorization_mul ha0 (pow_ne_zero _ hx0)]
      simp [hxval, Nat.factorization_pow]
    · rw [ite_eq_right hpk]
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdiv
      exact hpk ((D.smooth i hi).2 p hp hdiv)
  · simp [hp]

/-- Uniqueness on the selected indices, including the sign of the coefficient
and the positive power part. No uniqueness is asserted off `S`. -/
theorem unique_at (E : Decomposition k ell n d S) (hell : 0 < ell)
    {i : ℕ} (hi : i ∈ S) : D.a i = E.a i ∧ D.x i = E.x i := by
  have ha : (D.a i).natAbs = (E.a i).natAbs :=
    (D.natAbs_a_eq_smallPart hi).trans (E.natAbs_a_eq_smallPart hi).symm
  have hp : (D.x i) ^ ell = (E.x i) ^ ell := by
    apply mul_left_cancel₀ (Int.natAbs_ne_zero.mpr (D.smooth i hi).1)
    have hprod := congrArg Int.natAbs ((D.factor i hi).symm.trans (E.factor i hi))
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, ← ha] using hprod
  have hx : D.x i = E.x i := Nat.pow_left_injective hell.ne' hp
  refine ⟨?_, hx⟩
  apply mul_right_cancel₀ (pow_ne_zero ell
    (show (D.x i : ℤ) ≠ 0 by exact_mod_cast (D.x_pos i hi).ne'))
  simpa only [← hx] using (D.factor i hi).symm.trans (E.factor i hi)

end Decomposition
end PerfectPowers
