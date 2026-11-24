module

public import PerfectPowers.Curves.TupleConstruction
public import PerfectPowers.Curves.FamilyCounting
public import PerfectPowers.Analytic.TupleCurveParameters
import Mathlib.Tactic

/-!
# Curve points from disjoint common-divisor coefficient tuples

Representatives of distinct absolute coefficients are automatically distinct.
All curve bounds and point distinctness are proved explicitly from this fact.
-/

public section

namespace PerfectPowers

theorem coefficient_tuple_family_card_bound
    (hRemond : External.RemondStatement) {k ell d m : ℕ} {n : ℤ} {S A : Finset ℕ}
    (D : Decomposition k ell n d S) (hell : 0 < ell) (hellm : ell ≤ m) (hdiv : ell ∣ m) (hm : 2 ≤ m)
    (hprimitive : Nat.Coprime n.natAbs d) (hd : 0 < d) (hS : S ⊆ Finset.range k)
    (hA : A ⊆ Finset.Icc 1 k) (r : ℕ → ℕ)
    (hrep : ∀ a ∈ A, r a ∈ S ∧ (D.a (r a)).natAbs = a ∧ D.x (r a) ≠ 1)
    (family : Finset (Finset ℕ))
    (hprop : ∀ U ∈ family, U ⊆ A ∧ U.card = m + 1 ∧
      ∃ f : ℕ, tupleEta m * (k : ℝ) < (f : ℝ) ∧ ∀ a ∈ U, f ∣ a)
    (hdis : ∀ U ∈ family, ∀ V ∈ family, U ≠ V → Disjoint U V)
    (hfinite : CurveFamilyFinite ell m) :
    (family.card : ℝ) ≤ ((3 * (tupleSide m) ^ (2 * m) : ℕ) : ℝ) *
      External.remondBound m (3 * (tupleSide m + 1) ^ m) := by
  classical
  let ι := {U : Finset ℕ // U ∈ family}
  have hrinj : Set.InjOn r (↑A : Set ℕ) := by
    intro a ha b hb heq
    have h1 := (hrep a ha).2.1
    have h2 := (hrep b hb).2.1
    rw [heq] at h1
    exact h1.symm.trans h2
  have hex (U : ι) : ∃ f : ℕ, tupleEta m * (k : ℝ) < (f : ℝ) ∧ ∀ a ∈ U.val, f ∣ a :=
    (hprop U.val U.property).2.2
  choose f hf hfdiv using hex
  have hfpos (U : ι) : 0 < f U := by
    have h : (0 : ℝ) < f U :=
      lt_of_le_of_lt (mul_nonneg (tupleEta_pos hm).le (Nat.cast_nonneg k)) (hf U)
    exact_mod_cast h
  let J : ι → Finset ℕ := fun U => U.val.image r
  have hJS (U : ι) : J U ⊆ S := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    exact (hrep a ((hprop U.val U.property).1 ha)).1
  have hJcard (U : ι) : (J U).card = m + 1 := by
    rw [Finset.card_image_of_injOn (hrinj.mono (hprop U.val U.property).1)]
    exact (hprop U.val U.property).2.1
  have hJdiv (U : ι) (i : ℕ) (hi : i ∈ J U) : (f U : ℤ) ∣ D.a i := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    apply Int.ofNat_dvd_left.mpr
    rw [(hrep a ((hprop U.val U.property).1 ha)).2.1]
    exact hfdiv U a ha
  let T : ι → ProgressionTuple D m := fun U =>
    ProgressionTuple.ofIndexSet (J U) (hJS U) (hJcard U) (f U) (hfpos U) (hJdiv U)
  have hTsupport (U : ι) : (T U).support ⊆ J U :=
    ProgressionTuple.support_ofIndexSet_subset (J U) (hJS U) (hJcard U) (f U) (hfpos U) (hJdiv U)
  have hTindex (U : ι) (j : Fin m) : (T U).index j ∈ J U := (J U).orderEmbOfFin_mem _ j.succ
  have hsmall (U : ι) (j : Fin m) : (D.a ((T U).index j)).natAbs ≤ k := by
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp (hTindex U j)
    rw [← heq, (hrep a ((hprop U.val U.property).1 ha)).2.1]
    exact (Finset.mem_Icc.mp (hA ((hprop U.val U.property).1 ha))).2
  have hB (U : ι) : (T U).coefficient.natAbs ≤ (tupleSide m) ^ m :=
    ((T U).coefficient_natAbs_le (hsmall U)).trans
      (Nat.pow_le_pow_left (quotient_le_tupleSide hm (hf U)) m)
  have hC (U : ι) (j : Fin m) : 1 ≤ (T U).shift j ∧ (T U).shift j ≤ (tupleSide m : ℤ) := by
    refine ⟨(T U).shift_pos hprimitive j, ?_⟩
    have hside : (k / (T U).f : ℤ) ≤ (tupleSide m : ℤ) := by
      exact_mod_cast quotient_le_tupleSide hm (hf U)
    exact ((T U).shift_le hS j).trans hside
  have hnontriv (U : ι) : ∃ i ∈ (T U).support, 1 < D.x i := by
    let j : Fin m := ⟨0, by omega⟩
    have hi : (T U).index j ∈ (T U).support := ProgressionTuple.mem_support.mpr ⟨j, rfl⟩
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp (hTindex U j)
    have hxne := (hrep a ((hprop U.val U.property).1 ha)).2.2
    have hxpos := D.x_pos _ ((T U).index_mem j)
    rw [heq] at hxne
    exact ⟨_, hi, by omega⟩
  have hinj : Function.Injective (fun U : ι => (T U).point) := by
    intro U V heq
    by_contra hne
    have hUV : U.val ≠ V.val := fun h => hne (Subtype.ext h)
    have hdisJ : Disjoint (J U) (J V) := by
      apply Finset.disjoint_left.mpr
      intro i hiU hiV
      obtain ⟨a, ha, hai⟩ := Finset.mem_image.mp hiU
      obtain ⟨b, hb, hbi⟩ := Finset.mem_image.mp hiV
      have hab := hrinj ((hprop U.val U.property).1 ha) ((hprop V.val V.property).1 hb) (hai.trans hbi.symm)
      exact Finset.disjoint_left.mp (hdis U.val U.property V.val V.property hUV) ha (hab.symm ▸ hb)
    exact (T U).point_ne_of_disjoint (T V) hprimitive hell hd hS
      (hdisJ.mono (hTsupport U) (hTsupport V)) (hnontriv U) heq
  have hcount := card_le_power_curve_family_bound_of_finite hRemond hell (tupleSide_pos hm)
    (Finset.univ : Finset ι) (fun U => (T U).coefficient) (fun U => (T U).shift) (fun U => (T U).point)
    (fun U _ => hB U) (fun U _ => hC U) (fun U _ => (T U).point_onCurve hprimitive hd hdiv)
    (fun U _ V _ heq => hinj heq)
    (fun U _ => hfinite (T U).coefficient (T U).shift (T U).coefficient_ne_zero
      ((T U).shift_injective hprimitive) (fun j => by have h := (T U).shift_pos hprimitive j; omega))
  simpa only [Finset.card_univ, ι, Fintype.card_coe, max_eq_right hellm] using hcount

end PerfectPowers
