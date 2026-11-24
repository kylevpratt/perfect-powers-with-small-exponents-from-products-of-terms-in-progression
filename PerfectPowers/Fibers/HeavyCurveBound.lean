module

public import PerfectPowers.Fibers.HeavyTuples
public import PerfectPowers.Curves.EqualFiberTuples
public import PerfectPowers.Curves.FamilyCounting
import Mathlib.Tactic

/-!
# The finite curve-counting inequality for heavy fibers

The finiteness premise is supplied by `Curves.AffineFiniteness` from the
permitted affine Faltings and genus inputs. It is kept explicit here, rather than installed as
another mathematical axiom. No hypothesis on the total number of trivial
power parts is needed for this finite inequality.
-/

public section

namespace PerfectPowers

theorem Decomposition.heavy_mass_le_curve_bound
    (hRemond : External.RemondStatement) {k ell d m L : ℕ} {n : ℤ} {S : Finset ℕ}
    (D : Decomposition k ell n d S) (I : GoodIndices D)
    (hell : 0 < ell) (hellm : ell ≤ m) (hdiv : ell ∣ m) (hm : 3 ≤ m)
    (hprimitive : Nat.Coprime n.natAbs d) (hd : 0 < d) (hS : S ⊆ Finset.range k) (hL : 0 < L)
    (hfinite : CurveFamilyFinite ell m) :
    ((D.heavyIndices I m).card : ℝ) ≤
      ((m : ℝ) + 1) ^ 2 * (((3 * L ^ m : ℕ) : ℝ) *
        External.remondBound m (3 * (L + 1) ^ m)) +
      (m : ℝ) * ((m : ℝ) + 1) * ((k : ℝ) / L) * (1 + Real.log (k : ℝ)) := by
  classical
  obtain ⟨family, hprop, hdis, hcard⟩ := D.exists_heavy_short_tuples I hL hS
  let ι := {U : Finset ℕ // U ∈ family}
  have hex (U : ι) : ∃ a : ℕ, 1 ≤ a ∧ a ≤ k ∧
      (∀ i ∈ U.val, (D.a i).natAbs = a) ∧ ∀ i ∈ U.val, ∀ j ∈ U.val, Nat.dist i j < a * L :=
    (hprop U.val U.property).2.2
  choose a ha1 hak hcoeff hgap using hex
  have hUS (U : ι) : U.val ⊆ S := by
    intro i hi
    exact I.subset (Finset.mem_filter.mp ((hprop U.val U.property).1 hi)).1
  have hUdiv (U : ι) (i : ℕ) (hi : i ∈ U.val) : (a U : ℤ) ∣ D.a i := by
    apply Int.ofNat_dvd_left.mpr
    rw [hcoeff U i hi]
  let T : ι → ProgressionTuple D m := fun U => ProgressionTuple.ofIndexSet
    U.val (hUS U) (hprop U.val U.property).2.1 (a U) (ha1 U) (hUdiv U)
  have hTabs (U : ι) (j : Fin m) : (D.a ((T U).index j)).natAbs = (T U).f := by
    change (D.a (U.val.orderEmbOfFin (hprop U.val U.property).2.1 j.succ)).natAbs = a U
    exact hcoeff U _ (U.val.orderEmbOfFin_mem _ j.succ)
  have hTgap (U : ι) (j : Fin m) : (T U).index j - (T U).base < (T U).f * L := by
    have hi : (T U).index j ∈ U.val := U.val.orderEmbOfFin_mem _ j.succ
    have hbase : (T U).base ∈ U.val := U.val.orderEmbOfFin_mem _ 0
    have h := hgap U _ hi _ hbase
    rw [Nat.dist_eq_sub_of_le_right ((T U).base_lt j).le] at h
    exact h
  have hTsupport (U : ι) : (T U).support ⊆ U.val :=
    ProgressionTuple.support_ofIndexSet_subset U.val (hUS U) (hprop U.val U.property).2.1
      (a U) (ha1 U) (hUdiv U)
  have hinj : Function.Injective (fun U : ι => (T U).point) := by
    intro U V heq
    by_contra hne
    have hUV : U.val ≠ V.val := fun h => hne (Subtype.ext h)
    have hdisSupport : Disjoint (T U).support (T V).support :=
      (hdis U.val U.property V.val V.property hUV).mono (hTsupport U) (hTsupport V)
    exact (T U).point_ne_of_disjoint (T V) hprimitive hell hd hS hdisSupport
      ((T U).support_has_nontrivial hd hm (hTabs U)) heq
  have hpointCount := card_le_curve_family_bound_of_finite hRemond hell
    (Finset.univ : Finset ι) (fun U => (T U).coefficient) (fun U => (T U).shift) (fun U => (T U).point)
    (fun U _ => ((T U).coefficient_natAbs_eq_one (hTabs U)).le)
    (fun U _ j => ⟨(T U).shift_pos hprimitive j, (T U).shift_le_of_short_gaps hprimitive (hTgap U) j⟩)
    (fun U _ => (T U).point_onCurve hprimitive hd hdiv)
    (fun U _ V _ heq => hinj heq)
    (fun U _ => hfinite (T U).coefficient (T U).shift (T U).coefficient_ne_zero
      ((T U).shift_injective hprimitive) (fun j => by have h := (T U).shift_pos hprimitive j; omega))
  have hfamily : (family.card : ℝ) ≤ ((3 * L ^ m : ℕ) : ℝ) *
      External.remondBound m (3 * (L + 1) ^ m) := by
    simpa only [Finset.card_univ, ι, Fintype.card_coe, max_eq_right hellm] using hpointCount
  have hmul := mul_le_mul_of_nonneg_left hfamily (sq_nonneg ((m : ℝ) + 1))
  linarith

end PerfectPowers
