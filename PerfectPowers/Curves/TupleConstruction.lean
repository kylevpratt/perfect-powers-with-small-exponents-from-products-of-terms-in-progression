module

public import PerfectPowers.Curves.ProgressionTuple
public import PerfectPowers.Curves.PointDistinctness
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! # Constructing ordered progression tuples from finite index sets -/

@[expose] public section

namespace PerfectPowers.ProgressionTuple

variable {k ell d m : ℕ} {n : ℤ} {S : Finset ℕ}
    {D : Decomposition k ell n d S}

noncomputable def ofIndexSet (U : Finset ℕ) (hU : U ⊆ S) (hcard : U.card = m + 1)
    (f : ℕ) (hf : 0 < f) (hdiv : ∀ i ∈ U, (f : ℤ) ∣ D.a i) : ProgressionTuple D m :=
  { base := U.orderEmbOfFin hcard 0
    index := fun j => U.orderEmbOfFin hcard j.succ
    base_mem := hU (U.orderEmbOfFin_mem hcard 0)
    index_mem := fun j => hU (U.orderEmbOfFin_mem hcard j.succ)
    base_lt := fun j => (U.orderEmbOfFin hcard).strictMono (by exact_mod_cast Nat.succ_pos j.val)
    index_injective := fun i j hij => Fin.succ_injective _ ((U.orderEmbOfFin hcard).injective hij)
    f := f
    f_pos := hf
    base_dvd := hdiv _ (U.orderEmbOfFin_mem hcard 0)
    index_dvd := fun j => hdiv _ (U.orderEmbOfFin_mem hcard j.succ) }

def support (T : ProgressionTuple D m) : Finset ℕ := Finset.univ.image T.index

theorem mem_support {T : ProgressionTuple D m} {i : ℕ} :
    i ∈ T.support ↔ ∃ j, T.index j = i := by simp [support]

theorem card_support (T : ProgressionTuple D m) : T.support.card = m := by
  rw [support, Finset.card_image_of_injective _ T.index_injective]
  simp

theorem support_subset (T : ProgressionTuple D m) : T.support ⊆ S := by
  intro i hi
  obtain ⟨j, rfl⟩ := mem_support.mp hi
  exact T.index_mem j

theorem support_ofIndexSet_subset (U : Finset ℕ) (hU : U ⊆ S) (hcard : U.card = m + 1)
    (f : ℕ) (hf : 0 < f) (hdiv : ∀ i ∈ U, (f : ℤ) ∣ D.a i) :
    (ofIndexSet U hU hcard f hf hdiv).support ⊆ U := by
  intro i hi
  obtain ⟨j, rfl⟩ := mem_support.mp hi
  exact U.orderEmbOfFin_mem hcard j.succ

theorem pointY_eq_support_product (T : ProgressionTuple D m) :
    T.point.2 = (∏ i ∈ T.support, (D.x i : ℚ)) / (d : ℚ) ^ (m / ell) := by
  change _ = (∏ i ∈ Finset.univ.image T.index, (D.x i : ℚ)) / _
  rw [Finset.prod_image (fun i hi j hj hij => T.index_injective hij)]
  rfl

theorem point_ne_of_disjoint (T U : ProgressionTuple D m)
    (hprimitive : Nat.Coprime n.natAbs d) (hell : 0 < ell)
    (hd : 0 < d) (hS : S ⊆ Finset.range k) (hdis : Disjoint T.support U.support)
    (hlarge : ∃ i ∈ T.support, 1 < D.x i) : T.point ≠ U.point := by
  intro heq
  have hY := congrArg Prod.snd heq
  rw [T.pointY_eq_support_product, U.pointY_eq_support_product] at hY
  exact D.pointY_ne_of_disjoint hprimitive hell hS T.support_subset U.support_subset hdis hlarge
    (pow_ne_zero _ (by exact_mod_cast hd.ne' : (d : ℚ) ≠ 0)) hY

end PerfectPowers.ProgressionTuple
