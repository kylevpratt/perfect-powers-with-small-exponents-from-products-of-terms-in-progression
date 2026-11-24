module

public import PerfectPowers.Curves.Equation
public import PerfectPowers.Arithmetic.Decomposition
import Mathlib.Tactic

/-!
# Algebra of the rational points constructed from progression tuples

The first lemma is independent of the arithmetic hypotheses. The second
instantiates it with integer relations and positive progression step.
-/

public section

namespace PerfectPowers

theorem point_identity_of_relations {ell m : ℕ} (hm : ell ∣ m) {d : ℚ} (hd : d ≠ 0)
    (v0 : ℚ) (v b C : Fin m → ℚ)
    (hrel : ∀ j, b j * v j ^ ell = v0 + C j * d) :
    (∏ j : Fin m, b j) * ((∏ j : Fin m, v j) / d ^ (m / ell)) ^ ell =
      ∏ j : Fin m, (v0 / d + C j) := by
  symm
  calc
    (∏ j : Fin m, (v0 / d + C j)) = ∏ j : Fin m, ((b j * v j ^ ell) / d) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hrel j]
      field_simp
    _ = (∏ j : Fin m, b j) * (∏ j : Fin m, v j) ^ ell / d ^ m := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = _ := by
      rw [div_pow, ← pow_mul, Nat.div_mul_cancel hm]
      ring

theorem onCurve_of_integer_relations {ell m d : ℕ} (hm : ell ∣ m) (hd : 0 < d)
    (q0 : ℤ) (q C : Fin m → ℤ) (x0 : ℕ) (x : Fin m → ℕ)
    (hrel : ∀ j, q j * (x j : ℤ) ^ ell = q0 * (x0 : ℤ) ^ ell + C j * (d : ℤ)) :
    OnCurve ell (∏ j : Fin m, q j) C
      ((q0 : ℚ) * (x0 : ℚ) ^ ell / (d : ℚ),
        (∏ j : Fin m, (x j : ℚ)) / (d : ℚ) ^ (m / ell)) := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hrelQ (j : Fin m) : (q j : ℚ) * (x j : ℚ) ^ ell =
      (q0 : ℚ) * (x0 : ℚ) ^ ell + (C j : ℚ) * (d : ℚ) := by
    exact_mod_cast hrel j
  simpa [OnCurve] using point_identity_of_relations hm hd0
    ((q0 : ℚ) * (x0 : ℚ) ^ ell) (fun j => (x j : ℚ)) (fun j => (q j : ℚ))
    (fun j => (C j : ℚ)) hrelQ

theorem Decomposition.divided_relation {k ell d : ℕ} {n : ℤ} {S : Finset ℕ}
    (D : Decomposition k ell n d S) {i0 i : ℕ} (hi0 : i0 ∈ S) (hi : i ∈ S)
    {f q0 q C : ℤ} (hf : f ≠ 0)
    (ha0 : D.a i0 = f * q0) (hai : D.a i = f * q)
    (hgap : (i : ℤ) - (i0 : ℤ) = f * C) :
    q * (D.x i : ℤ) ^ ell = q0 * (D.x i0 : ℤ) ^ ell + C * (d : ℤ) := by
  have hsub := term_sub_term n d i0 i
  rw [D.factor i hi, D.factor i0 hi0, ha0, hai, hgap] at hsub
  apply mul_left_cancel₀ hf
  nlinarith [hsub]

end PerfectPowers
