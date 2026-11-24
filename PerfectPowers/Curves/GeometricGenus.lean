module

public import PerfectPowers.Curves.Equation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
# Geometric genus for the affine Faltings interface

For a one-variable function field in characteristic zero, geometric genus is
the dimension of rational differentials regular at every place. A place is
represented here by a discrete valuation subring containing the constants,
with the given function field as its fraction field. Regularity means lying
in the image of its Kähler differentials: finite sums of `a * db` with both
`a` and `b` in that valuation ring.

Thus the invariant below is defined from actual rings and differentials,
not from a numerical superelliptic formula or an unspecified genus function.
The standard equivalence with the genus of the smooth projective model is
part of the accepted affine formulation of Faltings. No completion, genus
formula, or mathematical axiom is asserted by this module.
-/

@[expose] public section

noncomputable section

namespace PerfectPowers

noncomputable def differentialsRegularAt (K : Type*) [Field K] [Algebra ℚ K]
    (R : Subalgebra ℚ K) : Submodule ℚ (KaehlerDifferential ℚ K) :=
  Submodule.span ℚ (Set.range (fun ab : R × R =>
    (ab.1 : K) • KaehlerDifferential.D ℚ K (ab.2 : K)))

noncomputable def regularDifferentials (K : Type*) [Field K] [Algebra ℚ K] :
    Submodule ℚ (KaehlerDifferential ℚ K) :=
  ⨅ (R : Subalgebra ℚ K) (_ : IsDiscreteValuationRing R) (_ : IsFractionRing R K),
    differentialsRegularAt K R

noncomputable def functionFieldGenus (K : Type*) [Field K] [Algebra ℚ K] : ℕ :=
  Module.finrank ℚ (regularDifferentials K)

/-- An integral affine plane equation, geometrically integral over ℚ.
The rational irreducibility field makes the coordinate-ring domain instance
explicit; geometric irreducibility uses the algebraic closure of ℚ. -/
structure AffinePlaneCurve where
  equation : MvPolynomial (Fin 2) ℤ
  irreducible : Irreducible (equation.map (Int.castRingHom ℚ))
  geometricallyIrreducible :
    Irreducible (equation.map (Int.castRingHom (AlgebraicClosure ℚ)))

namespace AffinePlaneCurve

abbrev coordinateIdeal (C : AffinePlaneCurve) : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {C.equation.map (Int.castRingHom ℚ)}

instance (C : AffinePlaneCurve) : C.coordinateIdeal.IsPrime :=
  Ideal.isPrime_span_singleton_of_prime C.irreducible.prime

abbrev coordinateRing (C : AffinePlaneCurve) :=
  MvPolynomial (Fin 2) ℚ ⧸ C.coordinateIdeal

noncomputable abbrev functionField (C : AffinePlaneCurve) := FractionRing C.coordinateRing

noncomputable def geometricGenus (C : AffinePlaneCurve) : ℕ :=
  functionFieldGenus C.functionField

/-- The plane Jacobian criterion over the algebraic closure. -/
def Nonsingular (C : AffinePlaneCurve) : Prop :=
  ∀ P : Fin 2 → AlgebraicClosure ℚ,
    MvPolynomial.eval₂ (Int.castRingHom _) P C.equation = 0 →
      ∃ i : Fin 2, MvPolynomial.eval₂ (Int.castRingHom _) P
        (MvPolynomial.pderiv i C.equation) ≠ 0

end AffinePlaneCurve
end PerfectPowers
