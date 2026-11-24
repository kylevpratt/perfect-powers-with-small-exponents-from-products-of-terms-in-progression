module

public import PerfectPowers.Curves.GeometricGenus
public import PerfectPowers.External.Remond

/-!
# The permitted affine formulation of Faltings

This is the standard affine-plane corollary over ℚ: an absolutely irreducible
nonsingular equation of geometric genus at least two has finitely many
rational zeros. The genus is the concrete regular-differential invariant in
`Curves.GeometricGenus`. The equivalence of that invariant with the genus of
the smooth projective completion, and the passage from projective Faltings
to this affine formulation, are inside the explicitly accepted external
theorem boundary. They are not claimed as Lean proofs in this project.

This proposition defines the input; it neither declares an axiom nor assumes
the finiteness of our particular family without its geometric hypotheses.
-/

@[expose] public section

namespace PerfectPowers.External

def AffineFaltingsStatement : Prop :=
  ∀ C : AffinePlaneCurve, C.Nonsingular → 2 ≤ C.geometricGenus →
    (RationalZeros C.equation).Finite

end PerfectPowers.External
