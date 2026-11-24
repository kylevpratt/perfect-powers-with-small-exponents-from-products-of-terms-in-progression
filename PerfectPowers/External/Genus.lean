module

public import PerfectPowers.Curves.SuperellipticGeometry

/-!
# The permitted geometric-genus lower bound

The genus of every equation in the paper's family is at least two, uniformly
over the nonzero signed coefficient and distinct positive integer shifts.
The genus means the actual regular-differential invariant of the coordinate
ring's fraction field, shared with the affine Faltings interface. The
numerical superelliptic genus formula is not used as its definition.

Irreducibility and nonsingularity are proved internally, independently of
this lower bound. The bound is an accepted external hypothesis; proving it
is outside the agreed project scope.
-/

@[expose] public section

namespace PerfectPowers.External

def SuperellipticGenusStatement : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (B : ℤ) (C : Fin (branchCount ell) → ℤ)
    (hB : B ≠ 0) (hC : Function.Injective C),
    (∀ j, 0 < C j) → 2 ≤ (superellipticAffineCurve hell B C hB hC).geometricGenus

end PerfectPowers.External
