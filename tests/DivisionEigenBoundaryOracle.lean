import SymplecticStafford.FiniteLength.DivisionEigenBoundary
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Independent oracle for the division-ring pencil boundary

This oracle checks the contract on a one-point central pencil over `ℚ`.
The proof invokes the arbitrary-division-ring witness theorem, while the
singleton calculation independently verifies the advertised bad set.
It is deliberately not an oracle for constructing witnesses in a general
noncommutative division ring.
-/

namespace SymplecticStafford.FiniteLength.DivisionEigenBoundaryOracle

open SymplecticStafford.FiniteLength

example : ({0} : Set ℚ).Finite := by
  apply finite_central_pencil_bad_of_independent_witness
    (K := ℚ) (E := ℚ) (V := ℚ)
    (pencil := fun z (_ : Unit) => z)
    (bad := ({0} : Set ℚ))
    (witness := fun _ : ({0} : Set ℚ) => (1 : ℚ))
  · intro z
    simp [linearIndependent_unique_iff]
  · exact linearIndependent_unique_iff.mpr (by simp)

end SymplecticStafford.FiniteLength.DivisionEigenBoundaryOracle

#print axioms SymplecticStafford.FiniteLength.finite_central_pencil_bad_of_independent_witness
