module

public import SymplecticStafford.FiniteLength.DivisionEigenObstruction
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-!
# Independent oracle for the zero-pencil obstruction

The theorem is instantiated at the infinite field `ℚ` and the regular
one-dimensional `ℚ`-module.  No determinant or commutativity extension is
used; the oracle checks that the declared bad set really is all scalars.
-/

namespace SymplecticStafford.FiniteLength.DivisionEigenObstructionOracle

open SymplecticStafford.FiniteLength

example :
    ¬ ({z : ℚ | ¬ LinearIndependent ℚ (fun _ : Unit => (0 : ℚ))}).Finite := by
  exact zero_pencil_bad_set_not_finite

end SymplecticStafford.FiniteLength.DivisionEigenObstructionOracle

#print axioms SymplecticStafford.FiniteLength.zero_pencil_bad_set_not_finite
