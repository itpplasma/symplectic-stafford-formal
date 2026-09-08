import Mathlib.Data.ZMod.Basic
import SymplecticStafford.Ordered.SupportUnionBoundary

/-! Independent oracle for the M08 producer boundary.  The matrix ring is
finite and noncommutative, so finite generation is proved constructively; the
algebraic auxiliary relation is present, but the deliberately coarse support
map makes the union fail. -/

namespace SymplecticStafford.SupportUnionBoundaryOracle

open SymplecticStafford.Ordered

example : Nonempty (FiniteRightGeneration (R := R)
    (commonRightIdeal d F G)) :=
  finite_right_generation_of_fintype _

example : AuxiliaryDivisorRelation (R := R) d F G L := aux_relation

example : e ∈ (twoGeneratedRightIdeal d F).carrier := branch_contains_e

example : e ∉ (commonRightIdeal d F G).carrier := common_omits_e

example : ¬ (supportMissing (commonRightIdeal d F G) ⊆
    supportMissing (twoGeneratedRightIdeal d F) ∪
      supportMissing (twoGeneratedRightIdeal (d * L) G)) :=
  support_union_conclusion_fails

end SymplecticStafford.SupportUnionBoundaryOracle

#print axioms SymplecticStafford.Ordered.support_union_conclusion_fails
