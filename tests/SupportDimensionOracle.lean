import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import SymplecticStafford.Semantics.SupportDimension

/-!
# Independent M01 support/quotient oracle

The finite `ZMod 2` object supplies an actual support datum and checks both
directions of the bottom boundary.  A separate concrete right ideal checks
the quotient class/membership bridge.  No universal support, localization,
or same-divisor producer is instantiated.
-/

namespace SymplecticStafford.SupportDimensionOracle

open SymplecticStafford

abbrev Scalar := ZMod 2

def scalarBoundary : SupportDimensionBoundary Scalar Unit where
  support := Set.univ
  dimension := 0
  dimension_bot_iff_support_empty := by
    constructor
    · intro h
      exact False.elim ((WithBot.coe_ne_bot :
        (↑(0 : Nat) : SupportDimension) ≠ ⊥) h)
    · intro h
      simp at h
  support_empty_iff_zero := by
    constructor
    · intro h
      simp at h
    · intro h
      exfalso
      have hOne : (1 : Scalar) = 0 := h 1
      exact one_ne_zero hOne

example : scalarBoundary.support = Set.univ := rfl

example : scalarBoundary.dimension ≠ (⊥ : SupportDimension) := by
  apply dimension_ne_bot_of_exists_ne_zero scalarBoundary
  exact ⟨1, one_ne_zero⟩

def zeroBoundary : SupportDimensionBoundary PUnit Empty where
  support := ∅
  dimension := ⊥
  dimension_bot_iff_support_empty := by simp
  support_empty_iff_zero := by simp

example : ∀ x : PUnit, x = 0 :=
  zero_object_of_dimension_bot zeroBoundary rfl

def trivialRightIdeal : RingRightIdeal (R := Scalar) where
  carrier := Set.univ
  zero_mem := Set.mem_univ 0
  add_mem := by intro a b _ _; exact Set.mem_univ _
  neg_mem := by intro a _; exact Set.mem_univ _
  right_mul_mem := by intro a _ q; exact Set.mem_univ _

example (a : Scalar) :
    Quotient.mk (rightIdealSetoid trivialRightIdeal) a =
      (0 : RightQuotient trivialRightIdeal) := by
  apply (rightQuotient_mk_eq_zero_iff_mem trivialRightIdeal a).mpr
  exact Set.mem_univ a

example : QuotientIsZero trivialRightIdeal :=
  (quotientIsZero_iff_one_mem trivialRightIdeal).mpr (Set.mem_univ 1)

def quotientBoundary : QuotientSupportDimensionBoundary
    trivialRightIdeal Unit where
  support := ∅
  dimension := ⊥
  dimension_bot_iff_support_empty := by simp
  support_empty_iff_zero := by
    constructor
    · intro _
      exact fun q => (quotientIsZero_iff_one_mem trivialRightIdeal).mpr
        (Set.mem_univ 1) q
    · intro _
      rfl

example : (1 : Scalar) ∈ trivialRightIdeal :=
  one_mem_of_quotient_dimension_bot trivialRightIdeal quotientBoundary rfl

end SymplecticStafford.SupportDimensionOracle

#print axioms SymplecticStafford.SupportDimensionOracle.scalarBoundary
#print axioms SymplecticStafford.SupportDimensionOracle.quotientBoundary
