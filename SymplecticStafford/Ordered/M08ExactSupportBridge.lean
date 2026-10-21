module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Support
public import SymplecticStafford.Filtered.SpecCharacteristicSupport

@[expose] public section

/-!
# Exact characteristic-support bridge for M08

The common-colon calculation is an identity in the original noncommutative
ring.  To turn it into a support union, however, one still needs an actual
short exact sequence of modules over the commutative coefficient ring (or an
equivalent localized-zero theorem).  This file records the exact-sequence
route with all maps and exactness fields exposed.  It is a consumer, not a
construction of the associated graded module or of the maps.

The second half is a small actual-support boundary.  Even finite separated
filtered modules with explicit class maps can have a nonempty middle support
and empty branch supports.  Thus finite filtration/class data alone cannot
replace the exact sequence or localized-zero bridge.
-/

namespace SymplecticStafford.Ordered

universe u v w

section ExactBridge

variable {A : Type u} [CommRing A]
variable {QF : Type v} {QJ : Type w} {QG : Type u}
variable [AddCommGroup QF] [Module A QF]
variable [AddCommGroup QJ] [Module A QJ]
variable [AddCommGroup QG] [Module A QG]

/-- The precise module-theoretic input which makes the M08 support union
    formal.  `left` and `right` are the actual branch maps; no ideal quotient
    or localization is hidden in this structure. -/
structure ExactCharacteristicSupportBridge where
  left : QF →ₗ[A] QJ
  right : QJ →ₗ[A] QG
  exact : Function.Exact left right
  left_injective : Function.Injective left
  right_surjective : Function.Surjective right

theorem characteristicSupport_eq_union_of_exact_bridge
    (B : ExactCharacteristicSupportBridge (A := A) (QF := QF)
      (QJ := QJ) (QG := QG)) :
    Module.support A QJ = Module.support A QF ∪ Module.support A QG := by
  exact Module.support_of_exact B.exact B.left_injective B.right_surjective

theorem characteristicSupport_subset_union_of_exact_bridge
    (B : ExactCharacteristicSupportBridge (A := A) (QF := QF)
      (QJ := QJ) (QG := QG)) :
    Module.support A QJ ⊆ Module.support A QF ∪ Module.support A QG := by
  rw [characteristicSupport_eq_union_of_exact_bridge B]

end ExactBridge

section FilteredBoundary

/-- A one-step exhaustive/separated filtration of the integer module. -/
def integerOneStep : SymplecticStafford.Filtered.FiniteFilteredModule
    (R := ℤ) (M := ℤ) where
  height := 1
  carrier := fun n => if n = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro n
    cases n with
    | zero => simp
    | succ n => simp
  separated := by simp

/-- The same finite filtration on the zero module `ZMod 1`. -/
def zeroOneStep : SymplecticStafford.Filtered.FiniteFilteredModule
    (R := ℤ) (M := ZMod 1) where
  height := 1
  carrier := fun n => if n = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro n
    cases n with
    | zero => simp
    | succ n => simp
  separated := by simp

/- Explicit class maps show that the filtered boundary is not merely a
   proposition-valued support assignment. -/
def integerClass : SymplecticStafford.Filtered.FilteredClassData
    integerOneStep ℤ ℤ where
  layer := ⟨0, by decide⟩
  classMap := AddMonoidHom.id ℤ
  classMap_zero_iff_mem_next := by
    intro x
    simp [integerOneStep]

def zeroClass : SymplecticStafford.Filtered.FilteredClassData
    zeroOneStep ℤ (ZMod 1) where
  layer := ⟨0, by decide⟩
  classMap := AddMonoidHom.id (ZMod 1)
  classMap_zero_iff_mem_next := by
    intro x
    simp [zeroOneStep]

theorem integer_actual_support_eq_univ :
    Module.support ℤ ℤ = Set.univ := by
  exact Module.support_of_noZeroSMulDivisors

theorem zero_mod_one_actual_support_eq_empty :
    Module.support ℤ (ZMod 1) = ∅ := by
  apply Module.support_eq_empty_iff.mpr
  infer_instance

/-- A genuine `Module.support` countermodel to support union under finite
    filtered/class data alone: the middle module is `ℤ`, while both branch
    modules are zero. -/
theorem finite_filtered_actual_support_union_fails :
    ¬ (Module.support ℤ ℤ ⊆
      Module.support ℤ (ZMod 1) ∪ Module.support ℤ (ZMod 1)) := by
  rw [integer_actual_support_eq_univ,
    zero_mod_one_actual_support_eq_empty]
  simp

end FilteredBoundary

end SymplecticStafford.Ordered

#print axioms
  SymplecticStafford.Ordered.characteristicSupport_eq_union_of_exact_bridge
#print axioms
  SymplecticStafford.Ordered.finite_filtered_actual_support_union_fails
