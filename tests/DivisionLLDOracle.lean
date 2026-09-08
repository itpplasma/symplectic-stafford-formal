import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import SymplecticStafford.Source.DivisionLLD

/-! Independent concrete oracle for the conditional M06 affine selector. -/

namespace SymplecticStafford.DivisionLLDOracle

open SymplecticStafford.Source

abbrev U := ℚ
abbrev K := ℚ

def tests : DivisionLLDTestFamily U K where
  Index := Fin 2
  fintype := inferInstance
  ι := RingHom.id K
  ι_injective := Function.injective_id
  vCoeff := fun _ => 1
  uCoeff := fun i => if i = 0 then 0 else 1
  vCoeff_ne_zero := by intro i; norm_num
  offset := fun i => if i = 0 then 7 else -3
  rightTail := fun _ => 1
  rightTail_ne_zero := by intro i; norm_num
  generation := fun i source offset tail =>
    source = source ∧ offset = (if i = 0 then 7 else -3) ∧ tail = 1
  generation_of_pencil_ne_zero := by
    intro i B a z hne
    exact ⟨rfl, rfl, rfl⟩

example : ∃ z : K, z ∉ ⋃ i : tests.Index, tests.exceptional i :=
  tests.exists_scalar_avoiding

example (B a : U) :
    ∃ (H source : U),
      source = B + H * a ∧
      (∀ i, tests.generation i source (tests.offset i) (tests.rightTail i)) ∧
      (∀ i, tests.rightTail i ≠ 0) :=
  exists_original_affine_source tests B a

example (i : tests.Index) : tests.rightTail i ≠ 0 :=
  tests.rightTail_ne_zero i

end SymplecticStafford.DivisionLLDOracle

#print axioms SymplecticStafford.DivisionLLDOracle.tests
