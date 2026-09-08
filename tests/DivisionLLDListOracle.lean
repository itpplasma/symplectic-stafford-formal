import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic
import SymplecticStafford.Source.DivisionLLDList

/-! Independent behavioral oracle for the list-indexed M06 source theorem. -/

namespace SymplecticStafford.DivisionLLDListOracle

open SymplecticStafford.Source

abbrev U := ℚ
abbrev K := ℚ

def mkTest (v u : U) (hv : v ≠ 0) (offset : Int) (tail : U)
    (ht : tail ≠ 0) : AffineDivisionTest U K where
  vCoeff := v
  uCoeff := u
  vCoeff_ne_zero := hv
  offset := offset
  rightTail := tail
  rightTail_ne_zero := ht
  passes := fun source gotOffset gotTail =>
    gotOffset = offset ∧ gotTail = tail
  passes_of_pencil_ne_zero := by
    intro ι B a z hp
    exact ⟨rfl, rfl⟩

def tests : List (AffineDivisionTest U K) :=
  [mkTest 1 1 (by norm_num) 7 2 (by norm_num),
    mkTest 2 (-1) (by norm_num) (-4) 3 (by norm_num),
    mkTest 3 2 (by norm_num) 12 5 (by norm_num)]

example : (mkTest 1 1 (by norm_num) 7 2 (by norm_num)).offset = 7 := by rfl
example : (mkTest 2 (-1) (by norm_num) (-4) 3 (by norm_num)).offset = -4 := by rfl
example : (mkTest 3 2 (by norm_num) 12 5 (by norm_num)).rightTail = 5 := by rfl

theorem source_passes (B a : U) (ha : a ≠ 0) :
    ∃ (H source : U),
      source = B + H * a ∧
      (∀ t, t ∈ tests → t.passes source t.offset t.rightTail) ∧
      (∀ t, t ∈ tests → t.rightTail ≠ 0) := by
  obtain ⟨H, source, hsource, hpasses, htails⟩ :=
    exists_original_affine_source_of_list (RingHom.id K) Function.injective_id
      tests B a
  exact ⟨H, source, hsource, hpasses, htails⟩

example (source : U) :
    ¬ (mkTest 1 1 (by norm_num) 7 2 (by norm_num)).passes source 8 2 := by
  simp [mkTest]

example (source : U) :
    ¬ (mkTest 2 (-1) (by norm_num) (-4) 3 (by norm_num)).passes source (-4) 0 := by
  simp [mkTest]

end SymplecticStafford.DivisionLLDListOracle

#print axioms SymplecticStafford.DivisionLLDListOracle.source_passes
