import SymplecticStafford.Filtered.SpecCharacteristicSupport

/- An independent concrete oracle: the identity class on the one-step
   filtration of Z has a nonzero class, so its actual Spec-support cannot be
   empty.  This exercises the filtered-class boundary on concrete data rather
   than merely checking that the source file imports. -/

open SymplecticStafford.Filtered

def integerOneStep : FiniteFilteredModule (R := ℤ) (M := ℤ) where
  height := 1
  carrier := fun n => if n = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro n
    cases n with
    | zero => simp
    | succ n => simp
  separated := by simp

def integerClass : FilteredClassData integerOneStep ℤ ℤ where
  layer := ⟨0, by decide⟩
  classMap := AddMonoidHom.id ℤ
  classMap_zero_iff_mem_next := by
    intro x
    simp [integerOneStep]

example :
    (SpecCharacteristicSupport ℤ ℤ).Nonempty := by
  apply integerClass.specSupport_nonempty_of_not_mem_next (x := 1)
  · simp [integerOneStep]
  · simp [integerOneStep]

example : SpecCharacteristicSupport ℤ ℤ ≠ ∅ := by
  intro h
  have hz :=
    (integerClass.specSupport_empty_iff_classMap_eq_zero Function.surjective_id).mp h
  have h1 := hz 1
  simpa [integerClass] using h1

#print axioms integerClass
