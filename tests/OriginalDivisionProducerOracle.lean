import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import SymplecticStafford.Source.OriginalDivisionProducer

/-!
# Independent oracle for the bridged original-`U` M06 producer

Three local tests over `ℚ` use distinct offsets and nonzero right tails.  Their
generation predicates are tied to the actual local data, while each pencil
bridge is checked independently.  The theorem under test chooses one `H : ℚ`
for the entire list rather than receiving a source witness.
-/

namespace SymplecticStafford.OriginalDivisionProducerOracle

open SymplecticStafford.Source

abbrev U := ℚ
abbrev K := ℚ

def mkLocalTest (offset : Int) (tail : U) (htail : tail ≠ 0) :
    OriginalLocalTest U Unit Unit where
  targetDivisor := 1
  localization := ()
  cyclicFiniteModule := ()
  canonicalGenerator := ()
  rightTail := tail
  offset := offset
  localization_spec := True
  localization_spec_proof := True.intro
  finite_length_cyclic_spec := True
  finite_length_cyclic_proof := True.intro
  canonical_generator_spec := True
  canonical_generator_spec_proof := True.intro
  rightTail_nonzero := htail
  generation := fun _ gotOffset gotTail =>
    gotOffset = offset ∧ gotTail = tail

def mkTest (v u : U) (hv : v ≠ 0)
    (offset : Int) (tail : U) (htail : tail ≠ 0) :
    OriginalDivisionTest U K Unit Unit where
  localTest := mkLocalTest offset tail htail
  vCoeff := v
  uCoeff := u
  vCoeff_ne_zero := hv
  passes_of_pencil_ne_zero := by
    intro ι B a z hp
    exact ⟨rfl, rfl⟩

def tests : List (OriginalDivisionTest U K Unit Unit) :=
  [mkTest 1 1 (by norm_num) 7 2 (by norm_num),
    mkTest 2 (-1) (by norm_num) (-4) 3 (by norm_num),
    mkTest 3 2 (by norm_num) 12 5 (by norm_num)]

theorem tests_admissible :
    ∀ t, t ∈ tests → t.localTest.Admissible (1 : U) := by
  intro t ht
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | hnil
  · exact OriginalLocalTest.admissible_of_fields 1 _ rfl
  · exact OriginalLocalTest.admissible_of_fields 1 _ rfl
  · exact OriginalLocalTest.admissible_of_fields 1 _ rfl
  · simp at hnil

theorem source_passes (B a : U) (ha : a ≠ 0) :
    ∃ (H source : U),
      source = B + H * a ∧
      (∀ t, t ∈ tests → t.localTest.Admissible (1 : U)) ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.localTest.rightTail ≠ 0) := by
  exact exists_original_affine_source_of_bridged_list
    (RingHom.id K) Function.injective_id tests 1 B a ha tests_admissible

example (B a : U) (ha : a ≠ 0) :
    ∃ H source : U, source = B + H * a := by
  obtain ⟨H, source, hsource, -, -, -⟩ := source_passes B a ha
  exact ⟨H, source, hsource⟩

example (source : U) :
    ¬ (mkTest 1 1 (by norm_num) 7 2 (by norm_num)).localTest.generation
      source 8 2 := by
  simp [mkTest, mkLocalTest]

end SymplecticStafford.OriginalDivisionProducerOracle

#print axioms SymplecticStafford.OriginalDivisionProducerOracle.source_passes
