module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Tactic.FinCases
public import SymplecticStafford.Source.OriginalTestContract
public import SymplecticStafford.Source.DivisionLLD

@[expose] public section

/-!
# Independent oracle for the concrete original-ring finite source theorem

This oracle uses the division ring `ℚ` and three genuinely different tests.
Their offsets are not normalized and their right tails are not all the same.
The source is selected by avoiding the actual root of `B + z*a`; the assembly
cofactors are then constructed in `ℚ` itself, rather than passed through a
producer contract.
-/

namespace SymplecticStafford.OriginalAffineDivisionOracle

open SymplecticStafford.Source

abbrev U := ℚ
abbrev K := ℚ
abbrev I := Fin 3

def testFamily : NonzeroAffineTestFamily U K where
  Index := I
  fintype := inferInstance
  ι := RingHom.id K
  ι_injective := Function.injective_id
  offset := fun i : I => if i = 0 then 7 else if i = 1 then -4 else 12
  rightTail := fun i : I => if i = 0 then 2 else if i = 1 then 3 else 5
  rightTail_ne_zero := by
    intro i
    fin_cases i
    · norm_num
    · norm_num
    · have h20 : (2 : I) ≠ 0 := by decide
      simp [h20]

example : testFamily.offset (0 : I) = 7 := by rfl
example : testFamily.offset (1 : I) = -4 := by rfl
example : testFamily.offset (2 : I) = 12 := by rfl
example : testFamily.rightTail (0 : I) = 2 := by rfl
example : testFamily.rightTail (1 : I) = 3 := by rfl
example : testFamily.rightTail (2 : I) = 5 := by rfl

theorem selected_source_passes (B : U) (a : U) (ha : a ≠ 0) :
    ∃ (H source : U),
      source = B + H * a ∧
      (∀ i, testFamily.generation i source
        (testFamily.offset i) (testFamily.rightTail i)) ∧
      (∀ i, testFamily.rightTail i ≠ 0) :=
  testFamily.exists_original_affine_source B a ha

/- The predicate is behavioral: changing an offset or tail makes a test fail,
so the oracle cannot pass merely by forgetting those fields. -/
example (source : U) :
    ¬ testFamily.generation (0 : I) source 8 2 := by
  change ¬ (source ≠ 0 ∧ (8 : Int) = 7 ∧ (2 : U) = 2)
  norm_num

example (source : U) :
    ¬ testFamily.generation (1 : I) source (-4) 0 := by
  change ¬ (source ≠ 0 ∧ (-4 : Int) = -4 ∧ (0 : U) = 3)
  norm_num

def localTest (i : I) : OriginalLocalTest U Unit Unit where
  targetDivisor := 1
  localization := ()
  cyclicFiniteModule := ()
  canonicalGenerator := ()
  rightTail := testFamily.rightTail i
  offset := testFamily.offset i
  localization_spec := True
  localization_spec_proof := True.intro
  finite_length_cyclic_spec := True
  finite_length_cyclic_proof := True.intro
  canonical_generator_spec := True
  canonical_generator_spec_proof := True.intro
  rightTail_nonzero := testFamily.rightTail_ne_zero i
  generation := testFamily.generation i

def localTests : List (OriginalLocalTest U Unit Unit) :=
  [localTest (0 : I), localTest (1 : I), localTest (2 : I)]

theorem local_tests_are_admissible :
    AdmissibleOriginalTestList 1 localTests := by
  intro t ht
  simp only [localTests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | hnil
  · exact OriginalLocalTest.admissible_of_fields 1
      (localTest (0 : I)) rfl
  · exact OriginalLocalTest.admissible_of_fields 1
      (localTest (1 : I)) rfl
  · exact OriginalLocalTest.admissible_of_fields 1
      (localTest (2 : I)) rfl
  · simp at hnil

theorem concrete_original_source_and_cofactors
    (d B : U) (hd : d ≠ 0) (a : U) (ha : a ≠ 0) :
    ∃ (H source R S : U),
      source = B + H * a ∧
      (∀ t, t ∈ localTests → t.Passes source) ∧
      (∀ i, testFamily.rightTail i ≠ 0) ∧
      1 = d * R + (source * d) * S := by
  obtain ⟨H, source, hsource, hgen, htail⟩ :=
    selected_source_passes B a ha
  refine ⟨H, source, d⁻¹, 0, hsource, ?_, htail, ?_⟩
  · intro t ht
    simp only [localTests, List.mem_cons, List.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | hnil
    · exact hgen (0 : I)
    · exact hgen (1 : I)
    · exact hgen (2 : I)
    · simp at hnil
  · simp [hd]

end SymplecticStafford.OriginalAffineDivisionOracle

#print axioms SymplecticStafford.OriginalAffineDivisionOracle.selected_source_passes
#print axioms SymplecticStafford.OriginalAffineDivisionOracle.concrete_original_source_and_cofactors
