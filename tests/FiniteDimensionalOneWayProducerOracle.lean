import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic
import SymplecticStafford.Source.FiniteDimensionalOneWayProducer

/-!
# Independent oracle for the one-way finite-dimensional bridge

The local pass predicate keeps only its offset and right tail, so it also
passes at the singular pencil parameter `z = -1`.  Thus the converse
`Pass -> Injective` is false, while the required implication
`Injective -> Pass` is immediate.  The source-zero parameter is a separate
finite exception and is removed by the selector.
-/

namespace SymplecticStafford.FiniteDimensionalOneWayProducerOracle

open SymplecticStafford.Source

abbrev U := ℚ
abbrev K := ℚ
abbrev P := ℚ
abbrev V := ℚ
abbrev J := Unit

def localTest (divisor : U) (offset : Int) (tail : U) (htail : tail ≠ 0) :
    OriginalLocalTest U Unit Unit where
  targetDivisor := divisor
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

def finiteTest (divisor : U) (offset : Int) (tail : U) (htail : tail ≠ 0) :
    FiniteDimensionalDivisionTest U K Unit Unit P V J where
  localTest := localTest divisor offset tail htail
  block := fun _ _ z _ => 1 + z
  base := fun _ _ => LinearMap.id
  direction := fun _ _ => LinearMap.id
  retract := fun _ _ => LinearMap.id
  split := by intro B a; simp
  realization := by
    intro B a z
    rw [linearIndependent_unique_iff]
    constructor
    · intro h x y hxy
      change x + z * x = y + z * y at hxy
      have hxy' : (1 + z) * x = (1 + z) * y := by
        calc
          (1 + z) * x = x + z * x := by ring
          _ = y + z * y := hxy
          _ = (1 + z) * y := by ring
      exact mul_left_cancel₀ h hxy'
    · intro h hz
      have hzeroone : (0 : ℚ) = 1 := h (by simp [hz])
      exact zero_ne_one hzeroone

def tests (divisor : U) :
    List (FiniteDimensionalDivisionTest U K Unit Unit P V J) :=
  [finiteTest divisor 23 7 (by norm_num)]

theorem tests_admissible (divisor : U) :
    ∀ t, t ∈ tests divisor → t.localTest.Admissible divisor := by
  intro t ht
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | hnil
  · exact OriginalLocalTest.admissible_of_fields divisor _ rfl
  · simp at hnil

theorem passes_of_injective (divisor : U) :
    ∀ (t : FiniteDimensionalDivisionTest U K Unit Unit P V J),
      t ∈ tests divisor → ∀ z : K,
      Function.Injective (t.base 0 1 + z • t.direction 0 1) →
        t.localTest.Passes (0 + (RingHom.id K) z * (1 : U)) := by
  intro t ht z hinj
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | hnil
  · simp [finiteTest, localTest, OriginalLocalTest.Passes]
  · simp at hnil

/- The converse genuinely fails: the test passes at `-1`, but the realized
pencil is the zero map. -/
example : ¬ ((finiteTest (1 : U) 23 7 (by norm_num)).localTest.Passes
      (0 + (-1 : K) * (1 : U)) ↔
    Function.Injective
      ((LinearMap.id : ℚ →ₗ[ℚ] ℚ) + (-1 : ℚ) •
        (LinearMap.id : ℚ →ₗ[ℚ] ℚ))) := by
  intro hiff
  have hpass : (finiteTest (1 : U) 23 7 (by norm_num)).localTest.Passes
      (0 + (-1 : K) * (1 : U)) := by
    simp [finiteTest, localTest, OriginalLocalTest.Passes]
  have hinj := hiff.mp hpass
  have hzeroone : (0 : ℚ) = 1 := hinj (by simp)
  exact zero_ne_one hzeroone

theorem selected_source (d : U) (hd : d ≠ 0) :
    ∃ (H source : U),
      source = 0 + H * 1 ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests d → t.localTest.Admissible d) ∧
      (∀ t, t ∈ tests d → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests d → t.localTest.rightTail ≠ 0) := by
  exact exists_original_affine_source_of_finite_dimensional_list_of_injective
    (RingHom.id K) Function.injective_id d (tests d) 0 1 one_ne_zero
    (tests_admissible d) (passes_of_injective d)

example (d : U) (hd : d ≠ 0) :
    ∃ source R S : U,
      1 = d * R + (source * d) * S := by
  obtain ⟨H, source, hsource, hne, -, -, -⟩ := selected_source d hd
  exact ⟨source, d⁻¹, 0, by simp [hd]⟩

end SymplecticStafford.FiniteDimensionalOneWayProducerOracle

#print axioms
  SymplecticStafford.FiniteDimensionalOneWayProducerOracle.selected_source
