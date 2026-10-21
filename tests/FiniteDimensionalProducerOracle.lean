module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Tactic
public import SymplecticStafford.Source.FiniteDimensionalProducer

@[expose] public section

/-!
# Independent oracle for the split finite-dimensional M06 producer

The coefficient space and target are both one-dimensional over `ℚ`.  The
realized pencil is the genuinely singular pencil `1 + z`, while two local
tests retain different offsets and right tails.  The source-zero exception is
also removed, so the oracle exercises both finite bad-set arguments in the
producer.
-/

namespace SymplecticStafford.FiniteDimensionalProducerOracle

open SymplecticStafford.Source

abbrev U := ℚ
abbrev K := ℚ
abbrev P := ℚ
abbrev V := ℚ
abbrev J := Unit

def localTest (offset : Int) (tail : U) (htail : tail ≠ 0) :
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
  generation := fun source gotOffset gotTail =>
    source ≠ 0 ∧ gotOffset = offset ∧ gotTail = tail

def finiteTest (offset : Int) (tail : U) (htail : tail ≠ 0) :
    FiniteDimensionalDivisionTest U K Unit Unit P V J where
  localTest := localTest offset tail htail
  block := fun _ _ z _ => 1 + z
  base := fun _ _ => LinearMap.id
  direction := fun _ _ => LinearMap.id
  retract := fun _ _ => LinearMap.id
  split := by
    intro B a
    simp
  realization := by
    intro B a z
    rw [linearIndependent_unique_iff]
    constructor
    · intro h
      intro x y hxy
      change x + z * x = y + z * y at hxy
      have hxy' : (1 + z) * x = (1 + z) * y := by
        calc
          (1 + z) * x = x + z * x := by ring
          _ = y + z * y := hxy
          _ = (1 + z) * y := by ring
      exact mul_left_cancel₀ h hxy'
    · intro h
      intro hz
      have hzeroone : (0 : ℚ) = 1 := h (by simp [hz])
      exact zero_ne_one hzeroone

def tests : List (FiniteDimensionalDivisionTest U K Unit Unit P V J) :=
  [finiteTest 7 2 (by norm_num), finiteTest (-4) 3 (by norm_num)]

theorem tests_admissible :
    ∀ t, t ∈ tests → t.localTest.Admissible (1 : U) := by
  intro t ht
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | hnil
  · exact OriginalLocalTest.admissible_of_fields 1 _ rfl
  · exact OriginalLocalTest.admissible_of_fields 1 _ rfl
  · simp at hnil

theorem passes_iff_injective :
    ∀ (t : FiniteDimensionalDivisionTest U K Unit Unit P V J), t ∈ tests →
      ∀ z : K,
        t.localTest.Passes (1 + (RingHom.id K) z * (1 : U)) ↔
          Function.Injective (t.base 1 1 + z • t.direction 1 1) := by
  intro t ht z
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | hnil
  · dsimp [finiteTest, localTest, OriginalLocalTest.Passes]
    change ((1 + z * 1 : ℚ) ≠ 0 ∧ (7 : Int) = 7 ∧ (2 : ℚ) = 2) ↔
      Function.Injective ((LinearMap.id : ℚ →ₗ[ℚ] ℚ) +
        z • (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
    simp only [mul_one]
    simp only [eq_self, and_true]
    constructor
    · intro h
      intro x y hxy
      change x + z * x = y + z * y at hxy
      have hxy' : (1 + z) * x = (1 + z) * y := by
        calc
          (1 + z) * x = x + z * x := by ring
          _ = y + z * y := hxy
          _ = (1 + z) * y := by ring
      exact mul_left_cancel₀ h hxy'
    · intro h
      intro hz
      have hzeroone : (0 : ℚ) = 1 := h (by simp [hz])
      exact zero_ne_one hzeroone
  · dsimp [finiteTest, localTest, OriginalLocalTest.Passes]
    change ((1 + z * 1 : ℚ) ≠ 0 ∧ (-4 : Int) = -4 ∧ (3 : ℚ) = 3) ↔
      Function.Injective ((LinearMap.id : ℚ →ₗ[ℚ] ℚ) +
        z • (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
    simp only [mul_one]
    simp only [eq_self, and_true]
    constructor
    · intro h
      intro x y hxy
      change x + z * x = y + z * y at hxy
      have hxy' : (1 + z) * x = (1 + z) * y := by
        calc
          (1 + z) * x = x + z * x := by ring
          _ = y + z * y := hxy
          _ = (1 + z) * y := by ring
      exact mul_left_cancel₀ h hxy'
    · intro h
      intro hz
      have hzeroone : (0 : ℚ) = 1 := h (by simp [hz])
      exact zero_ne_one hzeroone
  · simp at hnil

theorem selected_source :
    ∃ (H source : U),
      source = 1 + H * (1 : U) ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests → t.localTest.Admissible (1 : U)) ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.localTest.rightTail ≠ 0) := by
  exact exists_original_affine_source_of_finite_dimensional_list
    (RingHom.id K) Function.injective_id (1 : U) tests 1 1 one_ne_zero
    tests_admissible passes_iff_injective

example : ∃ H source : U, source = 1 + H * 1 ∧ source ≠ 0 := by
  obtain ⟨H, source, hsource, hne, -, -, -⟩ := selected_source
  exact ⟨H, source, hsource, hne⟩

end SymplecticStafford.FiniteDimensionalProducerOracle

#print axioms
  SymplecticStafford.FiniteDimensionalProducerOracle.selected_source
