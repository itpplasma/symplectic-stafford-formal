import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic
import SymplecticStafford.Source.OriginalDivisionProducer

/-!
Independent oracle for the actual finite-top M06 bridge.  This does not
provide `passes_of_pencil_ne_zero`: cyclicity is derived from a concrete
division-ring top bridge and an original-U additive/scalar map.  Three tests
retain distinct offsets and tails, and the selected source is proved nonzero.
-/

namespace SymplecticStafford.ActualOriginalDivisionProducerOracle

open SymplecticStafford.Source
open SymplecticStafford.FiniteLength

abbrev U := ℚ
abbrev K := ℚ
abbrev R := ℚ
abbrev M := ℚ
abbrev I := Unit
abbrev D := fun _ : I => ℚ

theorem rational_right_cyclic_iff (x : ℚ) :
    RightCyclic (R := ℚ) x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    obtain ⟨r, hr⟩ := h 1
    subst x
    simp at hr
  · intro hx y
    refine ⟨MulOpposite.op (x⁻¹ * y), ?_⟩
    change x * (x⁻¹ * y) = y
    simp [hx]

def rationalBridge : CyclicTopBridge (R := R) (M := M)
    (D := D) (fun _ => RingHom.id K) where
  top :=
    { toFun := fun x _ => x
      map_zero' := by rfl
      map_add' := by intro x y; funext i; rfl }
  map_smul := by
    intro z m i
    change z * m = z * m
    rfl
  reflects_generation := by
    intro x hx
    apply (rational_right_cyclic_iff x).2
    exact (semisimple_top_criterion _).1 hx ()

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

def actualTest (offset : Int) (tail : U) (htail : tail ≠ 0) :
    ActualOriginalDivisionTest U K Unit Unit R M I D
      (RingHom.id K) (fun _ => RingHom.id K) where
  localTest := localTest offset tail htail
  bridge := rationalBridge
  sourceMap := AddMonoidHom.id U
  sourceMap_scalar := by
    intro z x
    change z * x = z * x
    rfl
  passes_iff_cyclic := by
    intro source
    change source ≠ 0 ∧ _ ∧ _ ↔ _
    constructor
    · intro h
      exact (rational_right_cyclic_iff source).2 h.1
    · intro h
      exact ⟨(rational_right_cyclic_iff source).1 h, rfl, rfl⟩

def tests : List (ActualOriginalDivisionTest U K Unit Unit R M I D
    (RingHom.id K) (fun _ => RingHom.id K)) :=
  [actualTest 7 2 (by norm_num),
   actualTest (-4) 3 (by norm_num),
   actualTest 12 5 (by norm_num)]

theorem tests_admissible :
    ∀ t, t ∈ tests → t.localTest.Admissible (1 : U) := by
  intro t ht
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | hnil
  · exact OriginalLocalTest.admissible_of_fields 1 _ rfl
  · exact OriginalLocalTest.admissible_of_fields 1 _ rfl
  · exact OriginalLocalTest.admissible_of_fields 1 _ rfl
  · simp at hnil

theorem initial_tops_nonzero :
    ∀ t, t ∈ tests → ∀ i, t.bridge.top (t.sourceMap (1 : U)) i ≠ 0 := by
  intro t ht i
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | hnil
  · norm_num [actualTest, rationalBridge, localTest]
  · norm_num [actualTest, rationalBridge, localTest]
  · norm_num [actualTest, rationalBridge, localTest]
  · simp at hnil

theorem selected_actual_source (a : U) (ha : a ≠ 0) :
    ∃ (H source : U),
      source = 1 + H * a ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests → t.localTest.Admissible (1 : U)) ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.localTest.rightTail ≠ 0) := by
  exact exists_original_affine_source_of_actual_list
    (RingHom.id K) Function.injective_id
    (fun _ => RingHom.id K)
    (fun _ => Function.injective_id) (1 : U) tests 1 a ha
    tests_admissible initial_tops_nonzero

theorem selected_finite_direction_source :
    ∃ (H source : U) (coefficients : List K),
      source = 1 + H * 2 ∧ source ≠ 0 ∧
      coefficients.length = ([1, -2, 3] : List U).length ∧
      H = weightedCombination (RingHom.id K) ([1, -2, 3] : List U) coefficients ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) := by
  obtain ⟨H, source, coefficients, hsource, hne, hlen, hcomb, -, hpasses, -⟩ :=
    exists_original_affine_source_of_actual_directions
      (RingHom.id K) Function.injective_id
      (fun _ => RingHom.id K) (fun _ => Function.injective_id)
      (1 : U) tests ([1, -2, 3] : List U) 1 2 (by norm_num) (by norm_num)
      tests_admissible initial_tops_nonzero
  exact ⟨H, source, coefficients, hsource, hne, hlen, hcomb, hpasses⟩

example : ∃ H source : U, source = 1 + H * 2 ∧ source ≠ 0 := by
  obtain ⟨H, source, hsource, hne, -, -, -⟩ :=
    selected_actual_source 2 (by norm_num)
  exact ⟨H, source, hsource, hne⟩

end SymplecticStafford.ActualOriginalDivisionProducerOracle

#print axioms
  SymplecticStafford.ActualOriginalDivisionProducerOracle.selected_actual_source
#print axioms
  SymplecticStafford.ActualOriginalDivisionProducerOracle.selected_finite_direction_source
