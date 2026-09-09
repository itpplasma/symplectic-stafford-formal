import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic
import SymplecticStafford.Source.OriginalFiniteCoefficientSource

/-!
# Independent oracle for the finite original-coefficient source package

The oracle uses three actual tests over `ℚ`, with distinct offsets and right
tails, and a concrete original-ring assembly callback.  The selected source
is obtained from the finite-direction theorem, then consumed through the new
package's membership, retention, and exact-recombination projections.
-/

namespace SymplecticStafford.OriginalFiniteCoefficientSourceOracle

open SymplecticStafford.Source
open SymplecticStafford.FiniteLength

abbrev U := ℚ
abbrev K := ℚ
abbrev R := ℚ
abbrev M := ℚ
abbrev I := Unit
abbrev D (_ : I) := ℚ

def algebra : FiniteCoefficientAlgebra U K where
  carrier := ⊤
  embedding := RingHom.id K
  embedding_injective := Function.injective_id
  scalar_mem := by simp

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

def bridge : CyclicTopBridge (R := R) (M := M)
    (D := D) (fun _ => RingHom.id K) where
  top :=
    { toFun := fun x _ => x
      map_zero' := by rfl
      map_add' := by intro x y; funext i; simp }
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
  bridge := bridge
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

theorem tests_initially_cyclic :
    ∀ t, t ∈ tests → ∀ i, t.bridge.top (t.sourceMap (1 : U)) i ≠ 0 := by
  intro t ht i
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | hnil
  · norm_num [actualTest, bridge, localTest]
  · norm_num [actualTest, bridge, localTest]
  · norm_num [actualTest, bridge, localTest]
  · simp at hnil

theorem selected_package :
    Nonempty (OriginalFiniteCoefficientSource algebra (1 : U) 1 2
      (tests.map (fun t => t.localTest)) [1, 2]) := by
  apply exists_original_finite_coefficient_source_of_actual_directions
    algebra (fun _ => RingHom.id K) (fun _ => Function.injective_id)
    1 tests [1, 2] 1 2 (by norm_num) (by norm_num)
    (by simp) (by simp)
    (by
      intro h hh
      have hh' : h = 1 ∨ h = 2 := by simpa using hh
      rcases hh' with h1 | h2
      · simp [h1]
      · simp [h2])
    tests_admissible tests_initially_cyclic
  intro H source hsource hne hpasses
  refine ⟨{ right₁ := 1, right₂ := 0, identity := ?_ }, ?_, ?_⟩
  · simp
  · simp
  · simp

theorem package_retains_finite_control :
    ∃ S : OriginalFiniteCoefficientSource algebra (1 : U) 1 2
        (tests.map (fun t => t.localTest)) [1, 2],
      S.coefficients.length = 2 ∧
      (∀ z, z ∈ S.coefficients → algebra.embedding z ∈ algebra.carrier) ∧
      (∀ h, h ∈ ([1, 2] : List U) → h ∈ algebra.carrier) := by
  obtain ⟨S⟩ := selected_package
  refine ⟨S, ?_, S.coefficient_mem, S.directions_mem⟩
  simpa using S.coefficients_length

theorem package_retains_one_source_and_all_tests :
    ∃ S : OriginalFiniteCoefficientSource algebra (1 : U) 1 2
        (tests.map (fun t => t.localTest)) [1, 2],
      S.source = 1 + S.multiplier * 2 ∧ S.source ≠ 0 ∧
      (∀ t, t ∈ tests.map (fun t => t.localTest) → t.Passes S.source) ∧
      (∀ t, t ∈ tests.map (fun t => t.localTest) → t.rightTail ≠ 0) := by
  obtain ⟨S⟩ := selected_package
  refine ⟨S, S.source_eq, S.source_nonzero, S.passes, S.rightTail_nonzero⟩

theorem package_has_exact_original_recombination :
    ∃ S : OriginalFiniteCoefficientSource algebra (1 : U) 1 2
        (tests.map (fun t => t.localTest)) [1, 2],
      (1 : U) = 1 * S.assembly.right₁ +
        (S.source * 1) * S.assembly.right₂ ∧
      S.assembly.right₁ ∈ algebra.carrier ∧
      S.assembly.right₂ ∈ algebra.carrier := by
  obtain ⟨S⟩ := selected_package
  refine ⟨S, S.exact_recombination, S.cofactor₁_mem, S.cofactor₂_mem⟩

example :
    Nonempty (TestedAssemblyWitness (1 : U) 1 2
      (tests.map (fun t => t.localTest))) := by
  obtain ⟨S⟩ := selected_package
  exact ⟨S.to_tested_assembly⟩

end SymplecticStafford.OriginalFiniteCoefficientSourceOracle

#print axioms
  SymplecticStafford.OriginalFiniteCoefficientSourceOracle.selected_package
#print axioms
  SymplecticStafford.OriginalFiniteCoefficientSourceOracle.package_has_exact_original_recombination
