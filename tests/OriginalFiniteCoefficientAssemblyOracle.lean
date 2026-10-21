module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Tactic
public import SymplecticStafford.Source.OriginalFiniteCoefficientAssembly

@[expose] public section

/-!
# Independent oracle for divisor-indexed finite-coefficient assembly

This oracle supplies, for every nonzero rational divisor, a concrete source
package over the top subring of `ℚ`.  The tests have distinct offsets and
right tails, while the selected source is shared by all tests for that
divisor.  The assembly wrapper is then consumed at two divisors and its
literal cofactor identities are checked.
-/

namespace SymplecticStafford.OriginalFiniteCoefficientAssemblyOracle

open SymplecticStafford.Source

abbrev U := ℚ
abbrev K := ℚ
abbrev LD := Unit
abbrev CD := Unit

def algebra : FiniteCoefficientAlgebra U K where
  carrier := ⊤
  embedding := RingHom.id K
  embedding_injective := Function.injective_id
  scalar_mem := by simp

def localTest (d : U) (offset : Int) (tail : U) (htail : tail ≠ 0) :
    OriginalLocalTest U LD CD where
  targetDivisor := d
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
    source = 1 ∧ gotOffset = offset ∧ gotTail = tail

def tests (d : U) : List (OriginalLocalTest U LD CD) :=
  [localTest d 7 2 (by norm_num), localTest d (-4) 3 (by norm_num),
   localTest d 12 5 (by norm_num)]

def directions (_d : U) : List U := [1, 2]

def background (_d : U) : U := 1
def affineTail (_d : U) : U := 1

theorem tests_admissible (d : U) (hd : d ≠ 0) :
    ∀ t, t ∈ tests d → t.Admissible d := by
  intro t ht
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | hnil
  · exact OriginalLocalTest.admissible_of_fields d _ rfl
  · exact OriginalLocalTest.admissible_of_fields d _ rfl
  · exact OriginalLocalTest.admissible_of_fields d _ rfl
  · simp at hnil

def selected (d : U) (hd : d ≠ 0) :
    OriginalFiniteCoefficientSource algebra d (background d)
      (affineTail d) (tests d) (directions d) := by
  have h1 : (1 : U) ∈ algebra.carrier := by simp [algebra]
  have h2 : (2 : U) ∈ algebra.carrier := by simp [algebra]
  have hzero : (0 : K) ∈ algebra.carrier := by simp [algebra]
  let w : AssemblyWitness d 1 :=
    { right₁ := d⁻¹
      right₂ := 0
      identity := by simp [hd] }
  refine {
    coefficients := [0, 0]
    coefficients_length := by simp [directions]
    coefficient_mem := by intro z hz; simp [algebra]
    directions_mem := by
      intro h hh
      have hh' : h = 1 ∨ h = 2 := by simpa [directions] using hh
      rcases hh' with h1' | h2'
      · simp [h1']
      · simp [h2']
    multiplier := 0
    source := 1
    source_eq := by simp [background, affineTail]
    multiplier_eq := by simp [weightedCombination, algebra, directions]
    background_mem := by simp [background, algebra]
    tail_mem := by simp [affineTail, algebra]
    multiplier_mem := hzero
    source_mem := h1
    source_nonzero := by norm_num
    admissible := tests_admissible d hd
    passes := ?_
    rightTail_nonzero := ?_
    assembly := w
    cofactor₁_mem := by simp [algebra]
    cofactor₂_mem := by simp [algebra] }
  · intro t ht
    simp only [tests, List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | hnil
    · norm_num [OriginalLocalTest.Passes, localTest]
    · norm_num [OriginalLocalTest.Passes, localTest]
    · norm_num [OriginalLocalTest.Passes, localTest]
    · simp at hnil
  · intro t ht
    simp only [tests, List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | hnil
    · norm_num [localTest]
    · norm_num [localTest]
    · norm_num [localTest]
    · simp at hnil

def assembly : OriginalFiniteCoefficientAssembly algebra background affineTail
    tests directions :=
  OriginalFiniteCoefficientAssembly.of_selected algebra background affineTail
    tests directions
    (by intro d hd; simp [background])
    (by intro d hd; simp [affineTail])
    (by intro d; simp [background, algebra])
    (by intro d; simp [affineTail, algebra])
    (by
      intro d h hh
      have hh' : h = 1 ∨ h = 2 := by simpa [directions] using hh
      rcases hh' with h1 | h2
      · simp [h1, algebra]
      · simp [h2, algebra])
    (by intro d hd; exact ⟨selected d hd⟩)

theorem selected_source_is_original (d : U) (hd : d ≠ 0) :
    (assembly.selectedSource hd).source ∈ algebra.carrier ∧
      (assembly.selectedSource hd).source ≠ 0 := by
  exact ⟨assembly.selected_source_mem hd, assembly.selected_source_nonzero hd⟩

theorem selected_tests_and_cofactors (d : U) (hd : d ≠ 0) :
    (∀ t, t ∈ tests d → t.Passes (assembly.selectedSource hd).source) ∧
      (assembly.selectedSource hd).assembly.right₁ ∈ algebra.carrier ∧
      (assembly.selectedSource hd).assembly.right₂ ∈ algebra.carrier := by
  refine ⟨?_, assembly.selected_cofactor₁_mem hd,
    assembly.selected_cofactor₂_mem hd⟩
  intro t ht
  exact assembly.selected_test_pass hd ht

theorem literal_identity_at_two :
    (1 : U) = 2 * (assembly.toDivisorIndexedAssembly.assemble
      (d := 2) (by norm_num)).right₁ +
      (assembly.toDivisorIndexedAssembly.source (d := 2) (by norm_num) * 2) *
        (assembly.toDivisorIndexedAssembly.assemble
          (d := 2) (by norm_num)).right₂ := by
  exact assembly.selected_exact_recombination (by norm_num)

example : SymplecticStafford.SameDivisorS1 (R := U) :=
  assembly.same_divisor

end SymplecticStafford.OriginalFiniteCoefficientAssemblyOracle

#print axioms
  SymplecticStafford.OriginalFiniteCoefficientAssemblyOracle.literal_identity_at_two
#print axioms
  SymplecticStafford.OriginalFiniteCoefficientAssemblyOracle.selected_tests_and_cofactors
