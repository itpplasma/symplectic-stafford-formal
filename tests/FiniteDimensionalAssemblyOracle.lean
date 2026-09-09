import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic
import SymplecticStafford.Source.FiniteDimensionalAssembly

/-!
# Independent oracle for divisor-indexed finite-dimensional assembly

The same split one-dimensional pencil is used for every divisor, while the
assembly callback receives the selected source and returns literal cofactors
in the original ring.  The two tests retain distinct offsets and tails. -/

namespace SymplecticStafford.FiniteDimensionalAssemblyOracle

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
  generation := fun source gotOffset gotTail =>
    source ≠ 0 ∧ gotOffset = offset ∧ gotTail = tail

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

def tests (divisor : U) : List (FiniteDimensionalDivisionTest U K Unit Unit P V J) :=
  [finiteTest divisor 7 2 (by norm_num), finiteTest divisor (-4) 3 (by norm_num)]

theorem tests_admissible (divisor : U) :
    ∀ t, t ∈ tests divisor → t.localTest.Admissible divisor := by
  intro t ht
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | hnil
  · exact OriginalLocalTest.admissible_of_fields divisor _ rfl
  · exact OriginalLocalTest.admissible_of_fields divisor _ rfl
  · simp at hnil

theorem passes_iff_injective (divisor : U) :
      ∀ (t : FiniteDimensionalDivisionTest U K Unit Unit P V J), t ∈ tests divisor →
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
    simp only [mul_one, and_true]
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
  · dsimp [finiteTest, localTest, OriginalLocalTest.Passes]
    change ((1 + z * 1 : ℚ) ≠ 0 ∧ (-4 : Int) = -4 ∧ (3 : ℚ) = 3) ↔
      Function.Injective ((LinearMap.id : ℚ →ₗ[ℚ] ℚ) +
        z • (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
    simp only [mul_one, and_true]
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
  · simp at hnil

def certificate : FiniteDimensionalDivisorCertificate U K Unit Unit P V J where
  scalarEmbedding := RingHom.id K
  scalarEmbedding_injective := Function.injective_id
  tests := tests
  background := fun _ => 1
  affineTail := fun _ => 1
  affineTail_nonzero := by intro d hd; norm_num
  admissible := by intro d hd; exact tests_admissible d
  pass_iff_injective := by
    intro d hd
    simpa using passes_iff_injective d
  assemble := by
    intro d hd H source hsource hne hpass
    exact AssemblyWitness.of_divisionRing hd

theorem concrete_divisor_assembly :
    Nonempty (DivisorIndexedAssembly U) :=
  ⟨certificate.toDivisorIndexedAssembly⟩

theorem concrete_same_divisor :
    SymplecticStafford.SameDivisorS1 (R := U) :=
  certificate.same_divisor

/- The callback's output is inspected directly: both cofactors are original
 rational values and the source occurs in the second ordered factor. -/
example (d : U) (hd : d ≠ 0) :
    ∃ source R S : U,
      1 = d * R + (source * d) * S := by
  let A : DivisorIndexedAssembly U := certificate.toDivisorIndexedAssembly
  exact ⟨A.source hd, (A.assemble hd).right₁,
    (A.assemble hd).right₂, (A.assemble hd).identity⟩

end SymplecticStafford.FiniteDimensionalAssemblyOracle

#print axioms
  SymplecticStafford.FiniteDimensionalAssemblyOracle.concrete_divisor_assembly
#print axioms
  SymplecticStafford.FiniteDimensionalAssemblyOracle.concrete_same_divisor
