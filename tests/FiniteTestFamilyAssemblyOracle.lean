import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic
import SymplecticStafford.Source.FiniteTestFamilyAssembly

/-!
# Independent oracle for retained finite-test assembly

This rational calibration uses two divisor-dependent local tests with
different offsets and tails.  The split coefficient pencil is the identity
(so its finite bad set is empty); the source-zero exception is still handled
by the producer.  The oracle inspects the retained generation fields and the
literal ordered assembly identity independently of the wrapper's theorem. -/

namespace SymplecticStafford.FiniteTestFamilyAssemblyOracle

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
  block := fun _ _ _ _ => 1
  base := fun _ _ => LinearMap.id
  direction := fun _ _ => 0
  retract := fun _ _ => LinearMap.id
  split := by intro B a; simp
  realization := by
    intro B a z
    rw [linearIndependent_unique_iff]
    constructor
    · intro h x y hxy
      simpa using hxy
    · intro h hz
      have hzeroone : (0 : ℚ) = 1 := h (by simpa [hz])
      exact zero_ne_one hzeroone

def tests (divisor : U) :
    List (FiniteDimensionalDivisionTest U K Unit Unit P V J) :=
  [finiteTest divisor 7 2 (by norm_num),
   finiteTest divisor (-4) 3 (by norm_num)]

theorem tests_admissible (divisor : U) :
    ∀ t, t ∈ tests divisor → t.localTest.Admissible divisor := by
  intro t ht
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | hnil
  · exact OriginalLocalTest.admissible_of_fields divisor _ rfl
  · exact OriginalLocalTest.admissible_of_fields divisor _ rfl
  · simp at hnil

theorem passes_iff_injective (divisor : U) :
    ∀ (t : FiniteDimensionalDivisionTest U K Unit Unit P V J),
      t ∈ tests divisor → ∀ z : K,
      t.localTest.Passes (1 + (RingHom.id K) z * (1 : U)) ↔
        Function.Injective (t.base 1 1 + z • t.direction 1 1) := by
  intro t ht z
  simp only [tests, List.mem_cons, List.mem_singleton] at ht
  rcases ht with rfl | rfl | hnil
  · dsimp [finiteTest, localTest, OriginalLocalTest.Passes]
    simp only [and_self, and_true, zero_smul, add_zero]
    constructor
    · intro _ x y hxy
      simpa using hxy
    · intro _
      trivial
  · dsimp [finiteTest, localTest, OriginalLocalTest.Passes]
    simp only [and_self, and_true, zero_smul, add_zero]
    constructor
    · intro _ x y hxy
      simpa using hxy
    · intro _
      trivial
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

theorem retained_fields (d : U) (hd : d ≠ 0) :
    ∀ t, t ∈ tests d →
      ∃ (source : U), source =
          (RetainedFiniteTestAssembly.of_certificate certificate).assembly.source hd ∧
        t.localTest.generation source t.localTest.offset t.localTest.rightTail ∧
        t.localTest.rightTail ≠ 0 := by
  intro t ht
  obtain ⟨hadm, hgen, htail⟩ :=
    (RetainedFiniteTestAssembly.of_certificate certificate).retained_tests d hd t ht
  exact ⟨(RetainedFiniteTestAssembly.of_certificate certificate).assembly.source hd,
    rfl, ⟨hgen, htail⟩⟩

theorem retained_source (d : U) (hd : d ≠ 0) :
    ∃ H source : U,
      source = (RetainedFiniteTestAssembly.of_certificate certificate).assembly.source hd ∧
      source = 1 + H * 1 ∧ source ≠ 0 := by
  let A := RetainedFiniteTestAssembly.of_certificate certificate
  exact ⟨A.multiplier d hd, A.assembly.source hd, rfl,
    A.affine_source d hd, A.source_nonzero d hd⟩

/- Altering either retained metadata field makes the local generation assertion
false.  These checks prevent the oracle from succeeding by dropping offsets or
right tails from the output contract. -/
example (source : U) :
    ¬ (finiteTest (1 : U) 7 2 (by norm_num)).localTest.generation
      source 8 2 := by
  simp [finiteTest, localTest]

example (source : U) :
    ¬ (finiteTest (1 : U) (-4) 3 (by norm_num)).localTest.generation
      source (-4) 0 := by
  simp [finiteTest, localTest]

theorem same_divisor : SymplecticStafford.SameDivisorS1 (R := U) :=
  (RetainedFiniteTestAssembly.of_certificate certificate).same_divisor

example (d : U) (hd : d ≠ 0) :
    ∃ source R S : U,
      1 = d * R + (source * d) * S := by
  let A := RetainedFiniteTestAssembly.of_certificate certificate
  exact ⟨A.assembly.source hd, (A.assembly.assemble hd).right₁,
    (A.assembly.assemble hd).right₂, (A.assembly.assemble hd).identity⟩

end SymplecticStafford.FiniteTestFamilyAssemblyOracle

#print axioms
  SymplecticStafford.FiniteTestFamilyAssemblyOracle.retained_fields
#print axioms
  SymplecticStafford.FiniteTestFamilyAssemblyOracle.retained_source
#print axioms SymplecticStafford.FiniteTestFamilyAssemblyOracle.same_divisor
