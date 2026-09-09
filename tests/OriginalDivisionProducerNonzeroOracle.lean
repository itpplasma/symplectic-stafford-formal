import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic
import SymplecticStafford.Source.OriginalDivisionProducer

/-!
Independent oracle for the strengthened M06 selector.  The three tests have
distinct division pencils, offsets, and right tails.  Their local predicates
consume the source-independent certificate fields, while the theorem under
test separately proves that the selected original-ring source is nonzero.
-/

namespace SymplecticStafford.OriginalDivisionProducerNonzeroOracle

open SymplecticStafford.Source

abbrev U := ℚ
abbrev K := ℚ

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
  generation := fun _ gotOffset gotTail =>
    gotOffset = offset ∧ gotTail = tail

def certifiedTest (v u : U) (hv : v ≠ 0)
    (offset : Int) (tail : U) (htail : tail ≠ 0) :
    CertifiedOriginalDivisionTest (K := K) (d := (1 : U)) Unit Unit where
  test := {
    localTest := localTest offset tail htail
    vCoeff := v
    uCoeff := u
    vCoeff_ne_zero := hv
    passes_of_pencil_ne_zero := by
      intro ι B a z hp
      exact ⟨rfl, rfl⟩ }
  admissible := by
    exact OriginalLocalTest.admissible_of_fields 1 _ rfl

def tests : List (CertifiedOriginalDivisionTest
    (K := K) (d := (1 : U)) Unit Unit) :=
  [certifiedTest 1 1 (by norm_num) 7 2 (by norm_num),
   certifiedTest 2 (-1) (by norm_num) (-4) 3 (by norm_num),
   certifiedTest 3 2 (by norm_num) 12 5 (by norm_num)]

theorem selected_source_is_nonzero (B a : U) (ha : a ≠ 0) :
    ∃ (H source : U),
      source = B + H * a ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests → t.test.localTest.Admissible (1 : U)) ∧
      (∀ t, t ∈ tests → t.test.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.test.localTest.rightTail ≠ 0) := by
  exact exists_original_affine_source_of_certified_list
    (RingHom.id K) Function.injective_id (1 : U) tests B a ha

theorem scalar_avoids_carried_exception (B a : U) (ha : a ≠ 0) :
    ∃ z : K, z ∉ Set.singleton (2 : K) ∧
      z ∉ affineExceptional (RingHom.id K)
        (tests.map (fun t => OriginalDivisionTest.toAffineDivisionTest t.test)) ∧
      B + z * a ≠ 0 := by
  exact exists_scalar_avoiding_affine_and_source
    (RingHom.id K) Function.injective_id
    (tests.map (fun t => OriginalDivisionTest.toAffineDivisionTest t.test)) B a ha
    (Set.singleton (2 : K)) (Set.finite_singleton 2)

example (B a : U) (ha : a ≠ 0) :
    ∃ source : U, source = B + (1 : U) * a ∨ source ≠ 0 := by
  obtain ⟨H, source, hsource, hne, -, -, -⟩ := selected_source_is_nonzero B a ha
  exact ⟨source, Or.inr hne⟩

/- The source-zero assertion is genuinely consumed: it is not available from
the old list theorem, whose local generation predicates may ignore source. -/
example (B a : U) (ha : a ≠ 0) :
    ∃ H source : U, source = B + H * a ∧ source ≠ 0 := by
  obtain ⟨H, source, hsource, hne, -, -, -⟩ := selected_source_is_nonzero B a ha
  exact ⟨H, source, hsource, hne⟩

end SymplecticStafford.OriginalDivisionProducerNonzeroOracle

#print axioms
  SymplecticStafford.OriginalDivisionProducerNonzeroOracle.selected_source_is_nonzero
#print axioms
  SymplecticStafford.OriginalDivisionProducerNonzeroOracle.scalar_avoids_carried_exception
