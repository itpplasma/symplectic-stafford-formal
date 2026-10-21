module

public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Induction.NatSupportRemoval

@[expose] public section

/-!
# Independent oracle for the concrete non-vacuous two-call step

The list contains an actual admissible local test.  Its generation predicate
is true, so the retention conclusion is checked at a real carried element;
the support and strict-removal laws are supplied by `nat_two_call_data`'s
construction rather than by an output-witness field.
-/

namespace SymplecticStafford.Induction.NatSupportRemovalOracle

open SymplecticStafford.Induction

def carriedTest : LocalTest Nat Unit Unit where
  targetDivisor := 1
  localization := ()
  cyclicModule := ()
  canonicalGenerator := ()
  rightTail := 1
  offset := 0
  localization_spec := True
  localization_spec_proof := True.intro
  finite_length_cyclic_spec := True
  finite_length_cyclic_proof := True.intro
  canonical_generator_spec := True
  canonical_generator_spec_proof := True.intro
  rightTail_nonzero := by decide
  generation := fun _ => True

def carried : List (LocalTest Nat Unit Unit) := [carriedTest]

theorem carried_admissible : AdmissibleTestList 1 carried := by
  intro t ht
  simp only [carried, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst t
  exact carriedTest.admissible_of_fields 1 rfl

def affine : AffineSource Nat := ⟨0, 1, by decide⟩

/- The lower contract and the two exact source facts are explicit hypotheses;
they are the remaining local input, not hidden in the oracle. -/
noncomputable example
    (lower : StrongPh 1 1 (natRemovalDefect (v := Unit) (w := Unit)))
    (hOld : (lower 1 (by decide) affine carried carried_admissible).source = 0)
    (hNew :
      (lower 1 (by decide) (homogeneousAffine affine.a affine.a_nonzero)
        carried carried_admissible).source ≠ 0) :
    StrongPhWitness 1 2 (natRemovalDefect (v := Unit) (w := Unit))
      1 affine carried := by
  apply nat_two_call_witness () lower affine carried carried_admissible hOld hNew
  intro z t ht hF hG
  trivial

noncomputable example
    (lower : StrongPh 1 1 (natRemovalDefect (v := Unit) (w := Unit)))
    (hOld : (lower 1 (by decide) affine carried carried_admissible).source = 0)
    (hNew :
      (lower 1 (by decide) (homogeneousAffine affine.a affine.a_nonzero)
        carried carried_admissible).source ≠ 0) :
    carriedTest.generation
      (nat_two_call_witness () lower affine carried carried_admissible hOld hNew
        (by
          intro z t ht hF hG
          trivial)).source := by
  exact (nat_two_call_witness () lower affine carried carried_admissible hOld hNew
    (by
      intro z t ht hF hG
      trivial)).tests_pass carriedTest (by simp [carried])

end SymplecticStafford.Induction.NatSupportRemovalOracle

#print axioms SymplecticStafford.Induction.nat_two_call_data
#print axioms SymplecticStafford.Induction.nat_two_call_witness
