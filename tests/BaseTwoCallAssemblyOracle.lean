module

public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Induction.BaseTwoCallAssembly

@[expose] public section

/-!
# Independent oracle for base/two-call endpoint assembly

The oracle keeps a genuinely nonempty carried test list.  Given explicit
pointwise base and raw two-call hypotheses, the endpoint's `tests_pass` field
is inspected at that test, and the terminal result is checked in original
`U`.  The hypotheses are intentionally variables: this is an assembly oracle,
not a universal producer claim.
-/

namespace SymplecticStafford.Induction.BaseTwoCallAssemblyOracle

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

def parameters : CentralParameters Nat Nat where
  embed := fun z => z
  central := by intros; exact Nat.mul_comm _ _

def defect : Nat → Nat → List (LocalTest Nat Unit Unit) → Int :=
  fun d _ _ => if d = 1 then -1 else 0

def affine : AffineSource Nat := ⟨3, 2, by decide⟩

def carried : List (LocalTest Nat Unit Unit) := [carriedTest]

theorem carried_admissible : AdmissibleTestList 1 carried := by
  intro t ht
  simp only [carried, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst t
  exact carriedTest.admissible_of_fields 1 rfl

/- Explicit hypotheses are sufficient for the endpoint constructor. -/
noncomputable example
    (base : BaseProducer (U := Nat) 1 defect)
    (family : TwoCallDescentFamily parameters Unit 1 defect) :
    StrongPh 1 (1 + 1) defect := by
  exact strongPh_fin_index_of_base_and_two_call_descent base family

/- The retained test is non-vacuous: it is an actual member of the carried
list, and the endpoint witness proves its generation predicate. -/
noncomputable example
    (base : BaseProducer (U := Nat) 1 defect)
    (family : TwoCallDescentFamily parameters Unit 1 defect) :
    carriedTest.generation
      (strongPh_fin_index_of_base_and_two_call_descent base family
        1 (by decide) affine carried carried_admissible).source := by
  have w :=
    (strongPh_fin_index_of_base_and_two_call_descent base family
      1 (by decide) affine carried carried_admissible)
  exact w.tests_pass carriedTest (by simp [carried])

def zeroExtraction : ∀ {d f : Nat} {Ω : List (LocalTest Nat Unit Unit)},
    defect d f Ω ≤ -1 → OriginalCofactors d f := by
  intro d f Ω h
  by_cases hd : d = 1
  · subst d
    refine {R := 1, S := 0, identity := ?_}
    simp
  · simp [defect, hd] at h

noncomputable example
    (base : BaseProducer (U := Nat) 1 defect)
    (family : TwoCallDescentFamily parameters Unit 1 defect) :
    OriginalCofactors 1
      (strongPh_fin_index_of_base_and_two_call_descent base family
        1 (by decide) affine carried carried_admissible).source := by
  exact terminal_cofactors_of_base_and_two_call_descent base family
    zeroExtraction 1 (by decide) affine carried carried_admissible

end SymplecticStafford.Induction.BaseTwoCallAssemblyOracle

#print axioms SymplecticStafford.Induction.BaseTwoCallAssemblyOracle.zeroExtraction
#print axioms SymplecticStafford.Induction.strongPh_fin_index_of_base_and_two_call_descent
