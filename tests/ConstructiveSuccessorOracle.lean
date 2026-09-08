import SymplecticStafford.Induction.ConstructiveSuccessor
import Mathlib.Data.ZMod.Basic

/-!
# Independent oracle for constructive base/successor assembly

The `ZMod 1` model closes every producer obligation by contradiction, while
the base constructor is exercised directly over a concrete nonempty source
model.  The assertions check that witnesses are built from fields rather than
accepted as a pre-built output, and that terminal cofactors remain in `U`.
-/

namespace SymplecticStafford.ConstructiveSuccessorOracle

open SymplecticStafford.Induction

abbrev U := ZMod 1

def defect : U → U → List (LocalTest U U U) → Int := fun _ _ _ => -1

def parameters : CentralParameters U U where
  embed := fun x => x
  central := by intros; exact mul_comm _ _

def baseData : BaseProducer 0 defect := by
  intro d hd A Ω hΩ
  exact False.elim (hd (Subsingleton.elim d 0))

def successors : ConstructiveSuccessorFamily parameters Unit 0 defect := by
  intro h lower d hd A Ω hΩ
  exact False.elim (hd (Subsingleton.elim d 0))

def zeroExtraction : ∀ {d f : U} {Ω : List (LocalTest U U U)},
    defect d f Ω ≤ -1 → OriginalCofactors d f := by
  intro d f Ω h
  refine {R := 0, S := 0, identity := ?_}
  exact Subsingleton.elim _ _

example : BaseProducer 0 defect := baseData

example : StrongPh 0 1 defect :=
  base_producer_strongPh baseData

example (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U U U))
    (hΩ : AdmissibleTestList d Ω) :
    OriginalCofactors d
      (strongPh_fin_index parameters Unit 0 defect
        (base_producer_strongPh baseData)
        (constructive_successor_family successors) d hd A Ω hΩ).source := by
  exact constructive_terminal_cofactors baseData successors zeroExtraction
    d hd A Ω hΩ

/- A non-vacuous finite-list check of the base constructor: the output fields
are supplied individually and the theorem assembles the witness. -/
def natBaseDefect : Nat → Nat → List (LocalTest Nat Unit Unit) → Int :=
  fun _ _ _ => 0

def natAffine : AffineSource Nat :=
  ⟨3, 2, by decide⟩

def natBase : BaseConstruction 1 natBaseDefect 4 natAffine [] where
  H := 5
  source := 13
  source_eq := by norm_num [natAffine]
  defect_bound := by norm_num [natBaseDefect, defectBound]
  tests_pass := by simp

example :
    (natBase.witness).source = 13 := by rfl

example :
    (natBase.witness).source = natAffine.B + natBase.H * natAffine.a := by
  exact natBase.source_eq

/- A non-vacuous successor instance over `Nat`.  The test list is empty, but
the lower calls, original-U relation, pencil source equation, and defect
decrease are all computed rather than discharged by a nonexistent divisor. -/
def natDefect : Nat → Nat → List (LocalTest Nat Unit Empty) → Int :=
  fun _ f _ => if f = 7 then -2 else -1

def natParameters : CentralParameters Nat Nat where
  embed := fun x => x
  central := by intros; exact Nat.mul_comm _ _

def natLower : StrongPh 1 1 natDefect := by
  intro d hd A Ω hΩ
  refine {
    H := 1
    source := A.B + A.a
    source_eq := by simp
    defect_bound := by
      by_cases h : A.B + A.a = 7 <;>
        simp [natDefect, defectBound, h]
    tests_pass := by
      intro t ht
      exact nomatch t.cyclicModule }

def natSuccessor : SuccessorConstruction natParameters Unit 1 1 natDefect
    natLower 1 (by decide) natAffine [] (admissibleTestList_nil 1) where
  L0 := 1
  C0 := natAffine.B + natAffine.a
  auxiliaryDivisor := 1
  auxiliaryDivisor_eq := by norm_num [natAffine]
  auxiliaryDivisor_nonzero := by decide
  old_relation := by norm_num [natAffine, natLower]
  oldInput := []
  oldInput_admissible := admissibleTestList_nil 1
  newInput := []
  newInput_admissible := admissibleTestList_nil 1
  carried_in_old := by intro t ht; simp at ht
  carried_in_new := by intro t ht; simp at ht
  parameter := 1
  parameter_good := True
  parameter_good_proof := True.intro
  components := {
    oldComponents := []
    newComponents := []
    commonComponents := []
    old_new_disjoint := by simp
    old_new_cover := by simp
    common_component_cover := by simp }
  componentExceptional := fun _ _ => False
  testExceptional := fun _ _ => False
  parameter_avoids_components := by simp
  parameter_retains_tests := by simp
  oldDefect := -1
  newDefect := -1
  commonDefect := -1
  outputDefect := -2
  old_bound := by norm_num [defectBound]
  new_bound := by norm_num [defectBound]
  common_eq_min := by norm_num
  output_eq_common_sub_one := by norm_num
  old_defect_eq := by norm_num [natDefect, natLower, natAffine]
  new_defect_eq := by
    norm_num [natDefect, natLower, homogeneousAffine, natAffine]
  outputH := 2
  outputSource := 7
  output_source_pencil := by
    norm_num [pencilMember, natParameters, natAffine, natLower,
      homogeneousAffine]
  output_source_affine := by norm_num [natAffine]
  output_defect_eq := by norm_num [natDefect]
  pencil_generation := by simp

example :
    natSuccessor.witness.source = 7 := by rfl

example :
    natDefect 1 natSuccessor.witness.source [] ≤ defectBound 1 (1 + 1) := by
  exact natSuccessor.witness.defect_bound

end SymplecticStafford.ConstructiveSuccessorOracle
