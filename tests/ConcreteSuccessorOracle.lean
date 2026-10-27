module

public import SymplecticStafford.Induction.ConcreteSuccessor
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Independent oracle for the concrete two-call successor contract

The natural-number model supplies a nonzero affine tail while the empty local
test lists make the producer obligations vacuous.  The oracle still
instantiates old and new `Fin`-indexed families, two lower calls, carried-list
membership, and the exact defect output.  It is an oracle for contract wiring
only, not for the universal theorem.
-/

namespace SymplecticStafford.ConcreteSuccessorOracle

open SymplecticStafford.Induction

abbrev U := Nat

def defect : U → U → List (LocalTest U Unit Empty) → Int :=
  fun _ f _ => if f = 0 then -1 else -2

def parameters : CentralParameters U U where
  embed := fun x => x
  central := by intros; exact Nat.mul_comm _ _

def lower : StrongPh 2 1 defect := by
  intro d hd A Ω hΩ
  refine {
    H := 0
    source := A.B
    source_eq := by simp
    defect_bound := by
      by_cases hzero : A.B = 0 <;> simp [defect, defectBound, hzero] <;>
        norm_num
    tests_pass := ?_ }
  intro t ht
  exact nomatch t.cyclicModule

def affineOne : AffineSource U :=
  ⟨0, 1, by decide⟩

def emptyAdmissible (d : U) :
    AdmissibleTestList d ([] : List (LocalTest U Unit Empty)) := by
  intro t ht
  simp at ht

def oldFamily : IndexedTestFamily U (LocalTest U Unit Empty)
    (fun q t => t.Admissible q) 1 1 where
  input := []
  family := fun _ => []
  input_admissible := emptyAdmissible 1
  family_admissible := by intro i t ht; simp at ht
  covers_input := by intro t ht; simp at ht

def newFamily : IndexedTestFamily U (LocalTest U Unit Empty)
    (fun q t => t.Admissible q) 1 1 where
  input := []
  family := fun _ => []
  input_admissible := emptyAdmissible 1
  family_admissible := by intro i t ht; simp at ht
  covers_input := by intro t ht; simp at ht

def certificate : ConcreteSuccessorData parameters Unit 2 1 defect lower
    1 (by decide) affineOne [] (emptyAdmissible 1) 1 (by decide) []
    (emptyAdmissible 1) [] (emptyAdmissible 1) 1 1 where
  oldFamily := oldFamily
  newFamily := newFamily
  oldInput_eq_family_input := rfl
  newInput_eq_family_input := rfl
  oldCall := lower 1 (by decide) affineOne [] (emptyAdmissible 1)
  oldCall_eq_lower := rfl
  newAffine := homogeneousAffine 1 (by decide)
  newAffine_eq_homogeneous := rfl
  newCall := lower 1 (by decide) (homogeneousAffine 1 (by decide)) []
    (emptyAdmissible 1)
  newCall_eq_lower := rfl
  carried_in_old := by intro t ht; simp at ht
  carried_in_new := by intro t ht; simp at ht
  old_new_split := {
    oldComponents := []
    newComponents := []
    commonComponents := []
    old_new_disjoint := by simp
    old_new_cover := by simp
    common_component_cover := by simp }
  arithmetic := {
    oldDefect := -1
    newDefect := -1
    commonDefect := -1
    outputDefect := -2
    old_bound := by norm_num [defectBound]
    new_bound := by norm_num [defectBound]
    common_eq_min := by norm_num
    output_eq_common_sub_one := by norm_num }
  old_defect_eq := by
    change (-1 : Int) = defect 1 0 []
    simp [defect]
  new_defect_eq := by
    change (-1 : Int) = defect 1 0 []
    simp [defect]
  output := {
    H := 1
    source := 1
    source_eq := by simp [affineOne]
    defect_bound := by norm_num [defect, defectBound]
    tests_pass := by intro t ht; exact nomatch t.cyclicModule }
  output_defect_eq := by simp [defect]

example : ∀ (t : LocalTest U Unit Empty), t ∈ ([] : List (LocalTest U Unit Empty)) →
    t.generation certificate.oldCall.source ∧
      t.generation certificate.newCall.source := by
  exact certificate.retention

example : defect 1 certificate.output.source ([] : List (LocalTest U Unit Empty)) ≤
    defectBound 2 (1 + 1) := by
  exact certificate.output_bound

example : ∀ (t : LocalTest U Unit Empty), t ∈ ([] : List (LocalTest U Unit Empty)) →
    ∃ i : Fin 1, t ∈ oldFamily.family i := by
  intro t ht
  simp at ht

end SymplecticStafford.ConcreteSuccessorOracle
