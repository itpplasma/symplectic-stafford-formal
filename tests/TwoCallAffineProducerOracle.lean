import SymplecticStafford.Induction.TwoCallAffineProducer
import Mathlib.Tactic.NormNum

/- Independent non-vacuous oracle for the two-call source constructor. -/

namespace SymplecticStaffordTest.TwoCallAffineProducer

open SymplecticStafford.Induction

noncomputable section

def parameters : CentralParameters Nat Nat where
  embed := fun x => x
  central := by intro x y; exact Nat.mul_comm _ _

def affine : AffineSource Nat := ⟨3, 2, by decide⟩

def defect : Nat → Nat → List (LocalTest Nat Unit Empty) → Int :=
  fun _ _ _ => -2

def lower : StrongPh 1 1 defect := by
  intro d hd A Ω hΩ
  refine {
    H := 5
    source := A.B + 5 * A.a
    source_eq := by simp
    defect_bound := by norm_num [defect, defectBound]
    tests_pass := ?_ }
  intro t ht
  exact nomatch t.cyclicModule

def old := lower 1 (by decide) affine [] (admissibleTestList_nil 1)
def new := lower 1 (by decide) (homogeneousAffine affine.a affine.a_nonzero)
  [] (admissibleTestList_nil 1)

example :
    affine.member (pencilMember parameters old.source new.source 1) := by
  exact affine_member_pencil_of_members parameters affine old.affine_member
    new.affine_member

example :
    StrongPhWitness (D := 1) (h := 2) defect 1 affine [] := by
  apply strongPhWitness_of_two_lower_calls parameters (lower := lower)
    (d := 1) (hd := by decide) (A := affine) (Ω := [])
    (hΩ := admissibleTestList_nil 1) (d₁ := 1) (hd₁ := by decide)
    (Ω₁ := []) (hΩ₁ := admissibleTestList_nil 1)
    (hcarry := by intro t ht; simp at ht)
    (scalar := 1)
  · norm_num [defect, defectBound, pencilMember, parameters, old, new, lower,
      affine, homogeneousAffine]
  · intro t ht h₁ h₂
    exact nomatch t.cyclicModule

example :
    (pencilMember parameters old.source new.source 1) = 23 := by
  norm_num [pencilMember, parameters, old, new, lower, affine,
    homogeneousAffine]

end
end SymplecticStaffordTest.TwoCallAffineProducer
