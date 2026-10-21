module

public import SymplecticStafford.Induction.TwoCallDescentProducer
public import SymplecticStafford.Induction.FiniteRemovalRetentionBridge
public import Mathlib.Tactic

@[expose] public section

/-!
# Independent oracle for the descent-level successor constructor

This is a non-vacuous natural-number instance.  The lower call has support
defect zero, while the selected pencil source has empty support outside one
explicit exceptional scalar.  The next witness is constructed by the new
producer rather than supplied as a field.
-/

namespace SymplecticStafford.TwoCallDescentProducerOracle

open SymplecticStafford.Induction

abbrev K := Unit

def parameters : CentralParameters Nat Nat where
  embed := id
  central := by intro z x; exact Nat.mul_comm _ _

def support (q f : Nat) (_ : List (LocalTest Nat Unit Empty)) : Finset K :=
  if f = 5 then {()} else ∅

def defect : Nat → Nat → List (LocalTest Nat Unit Empty) → Int :=
  fun q f xs => finiteSupportDefect (support q f xs)

def lower : StrongPh 1 1 defect := by
  intro d hd A Ω hΩ
  refine {
    H := 1
    source := A.B + A.a
    source_eq := by simp
    defect_bound := by
      simp only [defect, finiteSupportDefect, support]
      split <;> norm_num [defectBound]
    tests_pass := by
      intro t ht
      exact nomatch t.cyclicModule }

def affine : AffineSource Nat := ⟨3, 2, by decide⟩

def data : TwoCallDescentData (κ := K) parameters 1 1 defect lower
    1 (by decide) affine [] (admissibleTestList_nil 1) where
  L0 := 1
  C0 := 5
  auxiliaryDivisor := 1
  auxiliaryDivisor_eq := by decide
  auxiliaryDivisor_nonzero := by decide
  old_relation := by norm_num [affine, lower]
  newInput := []
  newInput_admissible := admissibleTestList_nil 1
  carried_in_new := by intro t ht; simp at ht
  support := support
  defect_eq_support := by intro q f xs; rfl
  exceptional := {0}
  exceptional_finite := Set.finite_singleton 0
  strict_support := by
    intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    have hne : 5 + z * 2 ≠ 5 := by
      intro h
      omega
    have hout : support 1
        (pencilMember parameters
          (lower 1 (by decide) affine [] (admissibleTestList_nil 1)).source
          (lower 1 (by decide)
            (homogeneousAffine affine.a affine.a_nonzero) []
            (admissibleTestList_nil 1)).source z) [] = ∅ := by
      change (if 5 + z * 2 = 5 then ({()} : Finset K) else ∅) = ∅
      simp [hz']
    rw [hout]
    simp [support, lower, affine]
  pencil_generation := by simp

noncomputable example : StrongPhWitness (D := 1) (h := 2) defect 1 affine [] :=
  data.witness

example : data.witness.source = affine.B + data.witness.H * affine.a := by
  exact data.witness.source_eq

example : defect 1 data.witness.source [] ≤ defectBound 1 (1 + 1) := by
  exact data.witness.defect_bound

/- The stronger bridge chooses the scalar through indexed component/test
   exceptions.  Its strictness field is proved from the raw datum only after
   deriving avoidance of the raw exceptional set from the component index. -/
def indexed : FiniteRemovalRetentionData data where
  componentBad := fun _ z => z ∈ data.exceptional
  testBad := fun _ _ => False
  component_finite := by
    intro a ha
    simpa only [Set.ofPred_mem_eq] using data.exceptional_finite
  test_finite := by
    intro t ht
    simp
  strict_support_of_good := by
    intro z hgood
    have hold : () ∈ data.support 1 5 [] := by
      change () ∈ support 1 5 []
      simp [support]
    have hz : z ∉ data.exceptional := by
      intro hzbad
      exact hgood () hold hzbad
    exact data.strict_support z hz
  pencil_generation_of_good := by
    intro z hgood htests t ht hF hG
    have hold : () ∈ data.support 1 5 [] := by
      change () ∈ support 1 5 []
      simp [support]
    exact data.pencil_generation z t (by
      intro hz
      exact hgood () hold hz) ht hF hG

noncomputable example : StrongPhWitness (D := 1) (h := 2) defect 1 affine [] :=
  indexed.witness

/- The finite-index endpoint also composes a raw descent family.  This
   subsingleton ring replay is only for the recursion plumbing: its producer
   calls are vacuous because there is no nonzero divisor. -/
namespace Endpoint

abbrev U := ZMod 1

def endpointParameters : CentralParameters U Nat where
  embed := fun z => z
  central := by intro z x; exact Subsingleton.elim _ _

def endpointDefect : U → U → List (LocalTest U Unit Unit) → Int :=
  fun _ _ _ => -1

def endpointBase : StrongPh 0 1 endpointDefect := by
  intro d hd A Ω hΩ
  exact False.elim (hd (Subsingleton.elim d 0))

def endpointFamily : TwoCallDescentFamily endpointParameters Unit 0 endpointDefect := by
  intro h lower d hd A Ω hΩ
  exact False.elim (hd (Subsingleton.elim d 0))

example : StrongPh 0 1 endpointDefect := endpointBase

noncomputable example : StrongPh 0 (0 + 1) endpointDefect :=
  strongPh_fin_index_of_two_call_descent endpointBase endpointFamily

end Endpoint

end SymplecticStafford.TwoCallDescentProducerOracle

#print axioms SymplecticStafford.TwoCallDescentProducerOracle.data
#print axioms SymplecticStafford.Induction.TwoCallDescentData.witness
