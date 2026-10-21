module

public import Mathlib.Tactic
public import SymplecticStafford.Induction.CentralFieldTwoCallSuccessor

@[expose] public section

/-!
# Independent central-field two-call successor oracle

This is a complete concrete two-call datum over `ℚ`.  The lower source is
`5`, the auxiliary source is `2`, and the component polynomial `X` excludes
the single scalar at which `5 + z * 2 = 5`; hence `{0,1}` strictly drops to
`{1}`.  The carried list contains an actual local test with right tail `1`.
The successor source and affine equation are obtained from the composed
constructor, not supplied as output data.
-/

namespace SymplecticStafford.Induction.CentralFieldTwoCallSuccessorOracle

open SymplecticStafford.Induction

abbrev K := ℚ
abbrev κ := Fin 2

def parameters : CentralParameters ℚ ℚ where
  embed := id
  central := by intro z x; exact mul_comm _ _

def carriedTest : LocalTest ℚ Unit Unit where
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
  rightTail_nonzero := by norm_num
  generation := fun _ => True

def carried : List (LocalTest ℚ Unit Unit) := [carriedTest]

theorem carried_mem : carriedTest ∈ carried := by simp [carried]

theorem carried_admissible : AdmissibleTestList 1 carried := by
  intro t ht
  have ht' : t = carriedTest := by simpa [carried] using ht
  subst t
  exact carriedTest.admissible_of_fields 1 rfl

def affine : AffineSource ℚ := ⟨3, 2, by norm_num⟩

def support (_q f : ℚ) (_xs : List (LocalTest ℚ Unit Unit)) : Finset κ :=
  if f = 5 then {0, 1} else {1}

def defect : ℚ → ℚ → List (LocalTest ℚ Unit Unit) → Int :=
  fun q f xs => finiteSupportDefect (support q f xs)

def data (lower : StrongPh 2 1 defect)
    (hOld : (lower 1 (by norm_num) affine carried carried_admissible).source = 5)
    (hNew : (lower 1 (by norm_num)
      (homogeneousAffine affine.a affine.a_nonzero) carried
      carried_admissible).source = 2) :
    TwoCallDescentData (κ := κ) parameters 2 1 defect lower
      1 (by norm_num) affine carried carried_admissible where
  L0 := 1
  C0 := 5
  auxiliaryDivisor := 1
  auxiliaryDivisor_eq := by norm_num
  auxiliaryDivisor_nonzero := by norm_num
  old_relation := by rw [hOld]; norm_num
  newInput := carried
  newInput_admissible := carried_admissible
  carried_in_new := listCarried_refl carried
  support := support
  defect_eq_support := by intro q f xs; rfl
  exceptional := {0}
  exceptional_finite := Set.finite_singleton 0
  strict_support := by
    intro z hz
    have hz' : z ≠ 0 := by simpa using hz
    have hne : 5 + z * 2 ≠ (5 : ℚ) := by
      intro h
      have : z * 2 = 0 := by linarith
      exact hz' (by exact (mul_eq_zero.mp this).resolve_right (by norm_num))
    rw [hOld, hNew]
    simp [support, pencilMember, parameters, hne]
    exact by decide
  pencil_generation := by
    intro z t hz ht hF hG
    have ht' : t = carriedTest := by simpa [carried] using ht
    subst t
    change True
    trivial

noncomputable def polynomialData
    (lower : StrongPh 2 1 defect)
    (hOld : (lower 1 (by norm_num) affine carried carried_admissible).source = 5)
    (hNew : (lower 1 (by norm_num)
      (homogeneousAffine affine.a affine.a_nonzero) carried
      carried_admissible).source = 2) :
    CentralFieldTwoCallData (κ := κ) (data lower hOld hNew) where
  componentPolynomial := fun p => if p = 0 then Polynomial.X else 1
  testPolynomial := fun _ => 1
  componentPolynomial_ne_zero := by
    intro p hp
    split <;> simp
  testPolynomial_ne_zero := by
    intro t ht
    simp
  strict_support_of_good := by
    intro z hgood
    have hzero : (Polynomial.X : Polynomial ℚ).eval z ≠ 0 := by
      exact hgood 0 (by simp [data, support, hOld])
    have hz : z ≠ 0 := by simpa using hzero
    have hne : 5 + z * 2 ≠ (5 : ℚ) := by
      intro h
      have : z * 2 = 0 := by linarith
      exact hz (by exact (mul_eq_zero.mp this).resolve_right (by norm_num))
    simpa [data, support, pencilMember, parameters, hOld, hNew, hne]
      using (show ({1} : Finset κ) ⊂ {0, 1} by decide)
  pencil_generation_of_good := by
    intro z hcomponent htests t ht hF hG
    have ht' : t = carriedTest := by simpa [carried] using ht
    subst t
    change True
    trivial

noncomputable example
    (lower : StrongPh 2 1 defect)
    (hOld : (lower 1 (by norm_num) affine carried carried_admissible).source = 5)
    (hNew : (lower 1 (by norm_num)
      (homogeneousAffine affine.a affine.a_nonzero) carried
      carried_admissible).source = 2) :
    StrongPhWitness (D := 2) (h := 2) defect 1 affine carried := by
  exact (data lower hOld hNew).central_field_witness
    (polynomialData lower hOld hNew)

noncomputable example
    (lower : StrongPh 2 1 defect)
    (hOld : (lower 1 (by norm_num) affine carried carried_admissible).source = 5)
    (hNew : (lower 1 (by norm_num)
      (homogeneousAffine affine.a affine.a_nonzero) carried
      carried_admissible).source = 2) :
    ((data lower hOld hNew).central_field_witness
      (polynomialData lower hOld hNew)).source =
      affine.B + ((data lower hOld hNew).central_field_witness
        (polynomialData lower hOld hNew)).H * affine.a := by
  exact (data lower hOld hNew).central_field_witness_source_eq
    (polynomialData lower hOld hNew)

noncomputable example
    (lower : StrongPh 2 1 defect)
    (hOld : (lower 1 (by norm_num) affine carried carried_admissible).source = 5)
    (hNew : (lower 1 (by norm_num)
      (homogeneousAffine affine.a affine.a_nonzero) carried
      carried_admissible).source = 2) :
    carriedTest.generation
      ((data lower hOld hNew).central_field_witness
        (polynomialData lower hOld hNew)).source := by
  exact ((data lower hOld hNew).central_field_witness
    (polynomialData lower hOld hNew)).tests_pass carriedTest carried_mem

end SymplecticStafford.Induction.CentralFieldTwoCallSuccessorOracle

#print axioms SymplecticStafford.Induction.TwoCallDescentData.central_field_witness
