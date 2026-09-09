import Mathlib.Tactic
import SymplecticStafford.Induction.CentralFieldFiniteIndex

/-!
# Independent central-field finite-index oracle

The endpoint is instantiated over `ℚ` with a concrete finite support map on
`Fin 2`: the old source value `5` has support `{0,1}`, while every other
source has `{1}`.  The base producer and the all-index central-field step
family remain explicit arguments, so this oracle checks endpoint composition
without pretending to construct the universal base or support-removal laws.
The endpoint test conclusion is read from the resulting `StrongPh` witness.
-/

namespace SymplecticStafford.Induction.CentralFieldFiniteIndexOracle

open SymplecticStafford.Induction

abbrev κ := Fin 2

def parameters : CentralParameters ℚ ℚ where
  embed := id
  central := by intro z x; exact mul_comm _ _

def support (_q f : ℚ) (_xs : List (LocalTest ℚ Unit Unit)) : Finset κ :=
  if f = 5 then {0, 1} else {1}

def defect : ℚ → ℚ → List (LocalTest ℚ Unit Unit) → Int :=
  fun q f xs => finiteSupportDefect (support q f xs)

example : support 1 5 [] = ({0, 1} : Finset κ) := by
  simp [support]

example : finiteSupportDefect (support 1 5 []) = 1 := by
  norm_num [support, finiteSupportDefect]

example
    (lower : StrongPh 2 1 defect)
    (d : ℚ) (hd : d ≠ 0) (A : AffineSource ℚ)
    (Ω : List (LocalTest ℚ Unit Unit))
    (hΩ : AdmissibleTestList d Ω)
    (step : CentralFieldTwoCallStep (P := parameters) (κ := κ)
      (D := 2) (h := 1) (defect := defect) (lower := lower)
      (d := d) (hd := hd) (A := A) (Ω := Ω) (hΩ := hΩ)) :
    ∀ z : ℚ,
      (∀ p, p ∈ step.oldSupport →
        (step.certificate.componentPolynomial p).eval z ≠ 0) →
      finiteSupportDefect (step.outputSupport z) ≤ defectBound 2 (1 + 1) := by
  exact step.output_bound

noncomputable example
    (base : BaseProducer 2 defect)
    (family : CentralFieldTwoCallFamily parameters κ 2 defect) :
    StrongPh 2 3 defect := by
  exact strongPh_fin_index_of_central_field_two_call κ 2 defect base family

noncomputable example
    (base : BaseProducer 2 defect)
    (family : CentralFieldTwoCallFamily parameters κ 2 defect) :
    FiniteIndexEndpoint 2 defect := by
  exact central_field_finite_index_endpoint κ 2 defect base family

noncomputable example
    (base : BaseProducer 2 defect)
    (family : CentralFieldTwoCallFamily parameters κ 2 defect)
    (d : ℚ) (hd : d ≠ 0) (A : AffineSource ℚ)
    (Ω : List (LocalTest ℚ Unit Unit))
    (hΩ : AdmissibleTestList d Ω) :
    ∀ t, t ∈ Ω →
      t.generation
        ((strongPh_fin_index_of_central_field_two_call κ 2 defect base family
          d hd A Ω hΩ).source) := by
  intro t ht
  exact (strongPh_fin_index_of_central_field_two_call κ 2 defect base family
    d hd A Ω hΩ).tests_pass t ht

end SymplecticStafford.Induction.CentralFieldFiniteIndexOracle

#print axioms SymplecticStafford.Induction.strongPh_fin_index_of_central_field_two_call
#print axioms SymplecticStafford.Induction.central_field_finite_index_endpoint
