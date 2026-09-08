import SymplecticStafford.Induction.FiniteIndex
import SymplecticStafford.Induction.TestRetention
import Mathlib.Tactic.Ring

/-!
# Constructive base and successor interfaces

The older induction files expose useful bookkeeping contracts, but their
`StrongPh` and successor certificates consume the complete output witness as
an input.  This file gives the next boundary: a caller supplies the individual
source, arithmetic, and finite-test facts, and the constructors below build
the `StrongPhWitness` and `SuccessorRule` fields.

The support-removal, scalar-avoidance, and local-test production theorems are
still hypotheses.  In particular, this does not claim the universal source
producer.  Every source in the constructed witness is an element of the
original `U`, and the terminal theorem keeps the original-U cofactor order.
-/

namespace SymplecticStafford.Induction

universe u v w x

variable {U : Type u} [Semiring U]

/-! ## Pointwise base construction -/

/-- Explicit data for one base `P₁` output.  Its fields are the source
coefficient, source identity, defect bound, and finite-test conclusions; it
does not package a pre-built `StrongPhWitness`. -/
structure BaseConstruction
    (D : Nat)
    (defect : U → U → List (LocalTest U v w) → Int)
    (d : U) (A : AffineSource U)
    (Ω : List (LocalTest U v w)) where
  H : U
  source : U
  source_eq : source = A.B + H * A.a
  defect_bound : defect d source Ω ≤ defectBound D 1
  tests_pass : ∀ t, t ∈ Ω → t.generation source

def BaseConstruction.witness
    {D : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {d : U} {A : AffineSource U}
    {Ω : List (LocalTest U v w)}
    (b : BaseConstruction D defect d A Ω) :
    StrongPhWitness D 1 defect d A Ω := by
  exact {
    H := b.H
    source := b.source
    source_eq := b.source_eq
    defect_bound := b.defect_bound
    tests_pass := b.tests_pass }

/-- A pointwise producer for the base index, stated without an output-witness
field. -/
def BaseProducer
    (D : Nat)
    (defect : U → U → List (LocalTest U v w) → Int) : Type _ :=
  ∀ (d : U), d ≠ 0 → ∀ (A : AffineSource U)
    (Ω : List (LocalTest U v w)),
    AdmissibleTestList d Ω → BaseConstruction D defect d A Ω

def base_producer_strongPh
    {D : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    (base : BaseProducer D defect) :
    StrongPh D 1 defect := by
  intro d hd A Ω hΩ
  exact (base d hd A Ω hΩ).witness

/-! ## Explicit two-call successor construction -/

/-- Data for one successor call.  The two lower-index witnesses are obtained
by applying `lower`; no witness for either call is supplied separately.  The
only hypotheses about the output are its source coefficient/equation, the
support-removal arithmetic, and a finite pencil-retention implication.

`old_relation` retains the original-U relation `F*d*L0=d*C0`, while
`carried_in_*` and `pencil_generation` retain every carried local test. -/
structure SuccessorConstruction
    {Λ : Type x} (P : CentralParameters U Λ) (κ : Type v)
    (D h : Nat)
    (defect : U → U → List (LocalTest U v w) → Int)
    (lower : StrongPh D h defect)
    (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U v w))
    (hΩ : AdmissibleTestList d Ω) where
  L0 : U
  C0 : U
  auxiliaryDivisor : U
  auxiliaryDivisor_eq : auxiliaryDivisor = d * L0
  auxiliaryDivisor_nonzero : auxiliaryDivisor ≠ 0
  old_relation : (lower d hd A Ω hΩ).source * d * L0 = d * C0
  oldInput : List (LocalTest U v w)
  oldInput_admissible : AdmissibleTestList d oldInput
  newInput : List (LocalTest U v w)
  newInput_admissible : AdmissibleTestList auxiliaryDivisor newInput
  carried_in_old : ListCarried Ω oldInput
  carried_in_new : ListCarried Ω newInput
  parameter : Λ
  parameter_good : Prop
  parameter_good_proof : parameter_good
  components : OldNewSplit κ
  componentExceptional : κ → Λ → Prop
  testExceptional : LocalTest U v w → Λ → Prop
  parameter_avoids_components : ∀ p, p ∈ components.commonComponents →
    ¬ componentExceptional p parameter
  parameter_retains_tests : ∀ t, t ∈ Ω → ¬ testExceptional t parameter
  oldDefect : Int
  newDefect : Int
  commonDefect : Int
  outputDefect : Int
  old_bound : oldDefect ≤ defectBound D h
  new_bound : newDefect ≤ defectBound D h
  common_eq_min : commonDefect = min oldDefect newDefect
  output_eq_common_sub_one : outputDefect = commonDefect - 1
  old_defect_eq : oldDefect =
    defect d (lower d hd A Ω hΩ).source Ω
  new_defect_eq : newDefect =
    defect auxiliaryDivisor
      (lower auxiliaryDivisor auxiliaryDivisor_nonzero
        (homogeneousAffine A.a A.a_nonzero) newInput newInput_admissible).source
      newInput
  outputH : U
  outputSource : U
  output_source_pencil : outputSource =
    pencilMember P (lower d hd A Ω hΩ).source
      (lower auxiliaryDivisor auxiliaryDivisor_nonzero
        (homogeneousAffine A.a A.a_nonzero) newInput newInput_admissible).source
      parameter
  output_source_affine : outputSource = A.B + outputH * A.a
  output_defect_eq : outputDefect = defect d outputSource Ω
  pencil_generation : ∀ t, t ∈ Ω →
    t.generation (lower d hd A Ω hΩ).source →
    t.generation
      (lower auxiliaryDivisor auxiliaryDivisor_nonzero
        (homogeneousAffine A.a A.a_nonzero) newInput newInput_admissible).source →
    t.generation outputSource

theorem SuccessorConstruction.output_bound
    {Λ : Type x} {P : CentralParameters U Λ} {κ : Type v}
    {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U v w)}
    {hΩ : AdmissibleTestList d Ω}
    (c : SuccessorConstruction P κ D h defect lower d hd A Ω hΩ) :
    c.outputDefect ≤ defectBound D (h + 1) := by
  rw [c.output_eq_common_sub_one, c.common_eq_min]
  rw [defectBound_succ]
  exact sub_le_sub_right
    (le_trans (min_le_left _ _) c.old_bound) 1

theorem SuccessorConstruction.output_tests
    {Λ : Type x} {P : CentralParameters U Λ} {κ : Type v}
    {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U v w)}
    {hΩ : AdmissibleTestList d Ω}
    (c : SuccessorConstruction P κ D h defect lower d hd A Ω hΩ) :
    ∀ t, t ∈ Ω → t.generation c.outputSource := by
  intro t ht
  apply c.pencil_generation t ht
  · exact (lower d hd A Ω hΩ).tests_pass t ht
  · apply (lower c.auxiliaryDivisor c.auxiliaryDivisor_nonzero
      (homogeneousAffine A.a A.a_nonzero) c.newInput
      c.newInput_admissible).tests_pass t
    exact c.carried_in_new ht

def SuccessorConstruction.witness
    {Λ : Type x} {P : CentralParameters U Λ} {κ : Type v}
    {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U v w)}
    {hΩ : AdmissibleTestList d Ω}
    (c : SuccessorConstruction P κ D h defect lower d hd A Ω hΩ) :
    StrongPhWitness (D := D) (h := h + 1) defect d A Ω := by
  refine {
    H := c.outputH
    source := c.outputSource
    source_eq := c.output_source_affine
    defect_bound := ?_
    tests_pass := c.output_tests }
  rw [← c.output_defect_eq]
  exact c.output_bound

/-- A pointwise successor producer whose output witness is constructed from
the explicit source/arithmetic/test fields above. -/
def ConstructiveSuccessorRule
    {Λ : Type x} (P : CentralParameters U Λ) (κ : Type v)
    (D h : Nat)
    (defect : U → U → List (LocalTest U v w) → Int)
    (lower : StrongPh D h defect) : Type _ :=
  ∀ (d : U), (hd : d ≠ 0) → ∀ (A : AffineSource U)
    (Ω : List (LocalTest U v w)),
    (hΩ : AdmissibleTestList d Ω) →
    SuccessorConstruction P κ D h defect lower d hd A Ω hΩ

def constructive_successor_rule
    {Λ : Type x} {P : CentralParameters U Λ} {κ : Type v}
    {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    (producer : ConstructiveSuccessorRule P κ D h defect lower) :
    SuccessorRule P κ D h defect lower := by
  intro d hd A Ω hΩ
  let c := producer d hd A Ω hΩ
  refine {
    L0 := c.L0
    C0 := c.C0
    auxiliaryDivisor := c.auxiliaryDivisor
    auxiliaryDivisor_eq := c.auxiliaryDivisor_eq
    auxiliaryDivisor_nonzero := c.auxiliaryDivisor_nonzero
    old_relation := c.old_relation
    oldTests := c.newInput
    oldTests_admissible := c.newInput_admissible
    auxiliary := lower c.auxiliaryDivisor c.auxiliaryDivisor_nonzero
      (homogeneousAffine A.a A.a_nonzero) c.newInput c.newInput_admissible
    auxiliary_is_lower_call := rfl
    oldComponents := c.components.oldComponents
    newComponents := c.components.newComponents
    commonComponents := c.components.commonComponents
    old_new_disjoint := c.components.old_new_disjoint
    old_new_cover := c.components.old_new_cover
    common_component_cover := c.components.common_component_cover
    commonDefect := c.commonDefect
    common_defect_bound := by
      rw [c.common_eq_min]
      exact le_trans (min_le_left _ _) c.old_bound
    componentExceptional := c.componentExceptional
    testExceptional := c.testExceptional
    parameter := c.parameter
    parameter_good := c.parameter_good
    parameter_good_proof := c.parameter_good_proof
    parameter_avoids_components := c.parameter_avoids_components
    parameter_retains_tests := c.parameter_retains_tests
    output := c.witness
    output_source_pencil := c.output_source_pencil
    carried_tests_retained := c.output_tests }

/-! ## Finite-index composition and original-U cofactors -/

def ConstructiveSuccessorFamily
    {Λ : Type x} (P : CentralParameters U Λ) (κ : Type v)
    (D : Nat)
    (defect : U → U → List (LocalTest U v w) → Int) : Type _ :=
  ∀ h : Nat, ∀ (lower : StrongPh D h defect),
    ConstructiveSuccessorRule P κ D h defect lower

def constructive_successor_family
    {Λ : Type x} {P : CentralParameters U Λ} {κ : Type v}
    {D : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    (family : ConstructiveSuccessorFamily P κ D defect) :
    SuccessorFamily P κ D defect := by
  intro h lower
  exact constructive_successor_rule (family h lower)

def constructive_terminal_cofactors
    {Λ : Type x} {P : CentralParameters U Λ} {κ : Type v}
    {D : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    (base : BaseProducer D defect)
    (family : ConstructiveSuccessorFamily P κ D defect)
    (zero_extraction : ∀ {d f : U} {Ω : List (LocalTest U v w)},
      defect d f Ω ≤ -1 → OriginalCofactors d f)
    (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U v w))
    (hΩ : AdmissibleTestList d Ω) :
    OriginalCofactors d
      (strongPh_fin_index P κ D defect (base_producer_strongPh base)
        (constructive_successor_family family) d hd A Ω hΩ).source := by
  exact terminal_cofactors_fin_index P κ D defect
    (base_producer_strongPh base) (constructive_successor_family family)
    zero_extraction (defectBound_terminal D) d hd A Ω hΩ

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.base_producer_strongPh
#print axioms SymplecticStafford.Induction.SuccessorConstruction.witness
#print axioms SymplecticStafford.Induction.constructive_terminal_cofactors
