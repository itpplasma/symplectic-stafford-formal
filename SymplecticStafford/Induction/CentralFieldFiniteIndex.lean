module

public import SymplecticStafford.Induction.CentralFieldTwoCallSuccessor
public import SymplecticStafford.Induction.BaseTwoCallAssembly

@[expose] public section

/-!
# Finite-index endpoint adapter for central-field two-call steps

`CentralFieldTwoCallSuccessor` constructs one next-index witness from an
actual two-call datum and its polynomial local certificate.  This file
packages those steps with a supplied `BaseProducer` into the integer-defect
`StrongPh`/finite-index interface.  Each family member retains the actual
old/new support map, the carried-test list, and both source-dependent local
implications through its two fields; no universal base or support-removal
input is inferred.
-/

namespace SymplecticStafford.Induction

universe u v w x y

variable {U : Type u} [Semiring U]

section Step

variable {K : Type v} [Field K] [Infinite K]
variable {κ : Type w} [DecidableEq κ]
variable {T : Type x} {V : Type y}

/-- A single central-field successor step, keeping the actual two-call data
and its local polynomial/support-retention certificate together. -/
structure CentralFieldTwoCallStep
    {P : CentralParameters U K} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U T V)}
    {hΩ : AdmissibleTestList d Ω} where
  data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ
  certificate : CentralFieldTwoCallData (κ := κ) data
  /-- Explicit old/new/output support representatives for the two calls. -/
  oldSupport : Finset κ
  newSupport : Finset κ
  outputSupport : K → Finset κ
  oldSupport_eq : oldSupport =
    data.support d (lower d hd A Ω hΩ).source Ω
  newSupport_eq : newSupport =
    data.support data.auxiliaryDivisor
      (lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
        (homogeneousAffine A.a A.a_nonzero) data.newInput
        data.newInput_admissible).source data.newInput
  outputSupport_eq : ∀ z : K, outputSupport z =
    data.support d
      (pencilMember P (lower d hd A Ω hΩ).source
        (lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
          (homogeneousAffine A.a A.a_nonzero) data.newInput
          data.newInput_admissible).source z) Ω
  output_subset_old : ∀ z : K,
    (∀ p, p ∈ oldSupport →
      (certificate.componentPolynomial p).eval z ≠ 0) →
      outputSupport z ⊆ oldSupport
  output_subset_new : ∀ z : K,
    (∀ p, p ∈ oldSupport →
      (certificate.componentPolynomial p).eval z ≠ 0) →
      outputSupport z ⊆ newSupport
  output_strict_old : ∀ z : K,
    (∀ p, p ∈ oldSupport →
      (certificate.componentPolynomial p).eval z ≠ 0) →
      outputSupport z ⊂ oldSupport
  output_strict_new : ∀ z : K,
    (∀ p, p ∈ oldSupport →
      (certificate.componentPolynomial p).eval z ≠ 0) →
      outputSupport z ⊂ newSupport
  old_bound : finiteSupportDefect oldSupport ≤ defectBound D h
  new_bound : finiteSupportDefect newSupport ≤ defectBound D h

theorem CentralFieldTwoCallStep.output_bound
    {K : Type v} [Field K] [Infinite K]
    {κ : Type w} [DecidableEq κ]
    {T : Type x} {V : Type y}
    {P : CentralParameters U K} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U T V)}
    {hΩ : AdmissibleTestList d Ω}
    (step : CentralFieldTwoCallStep (κ := κ) (P := P) (D := D)
      (h := h) (defect := defect) (lower := lower) (d := d)
      (hd := hd) (A := A) (Ω := Ω) (hΩ := hΩ)) :
    ∀ z : K,
      (∀ p, p ∈ step.oldSupport →
        (step.certificate.componentPolynomial p).eval z ≠ 0) →
      finiteSupportDefect (step.outputSupport z) ≤
        defectBound D (h + 1) := by
  intro z hz
  exact SupportRemovalArithmetic.output_bound {
    oldSupport := step.oldSupport
    newSupport := step.newSupport
    outputSupport := step.outputSupport z
    output_subset_old := step.output_subset_old z hz
    output_subset_new := step.output_subset_new z hz
    output_strict_old := step.output_strict_old z hz
    output_strict_new := step.output_strict_new z hz
    old_bound := step.old_bound
    new_bound := step.new_bound }

/-- A family of explicit central-field steps at every index and target datum.
The base and all local support/test inputs remain caller-supplied. -/
def CentralFieldTwoCallFamily
    (P : CentralParameters U K) (κ : Type w) [DecidableEq κ]
    (D : Nat) (defect : U → U → List (LocalTest U T V) → Int) : Type _ :=
  ∀ h : Nat, ∀ (lower : StrongPh D h defect), ∀ (d : U) (hd : d ≠ 0),
    ∀ (A : AffineSource U) (Ω : List (LocalTest U T V))
      (hΩ : AdmissibleTestList d Ω),
        CentralFieldTwoCallStep (P := P) (κ := κ) (D := D) (h := h)
          (defect := defect) (lower := lower) (d := d)
          (hd := hd) (A := A) (Ω := Ω) (hΩ := hΩ)

/-- One successor rule obtained from every explicit central-field step. -/
noncomputable def central_field_successor_of_family
    {P : CentralParameters U K} {κ : Type w} [DecidableEq κ]
    {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    (family : CentralFieldTwoCallFamily (T := T) (V := V) P κ D defect)
    (lower : StrongPh D h defect) :
    StrongPh D (h + 1) defect := by
  intro d hd A Ω hΩ
  let step := family h lower d hd A Ω hΩ
  exact step.data.central_field_witness step.certificate

end Step

section Endpoint

variable {K : Type v} [Field K] [Infinite K]
variable {κ : Type w} [DecidableEq κ]
variable {T : Type x} {V : Type y}

/-- Integer-defect finite-index endpoint assembled from a supplied base and
the central-field two-call family.  The recursion is the same finite-index
climb as `FiniteIndex`, but its successor is constructed from polynomial
roots and the explicit carried-test/support certificate at each step. -/
noncomputable def strongPh_fin_index_of_central_field_two_call
    {P : CentralParameters U K} (κ : Type w) [DecidableEq κ]
    (D : Nat) (defect : U → U → List (LocalTest U T V) → Int)
    (base : BaseProducer D defect)
    (family : CentralFieldTwoCallFamily (T := T) (V := V) P κ D defect) :
    StrongPh D (D + 1) defect := by
  let baseStrong : StrongPh D 1 defect := base_producer_strongPh base
  let rec climb (n : Nat) : StrongPh D (1 + n) defect :=
    match n with
    | 0 => baseStrong
    | n + 1 => central_field_successor_of_family
        (family := family) (h := 1 + n) (climb n)
  exact cast (congrArg (fun h : Nat => StrongPh D h defect)
    (Nat.add_comm 1 D)) (climb D)

/-- The endpoint in the named finite-index package, retaining the complete
`StrongPh` witness family for downstream consumers. -/
noncomputable def central_field_finite_index_endpoint
    {P : CentralParameters U K} (κ : Type w) [DecidableEq κ]
    (D : Nat) (defect : U → U → List (LocalTest U T V) → Int)
    (base : BaseProducer D defect)
    (family : CentralFieldTwoCallFamily (T := T) (V := V) P κ D defect) :
    FiniteIndexEndpoint D defect :=
  ⟨strongPh_fin_index_of_central_field_two_call κ D defect base family⟩

/-- Terminal original-ring extraction from the central-field finite-index
endpoint.  The zero-extraction bridge is deliberately still explicit. -/
noncomputable def terminal_cofactors_of_central_field_finite_index
    {P : CentralParameters U K} (κ : Type w) [DecidableEq κ]
    (D : Nat) (defect : U → U → List (LocalTest U T V) → Int)
    (base : BaseProducer D defect)
    (family : CentralFieldTwoCallFamily (T := T) (V := V) P κ D defect)
    (zero_extraction : ∀ {d f : U} {Ω : List (LocalTest U T V)},
      defect d f Ω ≤ -1 → OriginalCofactors d f)
    (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U T V))
    (hΩ : AdmissibleTestList d Ω) :
    OriginalCofactors d
      (strongPh_fin_index_of_central_field_two_call κ D defect base family
        d hd A Ω hΩ).source := by
  apply zero_extraction
  rw [← defectBound_terminal D]
  exact (strongPh_fin_index_of_central_field_two_call κ D defect base family
    d hd A Ω hΩ).defect_bound

end Endpoint

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.strongPh_fin_index_of_central_field_two_call
#print axioms SymplecticStafford.Induction.central_field_finite_index_endpoint
#print axioms SymplecticStafford.Induction.terminal_cofactors_of_central_field_finite_index
