module

public import SymplecticStafford.Induction.CentralFieldSupportRemoval
public import SymplecticStafford.Induction.FiniteRemovalRetentionBridge

@[expose] public section

/-!
# Central-field polynomial two-call successor

This is the composition layer between polynomial local certificates and the
two-call successor assembly.  An actual `TwoCallDescentData` supplies the
support map, lower calls, and original affine source.  The local module adds
one nonzero polynomial for each old support component and carried test,
together with the two source-dependent implications.  The adapter turns
these polynomials into the finite exceptional sets required by
`FiniteRemovalRetentionBridge`, whose witness constructor then produces the
next `StrongPhWitness`.

No support-removal or module-generation theorem is hidden here: those remain
the exact fields `strict_support_of_good` and `pencil_generation_of_good`.
-/

namespace SymplecticStafford.Induction

universe u v w x y

variable {U : Type u} [Semiring U]

section

variable {K : Type v} [Field K] [Infinite K]
variable {κ : Type w} [DecidableEq κ]
variable {T : Type x} {V : Type y}

/-- Polynomial bad-parameter certificates attached to an actual two-call
datum.  The old and new sources are the two lower-index calls stored in
`data`; the support map is therefore the same map used by its defect bound. -/
structure CentralFieldTwoCallData
    {P : CentralParameters U K} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U T V)}
    {hΩ : AdmissibleTestList d Ω}
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ) where
  componentPolynomial : κ → Polynomial K
  testPolynomial : LocalTest U T V → Polynomial K
  componentPolynomial_ne_zero : ∀ p,
    p ∈ data.support d (lower d hd A Ω hΩ).source Ω →
      componentPolynomial p ≠ 0
  testPolynomial_ne_zero : ∀ t, t ∈ Ω → testPolynomial t ≠ 0
  strict_support_of_good : ∀ z : K,
    (∀ p, p ∈ data.support d (lower d hd A Ω hΩ).source Ω →
      (componentPolynomial p).eval z ≠ 0) →
      data.support d
          (pencilMember P (lower d hd A Ω hΩ).source
            (lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
              (homogeneousAffine A.a A.a_nonzero) data.newInput
              data.newInput_admissible).source z) Ω ⊂
        data.support d (lower d hd A Ω hΩ).source Ω
  pencil_generation_of_good : ∀ z : K,
    (∀ p, p ∈ data.support d (lower d hd A Ω hΩ).source Ω →
      (componentPolynomial p).eval z ≠ 0) →
    (∀ t, t ∈ Ω → (testPolynomial t).eval z ≠ 0) →
    ∀ t, t ∈ Ω →
      t.generation (lower d hd A Ω hΩ).source →
      t.generation
        (lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
          (homogeneousAffine A.a A.a_nonzero) data.newInput
          data.newInput_admissible).source →
      t.generation
        (pencilMember P (lower d hd A Ω hΩ).source
          (lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
            (homogeneousAffine A.a A.a_nonzero) data.newInput
            data.newInput_admissible).source z)

/-- Convert the polynomial certificate into the finite-exception interface.
The only finiteness argument is the central-field fact that a nonzero
polynomial has finitely many roots. -/
def CentralFieldTwoCallData.toFiniteRemovalRetentionData
    {P : CentralParameters U K} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U T V)}
    {hΩ : AdmissibleTestList d Ω}
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ)
    (c : CentralFieldTwoCallData (κ := κ) data) :
    FiniteRemovalRetentionData data := by
  let old := lower d hd A Ω hΩ
  let new := lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
    (homogeneousAffine A.a A.a_nonzero) data.newInput
    data.newInput_admissible
  refine {
    componentBad := fun p z => (c.componentPolynomial p).eval z = 0
    testBad := fun t z => (c.testPolynomial t).eval z = 0
    component_finite := ?_
    test_finite := ?_
    strict_support_of_good := ?_
    pencil_generation_of_good := ?_ }
  · intro p hp
    exact finite_eval_zero_set (c.componentPolynomial_ne_zero p hp)
  · intro t ht
    exact finite_eval_zero_set (c.testPolynomial_ne_zero t ht)
  · intro z hgood
    apply c.strict_support_of_good z
    intro p hp hzero
    exact hgood p hp hzero
  · intro z hgood htests t ht hF hG
    apply c.pencil_generation_of_good z ?_ ?_ t ht hF hG
    · intro p hp hzero
      exact hgood p hp hzero
    · intro t' ht' hzero
      exact htests t' ht' hzero

end

section Successor

variable {K : Type v} [Field K] [Infinite K]
variable {κ : Type w} [DecidableEq κ]
variable {T : Type x} {V : Type y}

/-- Assemble the next-index witness from an actual two-call datum and the
central-field polynomial local certificate.  The bridge chooses one scalar,
retains every carried test, and reconstructs the original affine coefficient
through the existing `TwoCallDescentData` witness constructor. -/
noncomputable def TwoCallDescentData.central_field_witness
    {P : CentralParameters U K} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U T V)}
    {hΩ : AdmissibleTestList d Ω}
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ)
    (c : CentralFieldTwoCallData (κ := κ) data) :
    StrongPhWitness (D := D) (h := h + 1) defect d A Ω := by
  exact (CentralFieldTwoCallData.toFiniteRemovalRetentionData data c).witness

theorem TwoCallDescentData.central_field_witness_source_eq
    {P : CentralParameters U K} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U T V)}
    {hΩ : AdmissibleTestList d Ω}
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ)
    (c : CentralFieldTwoCallData (κ := κ) data) :
    (data.central_field_witness c).source =
      A.B + (data.central_field_witness c).H * A.a :=
  (data.central_field_witness c).source_eq

end Successor

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.CentralFieldTwoCallData.toFiniteRemovalRetentionData
#print axioms SymplecticStafford.Induction.TwoCallDescentData.central_field_witness
