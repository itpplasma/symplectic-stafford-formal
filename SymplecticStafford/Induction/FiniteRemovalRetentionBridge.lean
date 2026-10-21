module

public import SymplecticStafford.Induction.FiniteScalarAvoidance

@[expose] public section

/-!
# Component/test finite-exception bridge for the two-call successor

`FiniteScalarAvoidance` chooses one scalar outside finitely many component and
test exceptions.  This file connects that choice to the successor only
through indexed support-removal and indexed test-retention laws.  Thus the
successor witness is not supplied by the bridge: its source, affine
coefficient, and defect bound are constructed after the common scalar is
chosen.

The two indexed laws are the remaining mathematical input.  They are stated
at the exact finite-support and carried-test interfaces used by
`TwoCallDescentData`, so a client cannot replace them by a finite scalar count
or by a pre-built next-index witness.
-/

namespace SymplecticStafford.Induction

universe u v w x y

variable {U : Type u} [Semiring U]

section Bridge

variable {Λ : Type x} {κ : Type y} [Infinite Λ] [DecidableEq κ]

/-- Component- and test-indexed facts sufficient to consume the joint scalar
selection theorem for one actual two-call datum. -/
structure FiniteRemovalRetentionData
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U v w)} {hΩ : AdmissibleTestList d Ω}
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ) where
  componentBad : κ → Λ → Prop
  testBad : LocalTest U v w → Λ → Prop
  component_finite : ∀ a,
    a ∈ data.support d (lower d hd A Ω hΩ).source Ω →
    Set.Finite {z : Λ | componentBad a z}
  test_finite : ∀ t, t ∈ Ω →
    Set.Finite {z : Λ | testBad t z}
  /-- Indexed avoidance removes a support component from the old support. -/
  strict_support_of_good : ∀ z : Λ,
    (∀ a, a ∈ data.support d (lower d hd A Ω hΩ).source Ω →
      ¬ componentBad a z) →
      data.support d
          (pencilMember P (lower d hd A Ω hΩ).source
            (lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
              (homogeneousAffine A.a A.a_nonzero) data.newInput
              data.newInput_admissible).source z) Ω
        ⊂ data.support d (lower d hd A Ω hΩ).source Ω
  /-- Indexed avoidance retains each carried local generation test. -/
  pencil_generation_of_good : ∀ z : Λ,
    (∀ a, a ∈ data.support d (lower d hd A Ω hΩ).source Ω →
      ¬ componentBad a z) →
    (∀ t, t ∈ Ω → ¬ testBad t z) →
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

/-- Build the next-index witness from exact component/test finite-exception
data.  The old source is the first lower call and the auxiliary source is the
second lower call, both at index `h`. -/
noncomputable def FiniteRemovalRetentionData.witness
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U v w)} {hΩ : AdmissibleTestList d Ω}
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ)
    (retention : FiniteRemovalRetentionData data) :
    StrongPhWitness (D := D) (h := h + 1) defect d A Ω := by
  let z : Λ := Classical.choose (exists_scalar_avoiding_finset_list
    (data.support d (lower d hd A Ω hΩ).source Ω) Ω
    retention.componentBad retention.testBad data.exceptional
    retention.component_finite retention.test_finite data.exceptional_finite)
  have hz := Classical.choose_spec (exists_scalar_avoiding_finset_list
    (data.support d (lower d hd A Ω hΩ).source Ω) Ω
    retention.componentBad retention.testBad data.exceptional
    retention.component_finite retention.test_finite data.exceptional_finite)
  rcases hz with ⟨hzbase, hzcomp, hztest⟩
  let old := lower d hd A Ω hΩ
  let new := lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
    (homogeneousAffine A.a A.a_nonzero) data.newInput
    data.newInput_admissible
  have hnew_mem :
      (homogeneousAffine A.a A.a_nonzero).member new.source :=
    new.affine_member
  have hout_mem : A.member (pencilMember P old.source new.source z) :=
    affine_member_pencil_of_members P A old.affine_member hnew_mem
  let Hout : U := Classical.choose hout_mem
  have hsource : pencilMember P old.source new.source z =
      A.B + Hout * A.a := Classical.choose_spec hout_mem
  have hstrict := retention.strict_support_of_good z hzcomp
  have hbound :
      defect d (pencilMember P old.source new.source z) Ω ≤
        defectBound D (h + 1) := by
    rw [data.defect_eq_support]
    calc
      finiteSupportDefect
          (data.support d (pencilMember P old.source new.source z) Ω) ≤
          finiteSupportDefect (data.support d old.source Ω) - 1 :=
        finiteSupportDefect_le_sub_one_of_ssubset hstrict
      _ ≤ defectBound D h - 1 :=
        sub_le_sub_right (data.lower_support_bound) 1
      _ = defectBound D (h + 1) := (defectBound_succ D h).symm
  have hgen : ∀ t, t ∈ Ω →
      t.generation old.source → t.generation new.source →
      t.generation (pencilMember P old.source new.source z) := by
    intro t ht hF hG
    exact retention.pencil_generation_of_good z hzcomp hztest t ht hF hG
  refine {
    H := Hout
    source := pencilMember P old.source new.source z
    source_eq := hsource
    defect_bound := by simpa [old, new] using hbound
    tests_pass := ?_ }
  intro t ht
  apply hgen t ht
  · exact old.tests_pass t ht
  · exact new.tests_pass t (data.carried_in_new ht)

end Bridge

section Producer

variable {Λ : Type x} {κ : Type y} [Infinite Λ]

/-- A producer that supplies only raw two-call data plus indexed finite
support/test removal laws. -/
def FiniteRemovalRetentionProducer
    (P : CentralParameters U Λ) (κ : Type y)
    (D h : Nat)
    (defect : U → U → List (LocalTest U v w) → Int)
    (lower : StrongPh D h defect)
    [DecidableEq κ]
    (raw : TwoCallDescentProducer P κ D h defect lower)
    : Type _ :=
  ∀ (d : U), (hd : d ≠ 0) → ∀ (A : AffineSource U)
    (Ω : List (LocalTest U v w)),
    (hΩ : AdmissibleTestList d Ω) →
    FiniteRemovalRetentionData (raw d hd A Ω hΩ)

/-- Consume a raw producer and its indexed finite-exception laws. -/
noncomputable def strongPh_succ_of_finite_removal_retention
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    [DecidableEq κ]
    (raw : TwoCallDescentProducer P κ D h defect lower)
    (retention : FiniteRemovalRetentionProducer P κ D h defect lower raw) :
    StrongPh D (h + 1) defect := by
  intro d hd A Ω hΩ
  exact (retention d hd A Ω hΩ).witness

end Producer

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.FiniteRemovalRetentionData.witness
#print axioms SymplecticStafford.Induction.strongPh_succ_of_finite_removal_retention
