import SymplecticStafford.Induction.TwoCallAffineProducer
import SymplecticStafford.Induction.SupportRemovalArithmetic
import Mathlib.Data.Set.Finite.Basic

/-!
# A descent-level two-call producer

`TwoCallAffineProducer` already assembles a successor once a defect bound and
a pencil-generation implication have been supplied.  This file moves that
boundary one step back.  A `TwoCallDescentData` record supplies the actual
lower calls, a finite exceptional-scalar set, and a strict finite-support
decrease.  The successor source, its affine coefficient, its defect bound and
its carried-test conclusion are then constructed by theorems below; none of
those four output witnesses is a field of the data record.

The strict-support and pencil-stability fields are deliberately exposed as
mathematical inputs.  They are the remaining M09--M10 geometric/module
obligations, not renamed `StrongPhWitness` fields.  In particular, a finite
exceptional set is avoided using the actual `Infinite Λ` hypothesis.
-/

namespace SymplecticStafford.Induction

universe u v w x y

variable {U : Type u} [Semiring U]

section Descent

variable {Λ : Type x} {κ : Type y}

/-- Raw two-call input for one successor step.  The two recursive witnesses
are obtained by applying `lower`; only the auxiliary divisor/test lists,
actual support map and scalar exceptional set are supplied. -/
structure TwoCallDescentData
    {κ : Type y} [DecidableEq κ]
    (P : CentralParameters U Λ) (D h : Nat)
    (defect : U → U → List (LocalTest U v w) → Int)
    (lower : StrongPh D h defect)
    (d : U) (hd : d ≠ 0)
    (A : AffineSource U) (Ω : List (LocalTest U v w))
    (hΩ : AdmissibleTestList d Ω) where
  L0 : U
  C0 : U
  auxiliaryDivisor : U
  auxiliaryDivisor_eq : auxiliaryDivisor = d * L0
  auxiliaryDivisor_nonzero : auxiliaryDivisor ≠ 0
  old_relation : (lower d hd A Ω hΩ).source * d * L0 = d * C0
  newInput : List (LocalTest U v w)
  newInput_admissible : AdmissibleTestList auxiliaryDivisor newInput
  carried_in_new : ListCarried Ω newInput
  /-- The finite support proxy is an actual function, not a defect field. -/
  support : U → U → List (LocalTest U v w) → Finset κ
  defect_eq_support : ∀ (q f : U) (xs : List (LocalTest U v w)),
    defect q f xs = finiteSupportDefect (support q f xs)
  exceptional : Set Λ
  exceptional_finite : exceptional.Finite
  /-- Every scalar outside the finite exceptional set removes a component. -/
  strict_support : ∀ z : Λ,
    z ∉ exceptional →
      support d
          (pencilMember P (lower d hd A Ω hΩ).source
            (lower auxiliaryDivisor auxiliaryDivisor_nonzero
              (homogeneousAffine A.a A.a_nonzero) newInput
              newInput_admissible).source z) Ω
        ⊂ support d (lower d hd A Ω hΩ).source Ω
  /-- The same non-exceptional scalar retains every carried local test. -/
  pencil_generation : ∀ (z : Λ) (t : LocalTest U v w),
    z ∉ exceptional → t ∈ Ω →
      t.generation (lower d hd A Ω hΩ).source →
      t.generation
        (lower auxiliaryDivisor auxiliaryDivisor_nonzero
          (homogeneousAffine A.a A.a_nonzero) newInput
          newInput_admissible).source →
      t.generation
        (pencilMember P (lower d hd A Ω hΩ).source
          (lower auxiliaryDivisor auxiliaryDivisor_nonzero
            (homogeneousAffine A.a A.a_nonzero) newInput
            newInput_admissible).source z)

theorem TwoCallDescentData.lower_support_bound
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U v w)} {hΩ : AdmissibleTestList d Ω}
    [DecidableEq κ]
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ) :
    finiteSupportDefect (α := κ)
      (data.support d (lower d hd A Ω hΩ).source Ω) ≤
      defectBound D h := by
  rw [← data.defect_eq_support]
  exact (lower d hd A Ω hΩ).defect_bound

theorem TwoCallDescentData.pencil_bound
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U v w)} {hΩ : AdmissibleTestList d Ω}
    [DecidableEq κ]
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ)
    {z : Λ} (hz : z ∉ data.exceptional) :
    defect d
        (pencilMember P (lower d hd A Ω hΩ).source
          (lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
            (homogeneousAffine A.a A.a_nonzero) data.newInput
            data.newInput_admissible).source z) Ω ≤
      defectBound D (h + 1) := by
  rw [data.defect_eq_support]
  calc
    finiteSupportDefect (α := κ)
        (data.support d
          (pencilMember P (lower d hd A Ω hΩ).source
            (lower data.auxiliaryDivisor data.auxiliaryDivisor_nonzero
              (homogeneousAffine A.a A.a_nonzero) data.newInput
              data.newInput_admissible).source z) Ω) ≤
        finiteSupportDefect (α := κ)
          (data.support d (lower d hd A Ω hΩ).source Ω) - 1 :=
      finiteSupportDefect_le_sub_one_of_ssubset (data.strict_support z hz)
    _ ≤ defectBound D h - 1 :=
      sub_le_sub_right data.lower_support_bound 1
    _ = defectBound D (h + 1) := (defectBound_succ D h).symm

theorem TwoCallDescentData.pencil_tests
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U v w)} {hΩ : AdmissibleTestList d Ω}
    [DecidableEq κ]
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ)
    {z : Λ} (hz : z ∉ data.exceptional) :
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
            data.newInput_admissible).source z) := by
  intro t ht hF hG
  exact data.pencil_generation z t hz ht hF hG

/-- Construct one next-index witness from raw two-call descent data. -/
noncomputable def TwoCallDescentData.witness
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U v w)} {hΩ : AdmissibleTestList d Ω}
    [Infinite Λ] [DecidableEq κ]
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ) :
    StrongPhWitness (D := D) (h := h + 1) defect d A Ω := by
  let z : Λ := Classical.choose data.exceptional_finite.exists_notMem
  have hz : z ∉ data.exceptional :=
    Classical.choose_spec data.exceptional_finite.exists_notMem
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
  refine {
    H := Hout
    source := pencilMember P old.source new.source z
    source_eq := hsource
    defect_bound := ?_
    tests_pass := ?_ }
  · simpa [old, new] using data.pencil_bound hz
  · intro t ht
    apply data.pencil_tests hz t ht
    · exact old.tests_pass t ht
    · exact new.tests_pass t (data.carried_in_new ht)

end Descent

section Producer

variable {Λ : Type x} {κ : Type y} [Infinite Λ] [DecidableEq κ]

/-- A producer of raw two-call descent data.  It has no next-index witness
field; the witness is constructed by `TwoCallDescentData.witness`. -/
def TwoCallDescentProducer
    (P : CentralParameters U Λ) (κ : Type y)
    (D h : Nat)
    (defect : U → U → List (LocalTest U v w) → Int)
    (lower : StrongPh D h defect) [DecidableEq κ] : Type _ :=
  ∀ (d : U), (hd : d ≠ 0) → ∀ (A : AffineSource U)
    (Ω : List (LocalTest U v w)),
    (hΩ : AdmissibleTestList d Ω) →
    TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ

noncomputable def strongPh_succ_of_two_call_descent
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    (producer : TwoCallDescentProducer P κ D h defect lower) :
    StrongPh D (h + 1) defect := by
  intro d hd A Ω hΩ
  let data := producer d hd A Ω hΩ
  exact data.witness

/-- Raw descent producers for every induction index.  Each member is still a
two-call producer, so the family does not smuggle a pre-built successor rule
or endpoint witness into the finite-index induction. -/
def TwoCallDescentFamily
    (P : CentralParameters U Λ) (κ : Type y) [DecidableEq κ]
    (D : Nat)
    (defect : U → U → List (LocalTest U v w) → Int) : Type _ :=
  ∀ h : Nat, ∀ (lower : StrongPh D h defect),
    TwoCallDescentProducer P κ D h defect lower

noncomputable def twoCallDescent_strong_family
    {P : CentralParameters U Λ} {D : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    (family : TwoCallDescentFamily P κ D defect) :
    ∀ h : Nat, StrongPh D h defect → StrongPh D (h + 1) defect := by
  intro h lower
  exact strongPh_succ_of_two_call_descent (family h lower)

/-- The two-call family composes with the existing finite-index recursion. -/
noncomputable def strongPh_fin_index_of_two_call_descent
    {P : CentralParameters U Λ} {D : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    (base : StrongPh D 1 defect)
    (family : TwoCallDescentFamily P κ D defect) :
    StrongPh D (D + 1) defect := by
  let rec climb (n : Nat) : StrongPh D (1 + n) defect :=
    match n with
    | 0 => base
    | n + 1 => twoCallDescent_strong_family family (1 + n) (climb n)
  exact cast (congrArg (fun h : Nat => StrongPh D h defect) (Nat.add_comm 1 D))
    (climb D)

/-- Terminal original-ring cofactors after composing raw two-call descent
producers.  The only remaining input is the independently audited
zero-defect-to-cofactor bridge. -/
noncomputable def terminal_cofactors_of_two_call_descent
    {P : CentralParameters U Λ} {D : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    (base : StrongPh D 1 defect)
    (family : TwoCallDescentFamily P κ D defect)
    (zero_extraction : ∀ {d f : U} {Ω : List (LocalTest U v w)},
      defect d f Ω ≤ -1 → OriginalCofactors d f)
    (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U v w))
    (hΩ : AdmissibleTestList d Ω) :
    OriginalCofactors d
      (strongPh_fin_index_of_two_call_descent base family d hd A Ω hΩ).source := by
  apply zero_extraction
  rw [← defectBound_terminal D]
  exact (strongPh_fin_index_of_two_call_descent base family d hd A Ω hΩ).defect_bound

end Producer

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.TwoCallDescentData.witness
#print axioms SymplecticStafford.Induction.strongPh_succ_of_two_call_descent
#print axioms SymplecticStafford.Induction.strongPh_fin_index_of_two_call_descent
#print axioms SymplecticStafford.Induction.terminal_cofactors_of_two_call_descent
