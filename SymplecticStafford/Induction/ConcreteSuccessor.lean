module

public import SymplecticStafford.Induction.TestRetention
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Concrete conditional two-call successor contract

`StrongPh` already records the abstract lower-index call.  This file gives a
more concrete M09--M10 assembly boundary: the old and new local tests are
finite `Fin`-indexed families, each family has an explicit finite input list
and coverage proof, and the two supplied lower-call witnesses are tied to
those inputs.  A separate carried list is related to both inputs, so test
retention is an actual list-membership obligation rather than an implicit
claim about a changed auxiliary divisor.

The output witness and defect equalities remain supplied fields.  Thus this
module does not prove the paper's support construction, source producer, base
case, scalar avoidance, or universal successor theorem.
-/

namespace SymplecticStafford.Induction

universe u v w x y

variable {U : Type u} [Semiring U]

/-! ## Explicit finite old/new families -/

/-- A finite family of lists covering a displayed finite input list.

The index type is `Fin n`; when `n = 0`, the coverage field forces the input
list to be empty.  Admissibility is attached to every family member, not
merely to the union, so a client cannot hide an inadmissible local test in a
family slot.
-/
structure IndexedTestFamily
    (δ : Type v) (Test : Type w)
    (Adm : δ → Test → Prop)
    (d : δ) (n : Nat) where
  input : List Test
  family : Fin n → List Test
  input_admissible : ∀ t, t ∈ input → Adm d t
  family_admissible : ∀ i t, t ∈ family i → Adm d t
  covers_input : ∀ t, t ∈ input → ∃ i : Fin n, t ∈ family i

theorem IndexedTestFamily.member_of_family
    {δ : Type v} {Test : Type w}
    {Adm : δ → Test → Prop} {d : δ} {n : Nat}
    (f : IndexedTestFamily δ Test Adm d n)
    {t : Test} {i : Fin n} (ht : t ∈ f.family i) : Adm d t := by
  exact f.family_admissible i t ht

theorem IndexedTestFamily.covered_member
    {δ : Type v} {Test : Type w}
    {Adm : δ → Test → Prop} {d : δ} {n : Nat}
    (f : IndexedTestFamily δ Test Adm d n)
    {t : Test} (ht : t ∈ f.input) : ∃ i : Fin n, t ∈ f.family i := by
  exact f.covers_input t ht

/-- The two finite families used by a successor: old tests belong to the
first lower call, new tests to the second lower call. -/
structure OldNewIndexedFamilies
    (δ : Type v) (Test : Type w)
    (Adm : δ → Test → Prop)
    (oldDivisor newDivisor : δ)
    (oldCount newCount : Nat) where
  oldFamily : IndexedTestFamily δ Test Adm oldDivisor oldCount
  newFamily : IndexedTestFamily δ Test Adm newDivisor newCount

/-- Concrete certificate with explicit old/new finite family cardinalities.
This is the usual entry point for clients; it avoids any claim that a family
of tests is automatically produced from a lower call.
-/
structure ConcreteSuccessorData
    {T : Type v} {V : Type w}
    {Λ : Type x} (P : CentralParameters U Λ)
    (κ : Type y)
    (D h : Nat)
    (defect : U → U → List (LocalTest U T V) → Int)
    (lower : StrongPh D h defect)
    (d : U) (hd : d ≠ 0)
    (A : AffineSource U)
    (oldInput : List (LocalTest U T V))
    (oldInput_admissible : AdmissibleTestList d oldInput)
    (auxiliaryDivisor : U) (auxiliaryDivisor_nonzero : auxiliaryDivisor ≠ 0)
    (newInput : List (LocalTest U T V))
    (newInput_admissible : AdmissibleTestList auxiliaryDivisor newInput)
    (carried : List (LocalTest U T V))
    (carried_admissible : AdmissibleTestList d carried)
    (oldCount newCount : Nat) where
  oldFamily : IndexedTestFamily U (LocalTest U T V)
    (fun q t => t.Admissible q) d oldCount
  newFamily : IndexedTestFamily U (LocalTest U T V)
    (fun q t => t.Admissible q) auxiliaryDivisor newCount
  oldInput_eq_family_input : oldFamily.input = oldInput
  newInput_eq_family_input : newFamily.input = newInput
  oldCall : StrongPhWitness D h defect d A oldInput
  oldCall_eq_lower : oldCall = lower d hd A oldInput oldInput_admissible
  newAffine : AffineSource U
  newAffine_eq_homogeneous : newAffine = homogeneousAffine A.a A.a_nonzero
  newCall : StrongPhWitness D h defect auxiliaryDivisor newAffine newInput
  newCall_eq_lower : newCall = lower auxiliaryDivisor auxiliaryDivisor_nonzero
    newAffine newInput newInput_admissible
  carried_in_old : ListCarried carried oldInput
  carried_in_new : ListCarried carried newInput
  old_new_split : OldNewSplit κ
  arithmetic : TwoCallDefectArithmetic D h
  old_defect_eq : arithmetic.oldDefect = defect d oldCall.source oldInput
  new_defect_eq : arithmetic.newDefect =
    defect auxiliaryDivisor newCall.source newInput
  output : StrongPhWitness (D := D) (h := h + 1) defect d A carried
  output_defect_eq : arithmetic.outputDefect =
    defect d output.source carried

theorem ConcreteSuccessorData.old_family_covers
    {T : Type v} {V : Type w} {Λ : Type x} {κ : Type y}
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect} {d : U} {hd : d ≠ 0}
    {A : AffineSource U} {oldInput : List (LocalTest U T V)}
    {oldInput_admissible : AdmissibleTestList d oldInput}
    {auxiliaryDivisor : U} {auxiliaryDivisor_nonzero : auxiliaryDivisor ≠ 0}
    {newInput : List (LocalTest U T V)}
    {newInput_admissible : AdmissibleTestList auxiliaryDivisor newInput}
    {carried : List (LocalTest U T V)}
    {carried_admissible : AdmissibleTestList d carried}
    {oldCount newCount : Nat}
    (c : ConcreteSuccessorData P κ D h defect lower d hd A oldInput
    oldInput_admissible auxiliaryDivisor auxiliaryDivisor_nonzero newInput
      newInput_admissible carried carried_admissible oldCount newCount)
    {t : LocalTest U T V} (ht : t ∈ oldInput) :
    ∃ i : Fin oldCount, t ∈ c.oldFamily.family i := by
  have ht' : t ∈ c.oldFamily.input := by
    rw [c.oldInput_eq_family_input]
    exact ht
  exact c.oldFamily.covers_input t ht'

theorem ConcreteSuccessorData.new_family_covers
    {T : Type v} {V : Type w} {Λ : Type x} {κ : Type y}
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect} {d : U} {hd : d ≠ 0}
    {A : AffineSource U} {oldInput : List (LocalTest U T V)}
    {oldInput_admissible : AdmissibleTestList d oldInput}
    {auxiliaryDivisor : U} {auxiliaryDivisor_nonzero : auxiliaryDivisor ≠ 0}
    {newInput : List (LocalTest U T V)}
    {newInput_admissible : AdmissibleTestList auxiliaryDivisor newInput}
    {carried : List (LocalTest U T V)}
    {carried_admissible : AdmissibleTestList d carried}
    {oldCount newCount : Nat}
    (c : ConcreteSuccessorData P κ D h defect lower d hd A oldInput
    oldInput_admissible auxiliaryDivisor auxiliaryDivisor_nonzero newInput
      newInput_admissible carried carried_admissible oldCount newCount)
    {t : LocalTest U T V} (ht : t ∈ newInput) :
    ∃ i : Fin newCount, t ∈ c.newFamily.family i := by
  have ht' : t ∈ c.newFamily.input := by
    rw [c.newInput_eq_family_input]
    exact ht
  exact c.newFamily.covers_input t ht'

theorem ConcreteSuccessorData.retention
    {T : Type v} {V : Type w} {Λ : Type x} {κ : Type y}
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect} {d : U} {hd : d ≠ 0}
    {A : AffineSource U} {oldInput : List (LocalTest U T V)}
    {oldInput_admissible : AdmissibleTestList d oldInput}
    {auxiliaryDivisor : U} {auxiliaryDivisor_nonzero : auxiliaryDivisor ≠ 0}
    {newInput : List (LocalTest U T V)}
    {newInput_admissible : AdmissibleTestList auxiliaryDivisor newInput}
    {carried : List (LocalTest U T V)}
    {carried_admissible : AdmissibleTestList d carried}
    {oldCount newCount : Nat}
    (c : ConcreteSuccessorData P κ D h defect lower d hd A oldInput
      oldInput_admissible auxiliaryDivisor auxiliaryDivisor_nonzero newInput
      newInput_admissible carried carried_admissible oldCount newCount) :
    ∀ t, t ∈ carried →
      t.generation c.oldCall.source ∧ t.generation c.newCall.source := by
  intro t ht
  constructor
  · exact c.oldCall.tests_pass t (c.carried_in_old ht)
  · exact c.newCall.tests_pass t (c.carried_in_new ht)

theorem ConcreteSuccessorData.output_bound
    {T : Type v} {V : Type w} {Λ : Type x} {κ : Type y}
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect} {d : U} {hd : d ≠ 0}
    {A : AffineSource U} {oldInput : List (LocalTest U T V)}
    {oldInput_admissible : AdmissibleTestList d oldInput}
    {auxiliaryDivisor : U} {auxiliaryDivisor_nonzero : auxiliaryDivisor ≠ 0}
    {newInput : List (LocalTest U T V)}
    {newInput_admissible : AdmissibleTestList auxiliaryDivisor newInput}
    {carried : List (LocalTest U T V)}
    {carried_admissible : AdmissibleTestList d carried}
    {oldCount newCount : Nat}
    (c : ConcreteSuccessorData P κ D h defect lower d hd A oldInput
      oldInput_admissible auxiliaryDivisor auxiliaryDivisor_nonzero newInput
      newInput_admissible carried carried_admissible oldCount newCount) :
    defect d c.output.source carried ≤ defectBound D (h + 1) := by
  rw [← c.output_defect_eq]
  exact c.arithmetic.output_bound

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.ConcreteSuccessorData.retention
#print axioms SymplecticStafford.Induction.ConcreteSuccessorData.output_bound
