import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum

/-!
# Conditional strong finite-test induction contracts

This file is the formal boundary for paper obligations M09--M10.  It records
the data which a future producer proof must supply; it does not assert the
producer for an admissible algebra, and it does not hide that producer behind
an axiom or an imported theorem.

In particular, a test carries its actual localization, finite-length cyclic
module, canonical generator, nonzero right tail and offset.  A successor
certificate exposes both lower-index calls, the auxiliary divisor relation,
the old/new component split, and retention of the carried tests.  The
termination interface separately supplies the final original-ring cofactors.
-/

namespace SymplecticStafford.Induction

universe u v w x y

variable {U : Type u} [Semiring U]

/-- An affine source space `B + U a`, with the nonzero-tail hypothesis made
explicit.  The multiplication order is the paper's order. -/
structure AffineSource (U : Type u) [Semiring U] where
  B : U
  a : U
  a_nonzero : a ≠ 0

def AffineSource.member (A : AffineSource U) (f : U) : Prop :=
  ∃ H : U, f = A.B + H * A.a

def homogeneousAffine (a : U) (ha : a ≠ 0) : AffineSource U :=
  ⟨0, a, ha⟩

theorem homogeneousAffine_member (a : U) (ha : a ≠ 0) (H : U) :
    (homogeneousAffine a ha).member (H * a) := by
  exact ⟨H, by simp [homogeneousAffine]⟩

/-- Concrete data retained for one local finite-length test.

The three specification propositions are intentionally fields rather than
global instances.  Their proof fields force a caller to provide the actual
localization, finite-length cyclicity, and canonical-generator evidence.
`generation` is the exact local generation predicate to be checked for a
chosen source; it contains no existential source selection. -/
structure LocalTest (U : Type u) [Semiring U]
    (T : Type v) (V : Type w) where
  targetDivisor : U
  localization : T
  cyclicModule : V
  canonicalGenerator : V
  rightTail : U
  offset : Int
  localization_spec : Prop
  localization_spec_proof : localization_spec
  finite_length_cyclic_spec : Prop
  finite_length_cyclic_proof : finite_length_cyclic_spec
  canonical_generator_spec : Prop
  canonical_generator_spec_proof : canonical_generator_spec
  rightTail_nonzero : rightTail ≠ 0
  generation : U → Prop

def LocalTest.Admissible (d : U) (t : LocalTest U T V) : Prop :=
  t.targetDivisor = d ∧
    t.localization_spec ∧
    t.finite_length_cyclic_spec ∧
    t.canonical_generator_spec ∧
    t.rightTail ≠ 0

theorem LocalTest.admissible_of_fields (d : U)
    (t : LocalTest U T V) (ht : t.targetDivisor = d) :
    t.Admissible d := by
  exact ⟨ht, t.localization_spec_proof, t.finite_length_cyclic_proof,
    t.canonical_generator_spec_proof, t.rightTail_nonzero⟩

/-- The explicit finite-test-list predicate used by `P_h`.  Lists are finite
by construction; no finiteness or admissibility is inferred from a typeclass.
-/
def AdmissibleTestList (d : U) (Ω : List (LocalTest U T V)) : Prop :=
  ∀ t, t ∈ Ω → t.Admissible d

theorem admissibleTestList_nil (d : U) :
    AdmissibleTestList d ([] : List (LocalTest U T V)) := by
  intro t ht
  simp at ht

theorem admissibleTestList_cons {d : U} {t : LocalTest U T V}
    {Ω : List (LocalTest U T V)}
    (ht : t.Admissible d) (hΩ : AdmissibleTestList d Ω) :
    AdmissibleTestList d (t :: Ω) := by
  intro t' ht'
  simp only [List.mem_cons] at ht'
  rcases ht' with rfl | ht'
  · exact ht
  · exact hΩ t' ht'

/-- The bottom-extended defect bound.  In particular, the terminal index
`D+1` has bound `-1`, rather than a truncated natural subtraction. -/
def defectBound (D h : Nat) : Int := (D : Int) - (h : Int)

theorem defectBound_terminal (D : Nat) : defectBound D (D + 1) = -1 := by
  norm_num [defectBound]

/-- Literal original-ring cofactors for a selected source. -/
structure OriginalCofactors (d f : U) where
  R : U
  S : U
  identity : (1 : U) = d * R + (f * d) * S

/-- The witness returned by one strong `P_h` call.  It includes the affine
source coefficient, the defect bound, and every carried test's generation
certificate. -/
structure StrongPhWitness
    (D h : Nat)
    (defect : U → U → List (LocalTest U T V) → Int)
    (d : U) (A : AffineSource U)
    (Ω : List (LocalTest U T V)) where
  H : U
  source : U
  source_eq : source = A.B + H * A.a
  defect_bound : defect d source Ω ≤ defectBound D h
  tests_pass : ∀ t, t ∈ Ω → t.generation source

/-- Strong `P_h`, stated as a witness-producing contract.  This is a
conditional interface: it is not instantiated for the paper's admissible
class in this checkpoint. -/
def StrongPh
    (D h : Nat)
    (defect : U → U → List (LocalTest U T V) → Int) : Type _ :=
  ∀ (d : U), d ≠ 0 → ∀ (A : AffineSource U)
    (Ω : List (LocalTest U T V)),
    AdmissibleTestList d Ω → StrongPhWitness D h defect d A Ω

theorem StrongPhWitness.affine_member
    {D h : Nat} {defect : U → U → List (LocalTest U T V) → Int}
    {d : U} {A : AffineSource U}
    {Ω : List (LocalTest U T V)}
  (w : StrongPhWitness D h defect d A Ω) :
    A.member w.source := by
  exact ⟨w.H, w.source_eq⟩

/-- A central-parameter carrier for the pencil step.  The carrier is kept
abstract: a concrete proof must supply the parameter map and centrality in the
actual algebra. -/
structure CentralParameters (U : Type u) [Semiring U] (Λ : Type v) where
  embed : Λ → U
  central : ∀ (scalar : Λ) (x : U), embed scalar * x = x * embed scalar

def pencilMember {Λ : Type v} (P : CentralParameters U Λ)
    (F G : U) (scalar : Λ) : U := F + P.embed scalar * G

/-- A certificate for the `h → h+1` construction.

The fields expose both calls to the lower-index contract, the exact relation
`F*d*L0 = d*C0`, explicit old/new component lists and their split, a central
pencil parameter, and all carried-test obligations.  `output` is deliberately
supplied: this structure is an assembly contract, not a proof of the paper's
successor theorem. -/
structure SuccessorCertificate
    {T : Type v} {V : Type w}
    {Λ : Type x} {P : CentralParameters U Λ}
    {κ : Type y}
    (D h : Nat)
    (defect : U → U → List (LocalTest U T V) → Int)
    (lower : StrongPh D h defect)
    (d : U) (hd : d ≠ 0)
    (A : AffineSource U)
    (Ω : List (LocalTest U T V))
    (hΩ : AdmissibleTestList d Ω) where
  L0 : U
  C0 : U
  auxiliaryDivisor : U
  auxiliaryDivisor_eq : auxiliaryDivisor = d * L0
  auxiliaryDivisor_nonzero : auxiliaryDivisor ≠ 0
  old_relation :
    (lower d hd A Ω hΩ).source * d * L0 = d * C0
  oldTests : List (LocalTest U T V)
  oldTests_admissible :
    AdmissibleTestList auxiliaryDivisor oldTests
  auxiliary : StrongPhWitness D h defect auxiliaryDivisor
    (homogeneousAffine A.a A.a_nonzero) oldTests
  auxiliary_is_lower_call :
    auxiliary = lower auxiliaryDivisor auxiliaryDivisor_nonzero
      (homogeneousAffine A.a A.a_nonzero) oldTests oldTests_admissible
  oldComponents : List κ
  newComponents : List κ
  commonComponents : List κ
  old_new_disjoint : ∀ p, p ∈ oldComponents → p ∉ newComponents
  old_new_cover : ∀ p, p ∈ oldComponents ++ newComponents →
    p ∈ oldComponents ∨ p ∈ newComponents
  common_component_cover : ∀ p, p ∈ commonComponents →
    p ∈ oldComponents ∨ p ∈ newComponents
  commonDefect : Int
  common_defect_bound : commonDefect ≤ defectBound D h
  componentExceptional : κ → Λ → Prop
  testExceptional : LocalTest U T V → Λ → Prop
  parameter : Λ
  parameter_good : Prop
  parameter_good_proof : parameter_good
  parameter_avoids_components : ∀ p, p ∈ commonComponents →
    ¬ componentExceptional p parameter
  parameter_retains_tests : ∀ t, t ∈ Ω → ¬ testExceptional t parameter
  output : StrongPhWitness (D := D) (h := h + 1) defect d A Ω
  output_source_pencil :
    output.source = pencilMember P
      (lower d hd A Ω hΩ).source auxiliary.source parameter
  carried_tests_retained : ∀ t, t ∈ Ω → t.generation output.source

/-- A direct successor rule.  It returns explicit certificates for every
target datum, so its use cannot silently introduce an existential producer. -/
def SuccessorRule
    {T : Type v} {V : Type w}
    {Λ : Type x} (P : CentralParameters U Λ)
    (κ : Type y)
    (D h : Nat)
    (defect : U → U → List (LocalTest U T V) → Int)
    (lower : StrongPh D h defect) : Type _ :=
  ∀ (d : U), (hd : d ≠ 0) → ∀ (A : AffineSource U)
    (Ω : List (LocalTest U T V)),
    (hΩ : AdmissibleTestList d Ω) →
    SuccessorCertificate (P := P) (κ := κ) D h defect lower d hd A Ω hΩ

def strongPh_succ
    {T : Type v} {V : Type w}
    {Λ : Type x} (P : CentralParameters U Λ)
    (κ : Type y)
    {D h : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    {lower : StrongPh D h defect}
    (rule : SuccessorRule P κ D h defect lower) :
    StrongPh D (h + 1) defect := by
  intro d hd A Ω hΩ
  exact (rule d hd A Ω hΩ).output

/-- The explicit terminal extraction hypothesis.  It is the final original-U
bridge from bottom support dimension to literal cofactors; no existence is
assumed by the module. -/
structure TerminationInterface
    (D : Nat)
    {T : Type v} {V : Type w}
    (defect : U → U → List (LocalTest U T V) → Int) where
  zero_extraction : ∀ {d f : U} {Ω : List (LocalTest U T V)},
    defect d f Ω ≤ -1 → OriginalCofactors d f

def terminal_extraction
    {D : Nat}
    {T : Type v} {V : Type w}
    {defect : U → U → List (LocalTest U T V) → Int}
    (termination : TerminationInterface D defect)
    (terminal : StrongPh D (D + 1) defect)
    (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U T V)) (hΩ : AdmissibleTestList d Ω) :
    OriginalCofactors d (terminal d hd A Ω hΩ).source := by
  apply termination.zero_extraction
  calc
    defect d (terminal d hd A Ω hΩ).source Ω ≤ defectBound D (D + 1) :=
      (terminal d hd A Ω hΩ).defect_bound
    _ = -1 := defectBound_terminal D

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.strongPh_succ
#print axioms SymplecticStafford.Induction.terminal_extraction
