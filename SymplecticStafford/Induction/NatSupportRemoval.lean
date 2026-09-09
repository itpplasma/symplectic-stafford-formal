import SymplecticStafford.Induction.TwoCallDescentProducer

/-!
# A concrete non-vacuous two-call support-removal step

The universal producer is still unavailable, but the abstract two-call
interface can be instantiated non-vacuously at one original-ring datum.  Over
`Nat`, support is the singleton exactly at source zero, so a lower source zero
and a nonzero auxiliary source give strict removal for every scalar outside
the explicit finite exception `{0}`.  The carried-test pencil law is an
explicit hypothesis, as required by the contract.

This is a scoped positive bridge, not a universal `P_h` theorem: the lower
calls and their source facts are quantified inputs, and no successor output
witness is supplied.
-/

namespace SymplecticStafford.Induction

universe v w

def natRemovalDefect : Nat → Nat → List (LocalTest Nat v w) → Int :=
  fun _ f _ => if f = 0 then 0 else -1

def natRemovalSupport {κ : Type v} [DecidableEq κ] (unit : κ)
    (_q f : Nat) (_xs : List (LocalTest Nat v w)) : Finset κ :=
  if f = 0 then {unit} else ∅

def natRemovalParameters : CentralParameters Nat Nat where
  embed := fun z => z
  central := by intros; exact Nat.mul_comm _ _

def nat_two_call_data
    {T : Type v} {V : Type w}
    {κ : Type v} [DecidableEq κ]
    (unit : κ)
    (lower : StrongPh 1 1 (natRemovalDefect (v := T) (w := V)))
    (A : AffineSource Nat)
    (Ω : List (LocalTest Nat T V))
    (hΩ : AdmissibleTestList 1 Ω)
    (hOld : (lower 1 (by decide) A Ω hΩ).source = 0)
    (hNew :
      (lower 1 (by decide) (homogeneousAffine A.a A.a_nonzero) Ω hΩ).source ≠ 0)
    (hgen : ∀ z : Nat, ∀ t : LocalTest Nat T V, t ∈ Ω →
      t.generation (lower 1 (by decide) A Ω hΩ).source →
      t.generation
        (lower 1 (by decide) (homogeneousAffine A.a A.a_nonzero) Ω hΩ).source →
      t.generation
        (pencilMember natRemovalParameters
          (lower 1 (by decide) A Ω hΩ).source
          (lower 1 (by decide) (homogeneousAffine A.a A.a_nonzero) Ω hΩ).source z)) :
    TwoCallDescentData (κ := κ) natRemovalParameters 1 1
      (natRemovalDefect (v := T) (w := V)) lower 1 (by decide) A Ω hΩ := by
  let old := lower 1 (by decide) A Ω hΩ
  let new := lower 1 (by decide) (homogeneousAffine A.a A.a_nonzero) Ω hΩ
  refine {
    L0 := 1
    C0 := 0
    auxiliaryDivisor := 1
    auxiliaryDivisor_eq := by norm_num
    auxiliaryDivisor_nonzero := by decide
    old_relation := by simp [old, hOld]
    newInput := Ω
    newInput_admissible := hΩ
    carried_in_new := listCarried_refl Ω
    support := natRemovalSupport unit
    defect_eq_support := ?_
    exceptional := {0}
    exceptional_finite := Set.toFinite _
    strict_support := ?_
    pencil_generation := ?_ }
  · intro q f xs
    by_cases hf : f = 0 <;>
      simp [natRemovalDefect, natRemovalSupport, finiteSupportDefect, hf]
  · intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hOld' : old.source = 0 := hOld
    have hNew' : new.source ≠ 0 := hNew
    have hout :
        pencilMember natRemovalParameters old.source new.source z ≠ 0 := by
      rw [pencilMember, natRemovalParameters, hOld]
      simp [hNew', hz0]
    change natRemovalSupport unit 1
        (pencilMember natRemovalParameters old.source new.source z) Ω ⊂
      natRemovalSupport unit 1 old.source Ω
    simp [natRemovalSupport, hOld', hNew', hz0, pencilMember,
      natRemovalParameters]
  · intro z t hz ht hF hG
    exact hgen z t ht hF hG

noncomputable def nat_two_call_witness
    {T : Type v} {V : Type w}
    {κ : Type v} [DecidableEq κ]
    (unit : κ)
    (lower : StrongPh 1 1 (natRemovalDefect (v := T) (w := V)))
    (A : AffineSource Nat)
    (Ω : List (LocalTest Nat T V))
    (hΩ : AdmissibleTestList 1 Ω)
    (hOld : (lower 1 (by decide) A Ω hΩ).source = 0)
    (hNew :
      (lower 1 (by decide) (homogeneousAffine A.a A.a_nonzero) Ω hΩ).source ≠ 0)
    (hgen : ∀ z : Nat, ∀ t : LocalTest Nat T V, t ∈ Ω →
      t.generation (lower 1 (by decide) A Ω hΩ).source →
      t.generation
        (lower 1 (by decide) (homogeneousAffine A.a A.a_nonzero) Ω hΩ).source →
      t.generation
        (pencilMember natRemovalParameters
          (lower 1 (by decide) A Ω hΩ).source
          (lower 1 (by decide) (homogeneousAffine A.a A.a_nonzero) Ω hΩ).source z)) :
    StrongPhWitness 1 2 (natRemovalDefect (v := T) (w := V)) 1 A Ω := by
  exact (nat_two_call_data unit lower A Ω hΩ hOld hNew hgen).witness

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.nat_two_call_witness
