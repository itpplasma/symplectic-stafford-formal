import SymplecticStafford.Induction.ConstructiveSuccessor

/-!
# Constructive source and test output for a two-call successor

The older successor records accept `output_source_affine` and `output` as
fields.  This file removes those two supplied witness fields from the core
construction.  Given the actual lower-call witnesses, the affine source
equation is derived by distributivity, and the new witness is assembled from
the old/new sources, an explicit central parameter, a genuine defect bound,
and the actual carried-test implication.

The support-removal and test-generation facts remain mathematical inputs: this
theorem does not claim to construct them from filtered geometry.  It does,
however, keep the two lower calls and the original `U` source formula in the
proof term rather than accepting a pre-built successor witness.
-/

namespace SymplecticStafford.Induction

universe u v w x

variable {U : Type u} [Semiring U]

section Affine

variable {Λ : Type x}

/-- Two lower source members remain in the original affine source space after
the ordered central pencil operation. -/
theorem affine_member_pencil_of_members
    (P : CentralParameters U Λ) (A : AffineSource U)
    {F G : U} {scalar : Λ}
    (hF : A.member F)
    (hG : (homogeneousAffine A.a A.a_nonzero).member G) :
    A.member (pencilMember P F G scalar) := by
  rcases hF with ⟨H₁, hF⟩
  rcases hG with ⟨H₂, hG⟩
  refine ⟨H₁ + P.embed scalar * H₂, ?_⟩
  rw [pencilMember, hF, hG]
  simp only [homogeneousAffine, zero_add]
  simp only [add_mul, mul_assoc]
  ac_rfl

end Affine

section Successor

variable {Λ : Type x} (P : CentralParameters U Λ) (κ : Type v)

/-- Construct the next strong witness directly from the two lower witnesses.
The output source and affine coefficient are fixed by the pencil; only the
support-removal bound and the carried-test generation implication are
consumed as inputs. -/
noncomputable def strongPhWitness_of_two_lower_calls
    {D h : Nat}
    {defect : U → U → List (LocalTest U v w) → Int}
    {lower : StrongPh D h defect}
    {d : U} (hd : d ≠ 0) {A : AffineSource U}
    {Ω : List (LocalTest U v w)}
    (hΩ : AdmissibleTestList d Ω)
    {d₁ : U} (hd₁ : d₁ ≠ 0)
    {Ω₁ : List (LocalTest U v w)}
    (hΩ₁ : AdmissibleTestList d₁ Ω₁)
    (hcarry : ListCarried Ω Ω₁)
    (scalar : Λ)
    (hbound :
      defect d
        (pencilMember P (lower d hd A Ω hΩ).source
          (lower d₁ hd₁ (homogeneousAffine A.a A.a_nonzero) Ω₁ hΩ₁).source scalar)
        Ω ≤ defectBound D (h + 1))
    (hgen : ∀ t, t ∈ Ω →
      t.generation (lower d hd A Ω hΩ).source →
      t.generation
        (lower d₁ hd₁ (homogeneousAffine A.a A.a_nonzero) Ω₁ hΩ₁).source →
      t.generation
        (pencilMember P (lower d hd A Ω hΩ).source
          (lower d₁ hd₁ (homogeneousAffine A.a A.a_nonzero) Ω₁ hΩ₁).source scalar)) :
    StrongPhWitness (D := D) (h := h + 1) defect d A Ω := by
  let old := lower d hd A Ω hΩ
  let new := lower d₁ hd₁ (homogeneousAffine A.a A.a_nonzero) Ω₁ hΩ₁
  have hnew_mem :
      (homogeneousAffine A.a A.a_nonzero).member new.source :=
    new.affine_member
  have hout_mem : A.member (pencilMember P old.source new.source scalar) :=
    affine_member_pencil_of_members P A old.affine_member hnew_mem
  let Hout : U := Classical.choose hout_mem
  have hsource :
      pencilMember P old.source new.source scalar = A.B + Hout * A.a :=
    Classical.choose_spec hout_mem
  refine {
    H := Hout
    source := pencilMember P old.source new.source scalar
    source_eq := hsource
    defect_bound := by simpa [old, new] using hbound
    tests_pass := ?_ }
  intro t ht
  apply hgen t ht
  · exact old.tests_pass t ht
  · exact new.tests_pass t (hcarry ht)

end Successor

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.affine_member_pencil_of_members
#print axioms SymplecticStafford.Induction.strongPhWitness_of_two_lower_calls
