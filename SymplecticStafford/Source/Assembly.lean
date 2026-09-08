import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Basic
import SymplecticStafford.Semantics.S1Consequences

/-!
# Original-ring source selection and assembly contracts

The paper needs one source in the original algebra before local calculations
can be recombined.  This module exposes that boundary explicitly.  Its
structures package supplied witnesses; they do not manufacture a source,
prove existence for the admissible class, or identify a completed/localized
element with an element of the original ring.
-/

namespace SymplecticStafford.Source

universe u

variable {R : Type u} [Semiring R]

/-- A finite, original-ring list of possible source elements. -/
structure CandidateFamily (R : Type u) [Semiring R] where
  candidates : Finset R
  candidate_nonzero : ∀ f ∈ candidates, f ≠ 0

/-- A selected source is tracked together with its membership in the finite
candidate family.  The selection theorem is intentionally an input. -/
structure SelectedSource (F : CandidateFamily R) where
  source : R
  source_mem : source ∈ F.candidates

theorem selected_source_nonzero (F : CandidateFamily R)
    (s : SelectedSource F) : s.source ≠ 0 :=
  F.candidate_nonzero s.source s.source_mem

/-- One exact same-divisor witness in the original ring. -/
structure AssemblyWitness (d f : R) where
  right₁ : R
  right₂ : R
  identity : (1 : R) = d * right₁ + (f * d) * right₂

def AssemblyWitness.certificate {d f : R} (w : AssemblyWitness d f) :
    SymplecticStafford.RightCertificate (R := R) d f 1 :=
  ⟨w.right₁, w.right₂, w.identity⟩

/-- A selected source together with the exact original-ring assembly field.

This is a terminal *contract* for a future producer proof.  The field
`assemble` is not an axiom or a theorem: any concrete instance must provide
the displayed coefficients and preserve their noncommutative order.
-/
structure SingleSourceAssembly (F : CandidateFamily R)
    extends SelectedSource F where
  assemble : ∀ ⦃d : R⦄, d ≠ 0 → AssemblyWitness d source

theorem SingleSourceAssembly.assembled_certificate
    {F : CandidateFamily R} (A : SingleSourceAssembly F)
    {d : R} (hd : d ≠ 0) :
    Nonempty (SymplecticStafford.RightCertificate (R := R) d A.source 1) :=
  ⟨A.assemble hd |>.certificate⟩

theorem SingleSourceAssembly.sameDivisor
    {F : CandidateFamily R} (A : SingleSourceAssembly F) :
    SymplecticStafford.SameDivisorS1 (R := R) := by
  intro d hd
  obtain ⟨w⟩ := A.assembled_certificate hd
  exact ⟨A.source, w.right₁, w.right₂, w.identity⟩

/-- A weaker selection input: each nonzero divisor may select a candidate.
It is kept separate from `SingleSourceAssembly`, since a divisor-dependent
choice is not by itself a single global source. -/
structure DivisorSelection (F : CandidateFamily R) where
  select : ∀ ⦃d : R⦄, d ≠ 0 → ∃ f ∈ F.candidates, Nonempty (AssemblyWitness d f)

theorem DivisorSelection.sameDivisor
    {F : CandidateFamily R} (D : DivisorSelection F) :
    SymplecticStafford.SameDivisorS1 (R := R) := by
  intro d hd
  obtain ⟨f, _, ⟨w⟩⟩ := D.select hd
  exact ⟨f, w.right₁, w.right₂, w.identity⟩

end SymplecticStafford.Source

#print axioms SymplecticStafford.Source.selected_source_nonzero
#print axioms SymplecticStafford.Source.SingleSourceAssembly.sameDivisor
