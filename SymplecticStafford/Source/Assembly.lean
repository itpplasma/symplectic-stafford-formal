module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Finset.Basic
public import SymplecticStafford.Semantics.S1Consequences

@[expose] public section

/-!
# Original-ring source selection and assembly contract scaffolds

The paper needs one source in the original algebra before local calculations
can be recombined.  This module exposes that boundary explicitly.  Its
structures package supplied witnesses; they do not manufacture a source,
prove existence for the admissible class, or identify a completed/localized
element with an element of the original ring.  The finite-candidate structures
below are deliberately toy scaffolds: the paper's source is allowed to depend
on the divisor and is not obtained from a fixed finite family.
-/

namespace SymplecticStafford.Source

universe u

variable {R : Type u} [Semiring R]

/-- A finite, original-ring list of possible source elements.

This is a small test harness, not the paper's finite-test selection theorem.
-/
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

/-- In a division ring the original-ring cofactors are explicit.  This is a
concrete assembly consumer for finite source tests, not a source producer:
the source `f` is arbitrary and both cofactors are elements of the same ring.
-/
def AssemblyWitness.of_divisionRing
    {R : Type u} [DivisionRing R] {d f : R} (hd : d ≠ 0) :
    AssemblyWitness d f := by
  refine ⟨d⁻¹, 0, ?_⟩
  simp [hd]

def AssemblyWitness.certificate {d f : R} (w : AssemblyWitness d f) :
    SymplecticStafford.RightCertificate (R := R) d f 1 :=
  ⟨w.right₁, w.right₂, w.identity⟩

/-- A stronger optional contract with one source shared by every divisor.

The all-dimensional paper does not require this uniform-in-`d` source, so this
structure must not be counted as the paper's producer theorem.

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

/- A paper-shaped conditional interface: the source may depend on the
   divisor, while every returned cofactor remains in the original ring. -/
structure DivisorIndexedAssembly (R : Type u) [Semiring R] where
  source : ∀ ⦃d : R⦄, d ≠ 0 → R
  assemble : ∀ ⦃d : R⦄ (hd : d ≠ 0),
    AssemblyWitness d (source hd)

theorem DivisorIndexedAssembly.sameDivisor
    (A : DivisorIndexedAssembly R) :
    SymplecticStafford.SameDivisorS1 (R := R) := by
  intro d hd
  obtain ⟨w⟩ := Nonempty.intro (A.assemble hd)
  exact ⟨A.source hd, w.right₁, w.right₂, w.identity⟩

/-- A weaker finite-candidate selection input: each nonzero divisor may select
one candidate.  It is kept separate from `SingleSourceAssembly`, since a
divisor-dependent choice is not by itself a single global source.  This is
still only a supplied witness contract, not the paper's producer. -/
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
#print axioms SymplecticStafford.Source.AssemblyWitness.of_divisionRing
#print axioms SymplecticStafford.Source.SingleSourceAssembly.sameDivisor
#print axioms SymplecticStafford.Source.DivisorIndexedAssembly.sameDivisor
