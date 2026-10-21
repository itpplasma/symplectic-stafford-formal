module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.Noetherian.Basic
public import SymplecticStafford.Filtered.ReesNoetherianCriterion

@[expose] public section

/-!
# A concrete Noetherian Rees chart

Mathlib's `reesAlgebra I` is an actual subalgebra of `R[X]`; unlike the raw
filtered polynomial predicate, it is defined by powers of an ideal and has a
finite-type theorem.  This file consumes that theorem and turns its resulting
Noetherian ring instance into the project's strict reduction certificate.

The certificate conversion is explicit (finite generators are chosen for
each ideal and the two-level degree terminates).  Thus the chart is a real
consumer of a Noetherian Rees theorem, not a proposition-valued associated-
graded label.  It still does not identify the custom `ReesRing F` with this
chart or prove a leading-symbol lift for an arbitrary filtered algebra.
-/

namespace SymplecticStafford.Filtered

universe u

section Certificate

variable {A : Type u} [Ring A]

private theorem exists_finset_ideal_span_eq
    [IsNoetherianRing A] (I : Ideal A) :
    ∃ s : Finset A, Ideal.span (s : Set A) = I := by
  rcases Submodule.fg_def.mp (IsNoetherian.noetherian I) with
    ⟨S, hSfinite, hSspan⟩
  let s : Finset A := hSfinite.toFinset
  have hS_eq : (S : Set A) = (s : Set A) := by
    exact (Set.Finite.coe_toFinset hSfinite).symm
  refine ⟨s, ?_⟩
  change Submodule.span A (s : Set A) = I
  rw [← hS_eq, hSspan]

noncomputable def chosenIdealGenerators
    [IsNoetherianRing A] (I : Ideal A) : Finset A :=
  Classical.choose (exists_finset_ideal_span_eq I)

theorem chosenIdealGenerators_span
    [IsNoetherianRing A] (I : Ideal A) :
    Ideal.span (chosenIdealGenerators I : Set A) = I :=
  Classical.choose_spec (exists_finset_ideal_span_eq I)

noncomputable def idealTwoLevelDegree (x : A) : Nat := by
  classical
  exact if x = 0 then 0 else 1

/-- Any Noetherian ring has the strict reduction interface used by M02. -/
noncomputable def noetherianRingCertificate
    [IsNoetherianRing A] : ReesNoetherianCertificate A where
  degree := idealTwoLevelDegree
  generators := chosenIdealGenerators
  generators_mem := by
    intro I x hx
    have hxspan : x ∈ Ideal.span (chosenIdealGenerators I : Set A) :=
      Ideal.subset_span hx
    rw [chosenIdealGenerators_span I] at hxspan
    exact hxspan
  reduce := by
    intro I x hx hne
    refine ⟨0, Ideal.zero_mem I, ?_, ?_⟩
    · simp [idealTwoLevelDegree, hne]
    · have hxspan : x ∈ Ideal.span (chosenIdealGenerators I : Set A) := by
        rw [chosenIdealGenerators_span I]
        exact hx
      simpa using hxspan

theorem noetherianRingCertificate_isNoetherian
    [IsNoetherianRing A] :
    IsNoetherianRing A :=
  ReesNoetherianCertificate.isNoetherianRing noetherianRingCertificate

end Certificate

section ReesChart

variable {R : Type u} [CommRing R]

/-- The genuine Mathlib Rees algebra of an ideal carries the project's
    reduction certificate, with Noetherianity supplied by its finite-type
    construction over a Noetherian base. -/
noncomputable def reesAlgebraNoetherianCertificate
    [IsNoetherianRing R] (I : Ideal R) :
    ReesNoetherianCertificate (reesAlgebra I) :=
  noetherianRingCertificate

theorem reesAlgebraNoetherianCertificate_isNoetherian
    [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (reesAlgebra I) :=
  ReesNoetherianCertificate.isNoetherianRing
    (reesAlgebraNoetherianCertificate I)

end ReesChart

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.noetherianRingCertificate
#print axioms SymplecticStafford.Filtered.reesAlgebraNoetherianCertificate
#print axioms SymplecticStafford.Filtered.reesAlgebraNoetherianCertificate_isNoetherian
