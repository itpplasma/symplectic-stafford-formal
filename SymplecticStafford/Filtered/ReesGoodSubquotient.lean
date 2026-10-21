module

public import Mathlib.RingTheory.Noetherian.Basic
public import SymplecticStafford.Filtered.ReesNoetherianCriterion

@[expose] public section

/-!
# Noetherian Rees modules and good subquotients

Once the actual Rees ring is known to be Noetherian, a finite good module and
all of its subquotients are Noetherian.  This file makes that consumer
constructive at the certificate level: finite generators of every submodule
are chosen from the Noetherian module structure, and a two-level degree
(`0` at zero, `1` elsewhere) gives the strict reduction required by
`ReesModuleNoetherianCertificate`.

This is deliberately downstream of Rees-ring Noetherianity.  It does not
derive that ring hypothesis from finite-dimensional associated graded data;
the missing leading-term/symbol-lifting theorem remains explicit upstream.
-/

namespace SymplecticStafford.Filtered

universe u

section

variable {A M : Type u} [Ring A] [AddCommGroup M] [Module A M]

private theorem exists_finset_span_eq
    [IsNoetherian A M] (N : Submodule A M) :
    ∃ s : Finset M, Submodule.span A (s : Set M) = N := by
  rcases Submodule.fg_def.mp (IsNoetherian.noetherian N) with
    ⟨S, hSfinite, hSspan⟩
  let s : Finset M := hSfinite.toFinset
  have hS_eq : (S : Set M) = (s : Set M) := by
    exact (Set.Finite.coe_toFinset hSfinite).symm
  refine ⟨s, ?_⟩
  rw [← hS_eq, hSspan]

noncomputable def chosenSubmoduleGenerators
    [IsNoetherian A M] (N : Submodule A M) : Finset M :=
  Classical.choose (exists_finset_span_eq N)

theorem chosenSubmoduleGenerators_span
    [IsNoetherian A M] (N : Submodule A M) :
    Submodule.span A (chosenSubmoduleGenerators N : Set M) = N :=
  Classical.choose_spec (exists_finset_span_eq N)

noncomputable def twoLevelDegree (x : M) : Nat := by
  classical
  exact if x = 0 then 0 else 1

theorem twoLevelDegree_ne_zero {x : M} (hx : x ≠ 0) :
    twoLevelDegree x = 1 := by
  classical
  simp [twoLevelDegree, hx]

theorem twoLevelDegree_zero : twoLevelDegree (0 : M) = 0 := by
  classical
  simp [twoLevelDegree]

/-- A Noetherian module has an explicit strict-reduction certificate. -/
noncomputable def noetherianModuleCertificate
    [IsNoetherian A M] : ReesModuleNoetherianCertificate A M where
  degree := twoLevelDegree
  generators := chosenSubmoduleGenerators
  generators_mem := by
    intro N x hx
    have hxspan : x ∈ Submodule.span A
        (chosenSubmoduleGenerators N : Set M) :=
      Submodule.subset_span hx
    rw [chosenSubmoduleGenerators_span N] at hxspan
    exact hxspan
  reduce := by
    intro N x hx hne
    refine ⟨0, N.zero_mem, ?_, ?_⟩
    · rw [twoLevelDegree_zero, twoLevelDegree_ne_zero hne]
      decide
    · simpa using (show x ∈ Submodule.span A
        (chosenSubmoduleGenerators N : Set M) from by
          rw [chosenSubmoduleGenerators_span N]
          exact hx)

theorem noetherianModuleCertificate_isNoetherian
    [IsNoetherian A M] :
    IsNoetherian A M :=
  inferInstance

end

section ReesConsumer

variable {A M : Type u} [Ring A] [AddCommGroup M] [Module A M]

/-- A Noetherian ring and a finite good module produce the module certificate,
with no certificate field supplied for the module itself. -/
noncomputable def moduleCertificate_of_noetherianRing
    [IsNoetherianRing A] [Module.Finite A M] :
    ReesModuleNoetherianCertificate A M := by
  letI : IsNoetherian A M := inferInstance
  exact noetherianModuleCertificate

theorem moduleCertificate_of_noetherianRing_isNoetherian
    [IsNoetherianRing A] [Module.Finite A M] :
    IsNoetherian A M := by
  letI : IsNoetherian A M := inferInstance
  exact noetherianModuleCertificate_isNoetherian

theorem noetherian_good_subquotient
    [IsNoetherianRing A] [Module.Finite A M]
    (N : Submodule A M) : IsNoetherian A (M ⧸ N) := by
  letI : IsNoetherian A M := inferInstance
  infer_instance

end ReesConsumer

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.noetherianModuleCertificate
#print axioms SymplecticStafford.Filtered.moduleCertificate_of_noetherianRing
#print axioms SymplecticStafford.Filtered.noetherian_good_subquotient
