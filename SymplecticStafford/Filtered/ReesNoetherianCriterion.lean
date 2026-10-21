module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Ring.Basic

@[expose] public section

/-!
# Noetherianity from a terminating filtered lift

The raw `FiltrationData` API does not imply Noetherianity (see
`NoetherianBoundary.lean`).  The filtered proof needs one additional,
checkable ingredient: for every ideal of the actual algebraic Rees ring,
there must be finitely many lifted generators and every nonzero element must
reduce modulo their span to an element of strictly smaller filtered degree.

`Data` records exactly that reduction certificate.  The proof below performs
the degree descent in the kernel, then derives finite generation of every
ideal and hence `IsNoetherianRing`.  It is an API for the missing M02
construction, not an assumption disguised as a theorem about arbitrary raw
filtrations: a later Rees construction must still supply `Data` from its
associated graded finite-generation argument.

The reduction equation uses the order `x - y` and the left ideal span, so no
commutativity or completion is introduced.  This is deliberately stated at
the actual ring level and can therefore be instantiated with a noncommutative
Rees ring once its leading-term lift has been proved.
-/

namespace SymplecticStafford.Filtered

universe u

structure ReesNoetherianCertificate (A : Type u) [Ring A] where
  degree : A → Nat
  generators : ∀ I : Ideal A, Finset A
  generators_mem : ∀ (I : Ideal A) {x : A},
    x ∈ generators I → x ∈ I
  /-- One strict filtered reduction for every nonzero ideal element. -/
  reduce : ∀ (I : Ideal A) (x : A), x ∈ I → x ≠ 0 →
    ∃ y : A, y ∈ I ∧ degree y < degree x ∧
      x - y ∈ Ideal.span (generators I : Set A)

namespace ReesNoetherianCertificate

variable {A : Type u} [Ring A] (C : ReesNoetherianCertificate A)

private theorem mem_span_of_degree (I : Ideal A) :
    ∀ x : A, x ∈ I → x ∈ Ideal.span (C.generators I : Set A) := by
  intro x hx
  induction h : C.degree x using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hzero : x = 0
      · subst x
        exact Ideal.zero_mem _
      · obtain ⟨y, hyI, hyd, hxy⟩ := C.reduce I x hx hzero
        have hyd' : C.degree y < n := by simpa [h] using hyd
        have hy : y ∈ Ideal.span (C.generators I : Set A) :=
          ih (C.degree y) hyd' y hyI rfl
        have hxy' : x - y ∈ Ideal.span (C.generators I : Set A) := hxy
        have hsum : x = (x - y) + y := by simp
        rw [hsum]
        exact (Ideal.span (C.generators I : Set A)).add_mem hxy' hy

theorem ideal_eq_span_generators (I : Ideal A) :
    I = Ideal.span (C.generators I : Set A) := by
  apply le_antisymm
  · intro x hx
    exact mem_span_of_degree C I x hx
  · exact Ideal.span_le.2 (fun x hx => C.generators_mem I hx)

theorem ideal_fg (C : ReesNoetherianCertificate A) (I : Ideal A) : I.FG := by
  rw [ideal_eq_span_generators C I]
  exact Submodule.fg_span (C.generators I).finite_toSet

theorem isNoetherianRing (C : ReesNoetherianCertificate A) : IsNoetherianRing A := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  exact ideal_fg C I

end ReesNoetherianCertificate

/-! A module-level version is needed for good Rees subquotients.  It has the
same strict reduction interface, but ranges over actual `Submodule`s and
uses additive subtraction in the module. -/

structure ReesModuleNoetherianCertificate (A : Type u) (M : Type u)
    [Ring A] [AddCommGroup M] [Module A M] where
  degree : M → Nat
  generators : ∀ N : Submodule A M, Finset M
  generators_mem : ∀ (N : Submodule A M) {x : M},
    x ∈ generators N → x ∈ N
  /-- One strict filtered reduction for every nonzero submodule element. -/
  reduce : ∀ (N : Submodule A M) (x : M), x ∈ N → x ≠ 0 →
    ∃ y : M, y ∈ N ∧ degree y < degree x ∧
      x - y ∈ Submodule.span A (generators N : Set M)

namespace ReesModuleNoetherianCertificate

variable {A M : Type u} [Ring A] [AddCommGroup M] [Module A M]
  (C : ReesModuleNoetherianCertificate A M)

private theorem mem_span_of_degree (N : Submodule A M) :
    ∀ x : M, x ∈ N → x ∈ Submodule.span A (C.generators N : Set M) := by
  intro x hx
  induction h : C.degree x using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hzero : x = 0
      · subst x
        exact Submodule.zero_mem _
      · obtain ⟨y, hyN, hyd, hxy⟩ := C.reduce N x hx hzero
        have hyd' : C.degree y < n := by simpa [h] using hyd
        have hy : y ∈ Submodule.span A (C.generators N : Set M) :=
          ih (C.degree y) hyd' y hyN rfl
        have hxy' : x - y ∈ Submodule.span A (C.generators N : Set M) := hxy
        have hsum : x = (x - y) + y := by abel
        rw [hsum]
        exact (Submodule.span A (C.generators N : Set M)).add_mem hxy' hy

theorem submodule_eq_span_generators (N : Submodule A M) :
    N = Submodule.span A (C.generators N : Set M) := by
  apply le_antisymm
  · intro x hx
    exact mem_span_of_degree C N x hx
  · exact Submodule.span_le.2 (fun x hx => C.generators_mem N hx)

theorem submodule_fg (C : ReesModuleNoetherianCertificate A M)
    (N : Submodule A M) : N.FG := by
  rw [submodule_eq_span_generators C N]
  exact Submodule.fg_span (C.generators N).finite_toSet

/-- A strict finite-generator reduction certificate proves Noetherianity of
the actual module, including every good submodule as a finite module. -/
theorem isNoetherianModule (C : ReesModuleNoetherianCertificate A M) :
    IsNoetherian A M := by
  exact ⟨fun N => submodule_fg C N⟩

end ReesModuleNoetherianCertificate

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.ReesNoetherianCertificate.ideal_eq_span_generators
#print axioms SymplecticStafford.Filtered.ReesNoetherianCertificate.ideal_fg
#print axioms SymplecticStafford.Filtered.ReesNoetherianCertificate.isNoetherianRing
#print axioms SymplecticStafford.Filtered.ReesModuleNoetherianCertificate.submodule_eq_span_generators
#print axioms SymplecticStafford.Filtered.ReesModuleNoetherianCertificate.submodule_fg
#print axioms SymplecticStafford.Filtered.ReesModuleNoetherianCertificate.isNoetherianModule
