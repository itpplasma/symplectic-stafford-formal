module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.WithBot
public import SymplecticStafford.Filtered.FiniteSupportQuotient
public import SymplecticStafford.Semantics.SupportDimension

@[expose] public section

/-!
# Characteristic support of a finite filtered module

For a finite separated filtration, the characteristic-support proxy used in
this checkpoint is the set of layers whose actual module quotient has a
nonzero class.  Thus support is constructed from quotient maps, rather than
being supplied together with a zero-detection conclusion.  The associated
`WithBot Nat` dimension is the cardinality of this finite support, with
bottom reserved for the empty support.

This is a finite associated-graded support abstraction.  It does not claim
that these layers are the homogeneous spectrum of a Rees algebra, nor does it
construct localization or a full characteristic variety.
-/

namespace SymplecticStafford.Filtered

universe u v

section

variable {R : Type u} {M : Type v}
variable [Ring R] [AddCommGroup M] [Module R M]

namespace FiniteFilteredModule

variable (F : FiniteFilteredModule (R := R) (M := M))

/- A layer is indexed by `Fin F.height`, so the next layer is always an
   available filtration layer. -/
def QuotientSupport : Set (Fin F.height) :=
  {k | ∃ x : M, x ∈ F.carrier k.1 ∧
    Submodule.mkQ (F.carrier (k.1 + 1)) x ≠ 0}

/- Public M01 terminology: this finite associated-layer support is the
   characteristic-support proxy available before Rees-spectrum machinery is
   constructed. -/
abbrev CharacteristicSupport : Set (Fin F.height) := F.QuotientSupport

theorem mem_quotientSupport_iff (k : Fin F.height) :
    k ∈ F.QuotientSupport ↔
      ∃ x : M, x ∈ F.carrier k.1 ∧
        Submodule.mkQ (F.carrier (k.1 + 1)) x ≠ 0 :=
  Iff.rfl

theorem quotientSupport_nonempty_of_exists_ne_zero
    (hM : ∃ x : M, x ≠ 0) : F.QuotientSupport.Nonempty := by
  rcases hM with ⟨x, hx⟩
  rcases F.exists_associatedTopQuotient_nonzero hx with
    ⟨k, hk, hxk, hq⟩
  refine ⟨⟨k, hk⟩, ?_⟩
  exact ⟨x, hxk, hq⟩

theorem exists_ne_zero_of_quotientSupport_nonempty
    (hS : F.QuotientSupport.Nonempty) : ∃ x : M, x ≠ 0 := by
  rcases hS with ⟨k, hk⟩
  rcases hk with ⟨x, _, hqx⟩
  refine ⟨x, ?_⟩
  intro hx
  apply hqx
  subst x
  simp

theorem quotientSupport_nonempty_iff_exists_ne_zero :
    F.QuotientSupport.Nonempty ↔ ∃ x : M, x ≠ 0 := by
  constructor
  · exact F.exists_ne_zero_of_quotientSupport_nonempty
  · exact F.quotientSupport_nonempty_of_exists_ne_zero

theorem quotientSupport_empty_iff_zero :
    F.QuotientSupport = ∅ ↔ ∀ x : M, x = 0 := by
  constructor
  · intro h x
    by_contra hx
    rcases F.quotientSupport_nonempty_of_exists_ne_zero ⟨x, hx⟩ with
      ⟨k, hk⟩
    have hk' : k ∈ (∅ : Set (Fin F.height)) := h ▸ hk
    simp at hk'
  · intro h
    ext k
    constructor
    · intro hk
      rcases hk with ⟨x, _, hqx⟩
      apply hqx
      simp [h x]
    · intro hk
      exact False.elim hk

/- The support is finite because its ambient index type is finite.  Keeping
   this as a theorem makes the cardinality construction explicit. -/
theorem finite_quotientSupport : F.QuotientSupport.Finite := by
  exact Set.toFinite _

noncomputable def QuotientSupportCard
    (F : FiniteFilteredModule (R := R) (M := M)) : Nat := by
  letI := F.finite_quotientSupport.fintype
  exact Fintype.card {k : Fin F.height // k ∈ F.QuotientSupport}

noncomputable def QuotientSupportDimension
    (F : FiniteFilteredModule (R := R) (M := M)) : SupportDimension := by
  classical
  exact if hS : F.QuotientSupport.Nonempty then
    (F.QuotientSupportCard : SupportDimension)
  else
    ⊥

noncomputable abbrev CharacteristicSupportDimension
    (F : FiniteFilteredModule (R := R) (M := M)) : SupportDimension :=
  F.QuotientSupportDimension

theorem quotientSupportDimension_eq_card (hS : F.QuotientSupport.Nonempty) :
    F.QuotientSupportDimension =
      (F.QuotientSupportCard : SupportDimension) := by
  simp [QuotientSupportDimension, hS]

theorem quotientSupportDimension_eq_bot_iff_support_empty :
    F.QuotientSupportDimension = (⊥ : SupportDimension) ↔
      F.QuotientSupport = ∅ := by
  constructor
  · intro hD
    by_contra hS
    have hSne : F.QuotientSupport.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
    rw [F.quotientSupportDimension_eq_card hSne] at hD
    exact (WithBot.coe_ne_bot :
      (↑F.QuotientSupportCard : SupportDimension) ≠ ⊥) hD
  · intro hS
    simp [QuotientSupportDimension, hS]

theorem quotientSupportDimension_bot_iff_zero :
    F.QuotientSupportDimension = (⊥ : SupportDimension) ↔
      ∀ x : M, x = 0 := by
  rw [F.quotientSupportDimension_eq_bot_iff_support_empty,
    F.quotientSupport_empty_iff_zero]

theorem quotientSupportDimension_ne_bot_iff_support_nonempty :
    F.QuotientSupportDimension ≠ (⊥ : SupportDimension) ↔
      F.QuotientSupport.Nonempty := by
  constructor
  · intro hD
    by_contra hN
    apply hD
    exact (F.quotientSupportDimension_eq_bot_iff_support_empty).mpr
      (Set.not_nonempty_iff_eq_empty.mp hN)
  · intro hS hD
    exact (Set.not_nonempty_iff_eq_empty.mpr
      ((F.quotientSupportDimension_eq_bot_iff_support_empty).mp hD)) hS

theorem exists_nonzero_quotient_of_quotientSupportDimension_ne_bot
    (hD : F.QuotientSupportDimension ≠ (⊥ : SupportDimension)) :
    ∃ k : Fin F.height, ∃ x : M, x ∈ F.carrier k.1 ∧
      Submodule.mkQ (F.carrier (k.1 + 1)) x ≠ 0 := by
  rcases F.quotientSupportDimension_ne_bot_iff_support_nonempty.mp hD with
    ⟨k, hk⟩
  exact ⟨k, hk⟩

theorem quotientSupportDimension_ne_bot_iff_exists_ne_zero :
    F.QuotientSupportDimension ≠ (⊥ : SupportDimension) ↔
      ∃ x : M, x ≠ 0 := by
  constructor
  · intro hD
    by_contra hM
    apply hD
    apply F.quotientSupportDimension_bot_iff_zero.mpr
    intro x
    by_contra hx
    exact hM ⟨x, hx⟩
  · intro hM hD
    rcases hM with ⟨x, hx⟩
    exact hx ((F.quotientSupportDimension_bot_iff_zero.mp hD) x)

theorem quotientSupportDimension_ne_bot_of_quotient_nonzero
    {x : M} (hx : x ≠ 0) :
    F.QuotientSupportDimension ≠ (⊥ : SupportDimension) :=
  F.quotientSupportDimension_ne_bot_iff_exists_ne_zero.mpr ⟨x, hx⟩

/-- The concrete filtered-module support datum consumed by the generic
support boundary.  Both its support and its dimension are the definitions
above; no zero-detection statement is supplied as a field. -/
noncomputable def quotientSupportBoundary :
    SupportDimensionBoundary M (Fin F.height) where
  support := F.QuotientSupport
  dimension := F.QuotientSupportDimension
  dimension_bot_iff_support_empty :=
    F.quotientSupportDimension_eq_bot_iff_support_empty
  support_empty_iff_zero := F.quotientSupport_empty_iff_zero

theorem zero_of_quotientSupportDimension_bot
    (hD : F.QuotientSupportDimension = (⊥ : SupportDimension)) :
    ∀ x : M, x = 0 :=
  F.quotientSupportDimension_bot_iff_zero.mp hD

end FiniteFilteredModule

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.quotientSupport_nonempty_iff_exists_ne_zero
#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.quotientSupportDimension_bot_iff_zero
#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.zero_of_quotientSupportDimension_bot
