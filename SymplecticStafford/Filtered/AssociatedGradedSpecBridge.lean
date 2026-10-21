module

public import Mathlib.RingTheory.Support
public import SymplecticStafford.Filtered.M01StructuralClass

@[expose] public section

/-!
# Actual associated-graded/spec support bridge

`M01FilteredAlgebra` supplies actual additive filtered layers, but does not
pretend that those layers are already the spectrum of a commutative graded
ring.  This file isolates the next bridge: an actual commutative ring `A`, an
actual `A`-module `N`, and an explicit additive map from one quotient layer to
`N`.  Surjectivity and the exact quotient kernel are hypotheses of the bridge,
not proposition-valued labels.

The support is the Mathlib `Module.support A N`, and its zero-locus description
uses the actual annihilator.  The bridge therefore exposes the ring/module
operations through the `CommRing A`, `AddCommGroup N`, and `Module A N`
interfaces while keeping the filtered representative and predecessor data
literal.  No associated-graded construction, Noetherianity, or localization
is inferred from the bridge.
-/

namespace SymplecticStafford.Filtered

universe u v w

open SymplecticStafford

section

variable {R : Type u} [Ring R]
variable (F : AdditiveFilteredRingData R)

section Data

variable (A : Type v) (N : Type w)
variable [CommRing A] [AddCommGroup N] [Module A N]

/-- A concrete map from an actual consecutive filtered quotient to an actual
    commutative-ring module.  The kernel field is stated at the quotient
    level, while `layerMap_eq_zero_iff_mem_predecessor` below unfolds it back
    to original filtered representatives. -/
structure AssociatedGradedSpecBridge
    (F : AdditiveFilteredRingData R) (A : Type v) (N : Type w)
    [CommRing A] [AddCommGroup N] [Module A N] where
  layer : ℕ
  layerMap : AdditiveFilteredRingData.associatedLayer F layer →+ N
  surjective : Function.Surjective layerMap
  layerMap_eq_zero_iff : ∀ q, layerMap q = 0 ↔ q = 0

namespace AssociatedGradedSpecBridge

variable (C : AssociatedGradedSpecBridge F A N)

theorem layerMap_eq_zero_of_mem_predecessor
    (x : F.carrier C.layer)
    (hx : (x : R) ∈ AdditiveFilteredRingData.predecessor F C.layer) :
    C.layerMap (AdditiveFilteredRingData.associatedClass F C.layer
      (x : R) x.property) = 0 := by
  apply (C.layerMap_eq_zero_iff _).mpr
  apply (Submodule.Quotient.eq
    (AdditiveFilteredRingData.layerSubmodule F C.layer)).mpr
  change (x : R) - 0 ∈ AdditiveFilteredRingData.predecessor F C.layer
  simpa using hx

theorem layerMap_mk_eq_zero_iff_mem_predecessor
    (x : F.carrier C.layer) :
    C.layerMap (AdditiveFilteredRingData.associatedClass F C.layer
      (x : R) x.property) = 0 ↔
      (x : R) ∈ AdditiveFilteredRingData.predecessor F C.layer := by
  constructor
  · intro h
    apply (AdditiveFilteredRingData.associatedClass_eq_zero_iff
      F C.layer (x : R) x.property).mp
    exact (C.layerMap_eq_zero_iff _).mp h
  · intro h
    apply (C.layerMap_eq_zero_iff _).mpr
    exact (AdditiveFilteredRingData.associatedClass_eq_zero_iff
      F C.layer (x : R) x.property).mpr h

theorem specSupport_empty_iff_layer_killed :
    Module.support A N = ∅ ↔
      ∀ x : F.carrier C.layer,
        (x : R) ∈ AdditiveFilteredRingData.predecessor F C.layer := by
  rw [show Module.support A N = ∅ ↔ Subsingleton N by
    exact Module.support_eq_empty_iff]
  constructor
  · intro h x
    have hzero : C.layerMap (AdditiveFilteredRingData.associatedClass F
        C.layer (x : R) x.property) = 0 := by
      exact (Subsingleton.elim _ _)
    exact (layerMap_mk_eq_zero_iff_mem_predecessor F A N C x).mp hzero
  · intro h
    constructor
    intro y z
    obtain ⟨qy, rfl⟩ := C.surjective y
    obtain ⟨qz, rfl⟩ := C.surjective z
    have hy : C.layerMap qy = 0 := by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep qy
      exact (layerMap_mk_eq_zero_iff_mem_predecessor F A N C x).mpr (h x)
    have hz : C.layerMap qz = 0 := by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep qz
      exact (layerMap_mk_eq_zero_iff_mem_predecessor F A N C x).mpr (h x)
    rw [(C.layerMap_eq_zero_iff _).mp hy,
      (C.layerMap_eq_zero_iff _).mp hz]

theorem specSupport_nonempty_iff_exists_not_mem_predecessor :
    (Module.support A N).Nonempty ↔
      ∃ x : F.carrier C.layer,
        (x : R) ∉ AdditiveFilteredRingData.predecessor F C.layer := by
  constructor
  · intro hs
    by_contra h
    have hall : ∀ x : F.carrier C.layer,
        (x : R) ∈ AdditiveFilteredRingData.predecessor F C.layer := by
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    have hsub : Subsingleton N := by
      constructor
      intro y z
      obtain ⟨qy, rfl⟩ := C.surjective y
      obtain ⟨qz, rfl⟩ := C.surjective z
      obtain ⟨x, rfl⟩ := Quotient.exists_rep qy
      have hy : C.layerMap (Submodule.Quotient.mk x) = 0 := by
        exact (layerMap_mk_eq_zero_iff_mem_predecessor F A N C x).mpr (hall x)
      obtain ⟨x', rfl⟩ := Quotient.exists_rep qz
      have hz : C.layerMap (Submodule.Quotient.mk x') = 0 := by
        exact (layerMap_mk_eq_zero_iff_mem_predecessor F A N C x').mpr
          (hall x')
      exact congrArg C.layerMap
        ((C.layerMap_eq_zero_iff _).mp hy |>.trans
          ((C.layerMap_eq_zero_iff _).mp hz).symm)
    have hempty : Module.support A N = ∅ :=
      Module.support_eq_empty_iff.mpr hsub
    exact (Set.not_nonempty_iff_eq_empty.mpr hempty) hs
  · rintro ⟨x, hx⟩
    by_contra hempty
    apply hx
    exact (specSupport_empty_iff_layer_killed F A N C).mp
      (Set.not_nonempty_iff_eq_empty.mp hempty) x

end AssociatedGradedSpecBridge

end Data

section ZeroLocus

variable {A : Type v} {N : Type w}
variable [CommRing A] [AddCommGroup N] [Module A N]
variable [Module.Finite A N]

theorem specSupport_eq_zeroLocus_annihilator :
    Module.support A N =
      PrimeSpectrum.zeroLocus (Module.annihilator A N : Set A) :=
  Module.support_eq_zeroLocus

theorem specSupport_eq_zeroLocus_annihilator_iff_empty :
    Module.support A N = ∅ ↔
      PrimeSpectrum.zeroLocus (Module.annihilator A N : Set A) = ∅ := by
  rw [specSupport_eq_zeroLocus_annihilator]

end ZeroLocus

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.AssociatedGradedSpecBridge.specSupport_empty_iff_layer_killed
#print axioms SymplecticStafford.Filtered.specSupport_eq_zeroLocus_annihilator
