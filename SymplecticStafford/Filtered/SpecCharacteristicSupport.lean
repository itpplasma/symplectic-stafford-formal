import Mathlib.RingTheory.Support
import SymplecticStafford.Filtered.FiniteSupportQuotient

/-!
# Spectrum support for an actual associated module

`CharacteristicSupport.lean` deliberately exposes a finite support proxy: it
records the nonzero classes in finitely many filtration quotients.  This file
adds the exact M01 boundary that can be stated independently of a Rees
construction.  Once an actual commutative associated graded ring `A` and an
`A`-module `N` have been constructed, their characteristic support is the
Mathlib support `Module.support A N` in `Spec A`.

The `FilteredClassData` structure records one genuine filtered class map.  Its
kernel equation says that the map is the class modulo the next filtration
layer; it is an explicit bridge obligation, not an existence field hidden in
the support definition.  No Rees ring, localization, or universal source
producer is inferred here.
-/

namespace SymplecticStafford.Filtered

universe u v w

section Spectrum

variable {A : Type u} {N : Type v}
variable [CommRing A] [AddCommGroup N] [Module A N]

/- The full spectrum-valued support, as opposed to the finite layer proxy. -/
def SpecCharacteristicSupport (A : Type u) (N : Type v) [CommRing A]
    [AddCommGroup N]
    [Module A N] :
    Set (PrimeSpectrum A) :=
  Module.support A N

theorem mem_specCharacteristicSupport_iff (p : PrimeSpectrum A) :
    p ∈ SpecCharacteristicSupport A N ↔
      Nontrivial (LocalizedModule p.asIdeal.primeCompl N) :=
  Module.mem_support_iff

theorem specCharacteristicSupport_empty_iff_subsingleton :
    SpecCharacteristicSupport A N = ∅ ↔ Subsingleton N := by
  exact Module.support_eq_empty_iff

theorem specCharacteristicSupport_empty_iff_zero :
    SpecCharacteristicSupport A N = ∅ ↔ ∀ x : N, x = 0 := by
  rw [specCharacteristicSupport_empty_iff_subsingleton]
  exact subsingleton_iff_forall_eq 0

theorem specCharacteristicSupport_nonempty_iff_nontrivial :
    (SpecCharacteristicSupport A N).Nonempty ↔ Nontrivial N := by
  exact Module.nonempty_support_iff

variable [Module.Finite A N]

theorem specCharacteristicSupport_eq_zeroLocus_annihilator :
    SpecCharacteristicSupport A N =
      PrimeSpectrum.zeroLocus (Module.annihilator A N : Set A) := by
  exact Module.support_eq_zeroLocus

end Spectrum

section FilteredClass

variable {R : Type u} {M : Type v}
variable [Ring R] [AddCommGroup M] [Module R M]

/-!
An explicit associated-layer class map.  The target `N` is intended to be an
actual module over the commutative associated graded ring.  The map need only
be additive at this boundary; module compatibility belongs to the Rees/
associated-graded construction and is therefore not silently assumed.
-/
structure FilteredClassData (F : FiniteFilteredModule (R := R) (M := M))
    (A : Type w) (N : Type u)
    [CommRing A] [AddCommGroup N] [Module A N] where
  layer : Fin F.height
  classMap : M →+ N
  classMap_zero_iff_mem_next :
    ∀ x : M,
      classMap x = 0 ↔ x ∈ F.carrier (layer.1 + 1)

namespace FilteredClassData

variable {F : FiniteFilteredModule (R := R) (M := M)}
variable {A : Type w} {N : Type u}
variable [CommRing A] [AddCommGroup N] [Module A N]
variable (C : FilteredClassData F A N)

theorem classMap_eq_zero_of_mem_next {x : M}
    (hx : x ∈ F.carrier (C.layer.1 + 1)) : C.classMap x = 0 := by
  exact (C.classMap_zero_iff_mem_next x).mpr hx

theorem classMap_ne_zero_of_not_mem_next {x : M}
    (hx : x ∉ F.carrier (C.layer.1 + 1)) : C.classMap x ≠ 0 := by
  intro hzero
  exact hx ((C.classMap_zero_iff_mem_next x).mp hzero)

theorem specSupport_nonempty_of_filtered_class_ne_zero {x : M}
    (hx : x ∈ F.carrier C.layer.1)
    (hclass : C.classMap x ≠ 0) :
    (SpecCharacteristicSupport A N).Nonempty := by
  have hN : Nontrivial N := by
    exact ⟨⟨C.classMap x, 0, hclass⟩⟩
  exact specCharacteristicSupport_nonempty_iff_nontrivial (A := A) (N := N) |>.mpr hN

theorem specSupport_nonempty_of_not_mem_next {x : M}
    (hx : x ∈ F.carrier C.layer.1)
    (hnext : x ∉ F.carrier (C.layer.1 + 1)) :
    (SpecCharacteristicSupport A N).Nonempty := by
  exact C.specSupport_nonempty_of_filtered_class_ne_zero hx
    (C.classMap_ne_zero_of_not_mem_next hnext)

theorem filtered_class_zero_iff_mem_next {x : M} :
    C.classMap x = 0 ↔ x ∈ F.carrier (C.layer.1 + 1) :=
  C.classMap_zero_iff_mem_next x

/- If the class map is onto, its support is empty exactly when every filtered
   class is zero.  This is the precise zero-detection statement available at
   the bridge; selecting a global class map is a separate construction. -/
theorem specSupport_empty_iff_classMap_eq_zero
    (hsurj : Function.Surjective C.classMap) :
    SpecCharacteristicSupport A N = ∅ ↔ ∀ x : M, C.classMap x = 0 := by
  constructor
  · intro h x
    have hzero : ∀ y : N, y = 0 :=
      (specCharacteristicSupport_empty_iff_zero (A := A) (N := N)).mp h
    exact hzero (C.classMap x)
  · intro h
    apply (specCharacteristicSupport_empty_iff_zero (A := A) (N := N)).mpr
    intro y
    rcases hsurj y with ⟨x, rfl⟩
    exact h x

end FilteredClassData

end FilteredClass

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.mem_specCharacteristicSupport_iff
#print axioms SymplecticStafford.Filtered.specCharacteristicSupport_eq_zeroLocus_annihilator
#print axioms SymplecticStafford.Filtered.FilteredClassData.specSupport_empty_iff_classMap_eq_zero
