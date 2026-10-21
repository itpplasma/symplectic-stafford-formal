module

public import SymplecticStafford.Filtered.SpecCharacteristicSupport
public import SymplecticStafford.Filtered.OriginalCentralSupport

@[expose] public section

/-!
# An actual filtered-class map and its support boundary

`SpecCharacteristicSupport` is the genuine `Module.support` once a
commutative associated module has been supplied.  The older
`FilteredClassData` API maps the whole filtered module and therefore does not
identify the class with an actual layer quotient.  This file records the
smaller, kernel-checked bridge that is needed for that identification.

The target ring/module, the quotient-to-module map, its surjectivity, and its
kernel are all explicit inputs.  In particular, this file does not construct
`gr U`, a Rees localization, a Krull dimension, or any source producer.
-/

namespace SymplecticStafford.Filtered

universe u v w z

variable {R : Type u} {M : Type v}
variable [Ring R] [AddCommGroup M] [Module R M]

section Layer

/-- The next filtration layer, viewed as a submodule of the selected layer. -/
def filteredLayerSubmodule
    (F : FiniteFilteredModule (R := R) (M := M)) (k : Fin F.height) :
    Submodule R (F.carrier k.1) :=
  (F.carrier (k.1 + 1)).comap (F.carrier k.1).subtype

/-- The actual additive quotient represented by a selected filtered layer. -/
abbrev filteredLayerQuotient
    (F : FiniteFilteredModule (R := R) (M := M)) (k : Fin F.height) :=
  F.carrier k.1 ⧸ filteredLayerSubmodule F k

theorem filteredLayerQuotient_mk_eq_zero_iff_mem
    (F : FiniteFilteredModule (R := R) (M := M)) (k : Fin F.height)
    (x : F.carrier k.1) :
    (Submodule.mkQ (filteredLayerSubmodule F k) x = 0) ↔
      (x : M) ∈ F.carrier (k.1 + 1) := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- A class map whose source is the actual filtered quotient, with its kernel
    checked at the quotient level.  The target is intended to be a module over
    a commutative associated graded ring. -/
structure ActualFilteredClassMap
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Type w) (N : Type z)
    [CommRing A] [AddCommGroup N] [Module A N] where
  layer : Fin F.height
  classMap : filteredLayerQuotient F layer →+ N
  surjective : Function.Surjective classMap
  classMap_eq_zero_iff : ∀ q, classMap q = 0 ↔ q = 0

namespace ActualFilteredClassMap

variable {F : FiniteFilteredModule (R := R) (M := M)}
variable {A : Type w} {N : Type z}
variable [CommRing A] [AddCommGroup N] [Module A N]
variable (C : ActualFilteredClassMap F A N)

theorem classMap_eq_zero_of_mem_next
    (x : F.carrier C.layer.1)
    (hx : (x : M) ∈ F.carrier (C.layer.1 + 1)) :
    C.classMap (Submodule.mkQ (filteredLayerSubmodule F C.layer) x) = 0 := by
  apply (C.classMap_eq_zero_iff _).mpr
  exact (filteredLayerQuotient_mk_eq_zero_iff_mem F C.layer x).mpr hx

theorem classMap_mk_eq_zero_iff_mem_next
    (x : F.carrier C.layer.1) :
    C.classMap (Submodule.mkQ (filteredLayerSubmodule F C.layer) x) = 0 ↔
      (x : M) ∈ F.carrier (C.layer.1 + 1) := by
  rw [C.classMap_eq_zero_iff,
    filteredLayerQuotient_mk_eq_zero_iff_mem]

theorem layerQuotient_subsingleton_iff_all_mem_next :
    Subsingleton (filteredLayerQuotient F C.layer) ↔
      ∀ x : F.carrier C.layer.1,
        (x : M) ∈ F.carrier (C.layer.1 + 1) := by
  constructor
  · intro h x
    have hq : Submodule.mkQ (filteredLayerSubmodule F C.layer) x = 0 := by
      exact Subsingleton.elim _ _
    exact (filteredLayerQuotient_mk_eq_zero_iff_mem F C.layer x).mp hq
  · intro h
    constructor
    intro q₁ q₂
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q₁
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q₂
    have hx : Submodule.mkQ (filteredLayerSubmodule F C.layer) x = 0 :=
      (filteredLayerQuotient_mk_eq_zero_iff_mem F C.layer x).mpr (h x)
    have hy : Submodule.mkQ (filteredLayerSubmodule F C.layer) y = 0 :=
      (filteredLayerQuotient_mk_eq_zero_iff_mem F C.layer y).mpr (h y)
    exact hx.trans hy.symm

/- The support is empty exactly when every actual filtered class is killed. -/
theorem specSupport_empty_iff_layer_killed :
    SpecCharacteristicSupport A N = ∅ ↔
      ∀ x : F.carrier C.layer.1,
        (x : M) ∈ F.carrier (C.layer.1 + 1) := by
  rw [show SpecCharacteristicSupport A N = ∅ ↔
      Subsingleton (filteredLayerQuotient F C.layer) by
    constructor
    · intro hs
      have hN : Subsingleton N :=
        (specCharacteristicSupport_empty_iff_subsingleton (A := A) (N := N)).mp hs
      constructor
      intro q₁ q₂
      have hmap : C.classMap q₁ = C.classMap q₂ := Subsingleton.elim _ _
      have hzero : C.classMap (q₁ - q₂) = 0 := by
        rw [map_sub, hmap, sub_self]
      have hq : q₁ - q₂ = 0 := (C.classMap_eq_zero_iff _).mp hzero
      exact sub_eq_zero.mp hq
    · intro hq
      apply (specCharacteristicSupport_empty_iff_zero (A := A) (N := N)).mpr
      intro y
      obtain ⟨q, rfl⟩ := C.surjective y
      have hq0 : q = 0 := Subsingleton.elim _ _
      rw [hq0, map_zero]
  ]
  exact C.layerQuotient_subsingleton_iff_all_mem_next

theorem specSupport_nonempty_of_not_mem_next
    (x : F.carrier C.layer.1)
    (hx : (x : M) ∉ F.carrier (C.layer.1 + 1)) :
    (SpecCharacteristicSupport A N).Nonempty := by
  by_contra hs
  have hk := (C.specSupport_empty_iff_layer_killed).mp
    (Set.not_nonempty_iff_eq_empty.mp hs)
  exact hx (hk x)

theorem exists_not_mem_next_of_specSupport_nonempty
    (hs : (SpecCharacteristicSupport A N).Nonempty) :
    ∃ x : F.carrier C.layer.1,
      (x : M) ∉ F.carrier (C.layer.1 + 1) := by
  by_contra h
  apply (Set.not_nonempty_iff_eq_empty.mpr
    (C.specSupport_empty_iff_layer_killed.mpr ?_)) hs
  intro x
  by_contra hx
  exact h ⟨x, hx⟩

theorem specSupport_nonempty_iff_exists_not_mem_next :
    (SpecCharacteristicSupport A N).Nonempty ↔
      ∃ x : F.carrier C.layer.1,
        (x : M) ∉ F.carrier (C.layer.1 + 1) := by
  constructor
  · exact C.exists_not_mem_next_of_specSupport_nonempty
  · rintro ⟨x, hx⟩
    exact C.specSupport_nonempty_of_not_mem_next x hx

theorem layer_killed_of_specSupport_empty
    (hs : SpecCharacteristicSupport A N = ∅) :
    ∀ x : F.carrier C.layer.1,
      (x : M) ∈ F.carrier (C.layer.1 + 1) :=
  (C.specSupport_empty_iff_layer_killed).mp hs

end ActualFilteredClassMap

end Layer

section Defect

variable {A : Type w} {N : Type z}
variable [CommRing A] [AddCommGroup N] [Module A N]

/-- A support dimension/defect witness whose bottom case is tied to the
    actual spectrum support, rather than being an unrelated integer field. -/
structure SpecSupportDimensionDefect
    (F : FiniteFilteredModule (R := R) (M := M))
    (C : ActualFilteredClassMap F A N) where
  dimension : SupportDimension
  defect : Int
  defect_eq_dimension : defect = supportDimensionDefect dimension
  dimension_bot_iff_support_empty :
    dimension = (⊥ : SupportDimension) ↔
      SpecCharacteristicSupport A N = ∅

namespace SpecSupportDimensionDefect

variable {F : FiniteFilteredModule (R := R) (M := M)}
variable {C : ActualFilteredClassMap F A N}
variable (D : SpecSupportDimensionDefect F C)

theorem bot_iff_defect_le_neg_one :
    D.dimension = (⊥ : SupportDimension) ↔ D.defect ≤ -1 := by
  rw [D.defect_eq_dimension, supportDimensionDefect_le_neg_one_iff]

theorem defect_le_neg_one_iff_layer_killed :
    D.defect ≤ -1 ↔
      ∀ x : F.carrier C.layer.1,
        (x : M) ∈ F.carrier (C.layer.1 + 1) := by
  rw [← D.bot_iff_defect_le_neg_one, D.dimension_bot_iff_support_empty]
  exact C.specSupport_empty_iff_layer_killed

theorem defect_gt_neg_one_of_not_mem_next
    (x : F.carrier C.layer.1)
    (hx : (x : M) ∉ F.carrier (C.layer.1 + 1)) :
    ¬ D.defect ≤ -1 := by
  intro h
  exact hx ((D.defect_le_neg_one_iff_layer_killed).mp h x)

end SpecSupportDimensionDefect

end Defect

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.ActualFilteredClassMap.specSupport_empty_iff_layer_killed
#print axioms SymplecticStafford.Filtered.SpecSupportDimensionDefect.defect_le_neg_one_iff_layer_killed
