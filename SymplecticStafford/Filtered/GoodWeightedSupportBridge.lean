module

public import SymplecticStafford.Filtered.GoodWeightedModule
public import SymplecticStafford.Filtered.SpecCharacteristicSupport

@[expose] public section

/-!
# Good-module weighted detection at an associated layer

The finite detector in `GoodWeightedModule` sees a module element in a finite
coefficient space, while `FilteredClassData` sees its class modulo the next
filtered layer.  This file records the exact compatibility needed to connect
the two: bounded elements lie in the selected class layer, and each detector
output factors through an additive coordinate of the class map.

Under those explicit fields, a nonzero element has a nonzero detector output,
a nonzero associated-layer quotient class, and nonempty spectrum support.  No
surjectivity, Rees construction, localization, or universal characteristic
support is inferred.
-/

namespace SymplecticStafford.Filtered

universe uK uR uM uI uA

section

variable {K : Type uK} {R : Type uR} {M : Type uM} {ι : Type uI}
variable {A : Type uA} {N : Type uR}
variable [Ring K] [NoZeroDivisors K]
variable [Ring R] [AddCommGroup M] [Module R M] [Module K M]
variable [Nonempty ι] [Fintype ι] [DecidableEq ι]
variable [CommRing A] [AddCommGroup N] [Module A N]

/-- Compatibility between a finite good-module detector and one actual
associated filtered class.  The factor equation is stated for every module
element and output coordinate; it is not a consequence of injectivity alone.
-/
structure DetectorClassCompatibility
    (D : GoodWeightedModuleData (K := K) (R := R) (M := M) (ι := ι) m)
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Type uA) (N : Type uR)
    [CommRing A] [AddCommGroup N] [Module A N] where
  classData : FilteredClassData F A N
  bounded_mem_layer : ∀ {x : M} {n : ℕ},
    ModuleHasDegreeAtMost D.moduleFiltration n x →
      x ∈ F.carrier classData.layer.1
  classCoordinate : ι → N →+ K
  coordinate_factor : ∀ (x : M) (i : ι),
    classCoordinate i (classData.classMap x) =
      D.detector.triangular.action (D.detector.encode x) i

namespace DetectorClassCompatibility

variable {m : ℕ}
variable {D : GoodWeightedModuleData
  (K := K) (R := R) (M := M) (ι := ι) m}
variable {F : FiniteFilteredModule (R := R) (M := M)}
variable
  (C : DetectorClassCompatibility
    (K := K) (R := R) (M := M) (ι := ι) (D := D) (F := F) A N)

theorem classMap_ne_zero_of_detected_output
    {x : M} {i : ι}
    (hi : D.detector.triangular.action (D.detector.encode x) i ≠ 0) :
    C.classData.classMap x ≠ 0 := by
  intro hzero
  have hfactor := C.coordinate_factor x i
  rw [hzero, map_zero] at hfactor
  exact hi hfactor.symm

theorem not_mem_next_of_detected_output
    {x : M} {i : ι}
    (hi : D.detector.triangular.action (D.detector.encode x) i ≠ 0) :
    x ∉ F.carrier (C.classData.layer.1 + 1) := by
  intro hnext
  apply C.classMap_ne_zero_of_detected_output hi
  exact C.classData.classMap_eq_zero_of_mem_next hnext

/-- The weighted detector produces a nonzero associated-layer quotient and its
    support witness, provided the explicit class-factor compatibility holds. -/
theorem exists_detecting_layer_and_support {x : M} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ i : ι,
      ModuleHasDegreeAtMost D.moduleFiltration n x ∧
      D.detector.triangular.action (D.detector.encode x) i ≠ 0 ∧
      ∃ k : ℕ, k < F.height ∧ x ∈ F.carrier k ∧
        Submodule.mkQ (F.carrier (k + 1)) x ≠ 0 ∧
        C.classData.classMap x ≠ 0 ∧
        (SpecCharacteristicSupport A N).Nonempty := by
  rcases D.exists_bounded_and_detected hx with ⟨n, hn, i, hi⟩
  have hlayer : x ∈ F.carrier C.classData.layer.1 :=
    C.bounded_mem_layer hn
  have hnext : x ∉ F.carrier (C.classData.layer.1 + 1) :=
    C.not_mem_next_of_detected_output hi
  have hquot : Submodule.mkQ (F.carrier (C.classData.layer.1 + 1)) x ≠ 0 :=
    (F.quotient_ne_zero_iff_not_mem x C.classData.layer.1).mpr hnext
  have hclass : C.classData.classMap x ≠ 0 :=
    C.classMap_ne_zero_of_detected_output hi
  have hsupport : (SpecCharacteristicSupport A N).Nonempty :=
    C.classData.specSupport_nonempty_of_filtered_class_ne_zero hlayer hclass
  exact ⟨n, i, hn, hi, C.classData.layer.1, C.classData.layer.2,
    hlayer, hquot, hclass, hsupport⟩

end DetectorClassCompatibility

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.DetectorClassCompatibility.exists_detecting_layer_and_support
