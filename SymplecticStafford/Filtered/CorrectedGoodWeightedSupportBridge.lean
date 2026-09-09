import SymplecticStafford.Filtered.GoodWeightedSupportBridge

/-!
# Corrected weighted detection at an associated layer

This is the correction-aware M04/M01 composition.  The base detector/class
compatibility is retained, while a finite nilpotent right correction receives
its own additive class-coordinate factorization.  The latter is necessary:
the corrected row is generally not the same coordinate as the uncorrected
weighted output.

The resulting theorem turns corrected nonzero detection into an actual
next-layer quotient witness and nonempty spectrum support.  The correction
matrix, its nilpotence certificate, and both factorization interfaces remain
explicit hypotheses; no completion or universal good-module construction is
claimed.
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

structure CorrectedDetectorClassCompatibility
    (D : GoodWeightedModuleData (K := K) (R := R) (M := M) (ι := ι) m)
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Type uA) (N : Type uR)
    [CommRing A] [AddCommGroup N] [Module A N]
    extends DetectorClassCompatibility D F A N where
  correction : Matrix ι ι K
  correctionExponent : ℕ
  correction_nilpotent : correction ^ correctionExponent = 0
  correctedClassCoordinate : ι → N →+ K
  corrected_coordinate_factor : ∀ (x : M) (i : ι),
    correctedClassCoordinate i (classData.classMap x) =
      D.correctedAction correction x i

namespace CorrectedDetectorClassCompatibility

variable {m : ℕ}
variable {D : GoodWeightedModuleData
  (K := K) (R := R) (M := M) (ι := ι) m}
variable {F : FiniteFilteredModule (R := R) (M := M)}
variable
  (C : CorrectedDetectorClassCompatibility
    (K := K) (R := R) (M := M) (ι := ι) (D := D) (F := F) A N)

theorem classMap_ne_zero_of_corrected_detected_output
    {x : M} {i : ι}
    (hi : D.correctedAction C.correction x i ≠ 0) :
    C.classData.classMap x ≠ 0 := by
  intro hzero
  have hfactor := C.corrected_coordinate_factor x i
  rw [hzero, map_zero] at hfactor
  exact hi hfactor.symm

theorem not_mem_next_of_corrected_detected_output
    {x : M} {i : ι}
    (hi : D.correctedAction C.correction x i ≠ 0) :
    x ∉ F.carrier (C.classData.layer.1 + 1) := by
  intro hnext
  apply C.classMap_ne_zero_of_corrected_detected_output hi
  exact C.classData.classMap_eq_zero_of_mem_next hnext

/-- A corrected weighted detector yields a nonzero associated-layer quotient
    and support witness while retaining the original detector compatibility. -/
theorem exists_corrected_detecting_layer_and_support {x : M} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ i : ι,
      ModuleHasDegreeAtMost D.moduleFiltration n x ∧
      D.correctedAction C.correction x i ≠ 0 ∧
      ∃ k : ℕ, k < F.height ∧ x ∈ F.carrier k ∧
        Submodule.mkQ (F.carrier (k + 1)) x ≠ 0 ∧
        C.classData.classMap x ≠ 0 ∧
        (SpecCharacteristicSupport A N).Nonempty := by
  rcases D.exists_bounded_and_detected_after_nilpotent_right_correction
      C.correction C.correctionExponent C.correction_nilpotent hx with
    ⟨n, hn, i, hi⟩
  have hlayer : x ∈ F.carrier C.classData.layer.1 :=
    C.bounded_mem_layer hn
  have hnext : x ∉ F.carrier (C.classData.layer.1 + 1) :=
    C.not_mem_next_of_corrected_detected_output hi
  have hquot : Submodule.mkQ (F.carrier (C.classData.layer.1 + 1)) x ≠ 0 :=
    (F.quotient_ne_zero_iff_not_mem x C.classData.layer.1).mpr hnext
  have hclass : C.classData.classMap x ≠ 0 :=
    C.classMap_ne_zero_of_corrected_detected_output hi
  have hsupport : (SpecCharacteristicSupport A N).Nonempty :=
    C.classData.specSupport_nonempty_of_filtered_class_ne_zero hlayer hclass
  exact ⟨n, i, hn, hi, C.classData.layer.1, C.classData.layer.2,
    hlayer, hquot, hclass, hsupport⟩

end CorrectedDetectorClassCompatibility

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.CorrectedDetectorClassCompatibility.exists_corrected_detecting_layer_and_support
