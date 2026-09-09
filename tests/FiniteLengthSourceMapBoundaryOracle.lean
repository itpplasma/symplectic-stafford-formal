import Mathlib.Algebra.Field.Rat
import Mathlib.RingTheory.FiniteLength
import SymplecticStafford.Source.FiniteLengthSourceMapBoundary

/- Independent behavioral oracle for the source-map boundary. -/

namespace SymplecticStafford.Source.FiniteLengthSourceMapBoundaryOracle

open SymplecticStafford.FiniteLength
open SymplecticStafford.Source

example : IsFiniteLength (FiniteLengthBoundaryRᵐᵒᵖ) FiniteLengthBoundaryM := by
  apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
  exact ⟨inferInstance, inferInstance⟩

example (source : FiniteLengthBoundaryU) :
    ¬ boundaryTest.localTest.Passes source := by
  intro h
  have hcyclic : RightCyclic (R := FiniteLengthBoundaryR)
      (boundarySourceMap source) :=
    (boundaryTest.passes_iff_cyclic source).mp h
  have hzero : boundarySourceMap source = 0 := by
    simp [boundarySourceMap]
  rw [hzero] at hcyclic
  obtain ⟨r, hr⟩ := hcyclic 1
  have hrzero : r • (0 : FiniteLengthBoundaryM) = 0 := by simp
  rw [hrzero] at hr
  norm_num at hr

example : ¬ ∃ (H source : FiniteLengthBoundaryU),
    source = 1 + H * (1 : FiniteLengthBoundaryU) ∧
    boundaryTest.localTest.Passes source := by
  exact no_affine_source_from_finite_length_bridge

end SymplecticStafford.Source.FiniteLengthSourceMapBoundaryOracle
