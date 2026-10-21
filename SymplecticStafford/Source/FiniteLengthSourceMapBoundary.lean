module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.FiniteLength
public import SymplecticStafford.Source.OriginalDivisionProducer

@[expose] public section

/-!
# Finite length does not produce an original-U source map

The minimal-prime bridge supplies a finite-length local module, but that fact
alone does not connect an original source to a cyclic vector in the local
module.  This boundary keeps an actual finite-length module and an actual
`CyclicTopBridge`, while taking the source map to be zero.  Every local pass
then fails, including on every affine line in the original ring.

The example is intentionally a boundary for the *interface*: it does not
refute the paper's source theorem.  It identifies the additional algebraic
input required from a localization, namely a source map with enough image (in
the paper this is supplied by the original-U simple-module/no-finite-rank
argument, together with the relevant canonical generator).
-/

namespace SymplecticStafford.Source

open SymplecticStafford.FiniteLength

abbrev FiniteLengthBoundaryU := ℚ
abbrev FiniteLengthBoundaryK := ℚ
abbrev FiniteLengthBoundaryR := ℚ
abbrev FiniteLengthBoundaryM := ℚᵐᵒᵖ
abbrev FiniteLengthBoundaryI := Unit
abbrev FiniteLengthBoundaryD (_ : FiniteLengthBoundaryI) := ℚ

def boundaryLocalTest :
    OriginalLocalTest FiniteLengthBoundaryU Unit FiniteLengthBoundaryM where
  targetDivisor := 1
  localization := ()
  cyclicFiniteModule := (0 : FiniteLengthBoundaryM)
  canonicalGenerator := (1 : FiniteLengthBoundaryM)
  rightTail := 1
  offset := 0
  localization_spec := True
  localization_spec_proof := True.intro
  finite_length_cyclic_spec :=
    IsFiniteLength (FiniteLengthBoundaryRᵐᵒᵖ) FiniteLengthBoundaryM
  finite_length_cyclic_proof := by
    apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
    exact ⟨inferInstance, inferInstance⟩
  canonical_generator_spec := (1 : FiniteLengthBoundaryM) ≠ 0
  canonical_generator_spec_proof := by norm_num
  rightTail_nonzero := by norm_num
  generation := fun _ _ _ =>
    RightCyclic (R := FiniteLengthBoundaryR) (0 : FiniteLengthBoundaryM)

def boundaryTop : FiniteLengthBoundaryM →+
    (∀ _ : FiniteLengthBoundaryI, FiniteLengthBoundaryD ()) :=
  0

def boundaryBridge :
    CyclicTopBridge (R := FiniteLengthBoundaryR)
      (M := FiniteLengthBoundaryM)
      (fun _ : FiniteLengthBoundaryI => RingHom.id FiniteLengthBoundaryK) where
  top := boundaryTop
  map_smul := by
    intro z m i
    simp [boundaryTop]
  reflects_generation := by
    intro m hm
    have hzero : boundaryTop m () = 0 := by simp [boundaryTop]
    have hne : boundaryTop m () ≠ 0 :=
      (semisimple_top_criterion (boundaryTop m)).mp hm ()
    exact False.elim (hne hzero)

def boundarySourceMap : FiniteLengthBoundaryU →+ FiniteLengthBoundaryM := 0

def boundaryTest :
    ActualOriginalDivisionTest FiniteLengthBoundaryU FiniteLengthBoundaryK Unit
      FiniteLengthBoundaryM
      FiniteLengthBoundaryR FiniteLengthBoundaryM FiniteLengthBoundaryI
      FiniteLengthBoundaryD
      (RingHom.id FiniteLengthBoundaryK)
      (fun _ : FiniteLengthBoundaryI => RingHom.id FiniteLengthBoundaryK) where
  localTest := boundaryLocalTest
  bridge := boundaryBridge
  sourceMap := boundarySourceMap
  sourceMap_scalar := by
    intro z x
    simp [boundarySourceMap]
  passes_iff_cyclic := by
    intro source
    simp only [boundaryLocalTest, OriginalLocalTest.Passes]
    constructor
    · intro h
      exact h
    · intro h
      exact h

theorem boundary_module_isFiniteLength :
    IsFiniteLength (FiniteLengthBoundaryRᵐᵒᵖ) FiniteLengthBoundaryM := by
  apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
  exact ⟨inferInstance, inferInstance⟩

theorem boundary_test_passes_iff_cyclic (source : FiniteLengthBoundaryU) :
    boundaryTest.localTest.Passes source ↔
      RightCyclic (R := FiniteLengthBoundaryR) (boundarySourceMap source) := by
  exact boundaryTest.passes_iff_cyclic source

theorem no_affine_source_from_finite_length_bridge :
    ¬ ∃ (H source : FiniteLengthBoundaryU),
      source = 1 + H * (1 : FiniteLengthBoundaryU) ∧
      boundaryTest.localTest.Passes source := by
  rintro ⟨H, source, hsource, hpass⟩
  have hcyclic : RightCyclic (R := FiniteLengthBoundaryR)
      (boundarySourceMap source) :=
    (boundaryTest.passes_iff_cyclic source).mp hpass
  have hzero : boundarySourceMap source = 0 := by
    simp [boundarySourceMap]
  rw [hzero] at hcyclic
  obtain ⟨r, hr⟩ := hcyclic 1
  have hrzero : r • (0 : FiniteLengthBoundaryM) = 0 := by simp
  rw [hrzero] at hr
  norm_num at hr

theorem finite_length_and_top_bridge_do_not_supply_source :
    IsFiniteLength (FiniteLengthBoundaryRᵐᵒᵖ) FiniteLengthBoundaryM ∧
      ¬ ∃ (H source : FiniteLengthBoundaryU),
        source = 1 + H * (1 : FiniteLengthBoundaryU) ∧
        boundaryTest.localTest.Passes source := by
  exact ⟨boundary_module_isFiniteLength,
    no_affine_source_from_finite_length_bridge⟩

end SymplecticStafford.Source

#print axioms SymplecticStafford.Source.boundary_module_isFiniteLength
#print axioms SymplecticStafford.Source.no_affine_source_from_finite_length_bridge
#print axioms SymplecticStafford.Source.finite_length_and_top_bridge_do_not_supply_source
