import SymplecticStafford.Source.DivisionLLDList
import SymplecticStafford.Source.OriginalTestContract

/-!
# Original-`U` source production from bridged division tests

`OriginalTestContract` intentionally leaves each local generation predicate
unconstrained.  This file supplies the exact additional M06 input needed by
the finite division-coefficient argument: every local test carries a nonzero
coefficient and a theorem that a nonzero affine pencil passes that test.

The finite-root selector from `DivisionLLDList` then constructs one literal
multiplier `H : U` for the whole finite list.  The output retains the original
local-test predicates, integer offsets, nonzero right tails, and admissibility
at the common divisor.  No source witness is supplied; only the local pencil
bridges are supplied.  The theorem remains conditional on those bridges and
does not claim they follow from finite length or localization metadata.
-/

namespace SymplecticStafford.Source

universe u v w

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

/-- A local original-`U` test with its division-coefficient pencil bridge.

The bridge is quantified over every coefficient embedding and every affine
background/tail, so the selector may use one common embedding for all tests.
The original test remains a separate field, preserving its localization,
finite-length, canonical-generator, offset, and right-tail data. -/
structure OriginalDivisionTest
    (U : Type u) (K : Type v) (LocalizationData : Type w)
    (CyclicModuleData : Type*) [DivisionRing U] [Field K] where
  localTest : OriginalLocalTest U LocalizationData CyclicModuleData
  vCoeff : U
  uCoeff : U
  vCoeff_ne_zero : vCoeff ≠ 0
  passes_of_pencil_ne_zero :
    ∀ (ι : K →+* U) (B a : U) (z : K),
      vCoeff + ι z * uCoeff ≠ 0 →
        localTest.Passes (B + ι z * a)

namespace OriginalDivisionTest

variable {LocalizationData : Type w} {CyclicModuleData : Type*}

/-- Forgetful list item used by the generic finite-root selector.  The
generation predicate includes literal equality of the supplied offset and
right tail, so neither field is dropped by the adapter. -/
def toAffineDivisionTest
    (t : OriginalDivisionTest U K LocalizationData CyclicModuleData) :
    AffineDivisionTest U K where
  vCoeff := t.vCoeff
  uCoeff := t.uCoeff
  vCoeff_ne_zero := t.vCoeff_ne_zero
  offset := t.localTest.offset
  rightTail := t.localTest.rightTail
  rightTail_ne_zero := t.localTest.rightTail_nonzero
  passes := fun source gotOffset gotTail =>
    t.localTest.Passes source ∧
      gotOffset = t.localTest.offset ∧
      gotTail = t.localTest.rightTail
  passes_of_pencil_ne_zero := by
    intro ι B a z hp
    exact ⟨t.passes_of_pencil_ne_zero ι B a z hp, rfl, rfl⟩

theorem toAffineDivisionTest_passes
    (t : OriginalDivisionTest U K LocalizationData CyclicModuleData)
    (source : U) :
    (toAffineDivisionTest t).passes source
      (toAffineDivisionTest t).offset
      (toAffineDivisionTest t).rightTail ↔
      t.localTest.Passes source := by
  simp [toAffineDivisionTest]

end OriginalDivisionTest

/-!
The producer theorem is stated with the admissibility predicate from the
original contract.  Its arithmetic part is independent of those static
fields, but carrying the hypothesis and returning it makes the common
divisor/finite-list boundary explicit to downstream induction code.
-/
theorem exists_original_affine_source_of_bridged_list
    {LocalizationData : Type w} {CyclicModuleData : Type*}
    (ι : K →+* U) (hι : Function.Injective ι)
    (tests : List (OriginalDivisionTest U K LocalizationData CyclicModuleData))
    (d B a : U) (ha : a ≠ 0)
    (hadmissible : ∀ t, t ∈ tests → t.localTest.Admissible d) :
    ∃ (H source : U),
      source = B + H * a ∧
      (∀ t, t ∈ tests → t.localTest.Admissible d) ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.localTest.rightTail ≠ 0) := by
  let affineTests : List (AffineDivisionTest U K) :=
    tests.map OriginalDivisionTest.toAffineDivisionTest
  obtain ⟨H, source, hsource, hpasses, htails⟩ :=
    exists_original_affine_source_of_list ι hι affineTests B a
  refine ⟨H, source, hsource, hadmissible, ?_, ?_⟩
  · intro t ht
    have hmem : OriginalDivisionTest.toAffineDivisionTest t ∈ affineTests := by
      exact List.mem_map_of_mem ht
    have hp := hpasses (OriginalDivisionTest.toAffineDivisionTest t) hmem
    exact (OriginalDivisionTest.toAffineDivisionTest_passes t source).mp hp
  · intro t ht
    have hmem : OriginalDivisionTest.toAffineDivisionTest t ∈ affineTests := by
      exact List.mem_map_of_mem ht
    have htail := htails (OriginalDivisionTest.toAffineDivisionTest t) hmem
    exact htail

end SymplecticStafford.Source

#print axioms
  SymplecticStafford.Source.OriginalDivisionTest.toAffineDivisionTest_passes
#print axioms SymplecticStafford.Source.exists_original_affine_source_of_bridged_list
