import SymplecticStafford.Filtered.GoodFiltration
import SymplecticStafford.Filtered.RingFiltrationBridge
import SymplecticStafford.Filtered.WeightedDetectionComposition
import SymplecticStafford.Filtered.WeightedFaithfulCalibration

/-!
# Finite good modules with weighted detection

This file is the module-side M04 bridge for explicit finite data.  A
`RingFiltrationData` and finitely many bounded module generators construct the
actual exhaustive good filtration.  Independently supplied injective finite
coordinates, with an integer-weighted triangular action, then detect every
nonzero module element.  The weights are integers, so negative degrees are
allowed without shifting or truncating the module filtration.

The coordinate detector remains an input: finite bounded generation alone does
not produce faithful finite coordinates for an arbitrary module.  Thus this
API records exactly the algebraic boundary while composing the two proved
finite constructions, including the finite nilpotent right-correction step.
-/

namespace SymplecticStafford.Filtered

universe uK uR uM uI

section

variable {K : Type uK} {R : Type uR} {M : Type uM} {ι : Type uI}
variable [Ring K] [NoZeroDivisors K]
variable [Ring R] [AddCommGroup M] [Module R M] [Module K M]
variable [Nonempty ι] [Fintype ι] [DecidableEq ι]

/-!
The finite module presentation and the weighted detector are deliberately
separate fields.  This permits a coefficient field `K` different from the
filtered ring `R`, as in an associated/localized coefficient calculation.
-/
structure GoodWeightedModuleData (m : ℕ) where
  filtration : RingFiltrationData (R := R)
  generators : Fin m → M
  bounds : Fin m → ℕ
  span_top : Submodule.span R (Set.range generators) = ⊤
  detector : FaithfulWeightedDetector (ι := ι) (K := K) (M := M)

/-!
When the finite-coordinate action is diagonal, the faithful detector itself is
canonical.  This constructor keeps the only required input—an injective
coordinate map—and accepts arbitrary integer weights, including negative ones.
-/
section CoordinateConstructor

variable [Nontrivial K]

def GoodWeightedModuleData.ofCoordinates
    {m : ℕ}
    (filtration : RingFiltrationData (R := R))
    (generators : Fin m → M) (bounds : Fin m → ℕ)
    (span_top : Submodule.span R (Set.range generators) = ⊤)
    (encode : M →ₗ[K] (ι → K))
    (encode_injective : Function.Injective encode)
    (weight : ι → Int) :
    GoodWeightedModuleData (K := K) (R := R) (M := M) (ι := ι) m :=
  { filtration := filtration
    generators := generators
    bounds := bounds
    span_top := span_top
    detector :=
      { encode := encode
        encode_injective := encode_injective
        triangular := WeightedFaithfulCalibration.diagonalSystem weight } }

end CoordinateConstructor

namespace GoodWeightedModuleData

variable (D : GoodWeightedModuleData (K := K) (R := R) (M := M) (ι := ι) m)

/- The actual good filtration obtained from the finite bounded generators. -/
def moduleFiltration : ModuleFiltrationData
    D.filtration.toFiltrationData M :=
  GoodFiltration.moduleFiltration D.filtration.toFiltrationData
    D.generators D.bounds D.span_top

@[simp] theorem moduleFiltration_carrier (n : ℕ) :
    (D.moduleFiltration).carrier n =
      GoodFiltration.carrier D.filtration.toFiltrationData
        D.generators D.bounds n := rfl

theorem generator_mem (i : Fin m) :
    D.generators i ∈ D.moduleFiltration.carrier (D.bounds i) := by
  exact GoodFiltration.generator_mem D.filtration.toFiltrationData
    D.generators D.bounds i

theorem exhaustive (x : M) :
    ∃ n : ℕ, ModuleHasDegreeAtMost D.moduleFiltration n x :=
  D.moduleFiltration.exhaustive x

/-- A nonzero element has both a finite filtration bound and a detected
    weighted output coordinate. -/
theorem exists_bounded_and_detected {x : M} (hx : x ≠ 0) :
    ∃ n : ℕ, ModuleHasDegreeAtMost D.moduleFiltration n x ∧
      ∃ i, D.detector.triangular.action
        (D.detector.encode x) i ≠ 0 := by
  rcases D.exhaustive x with ⟨n, hn⟩
  exact ⟨n, hn, D.detector.detect_nonzero hx⟩

/- The explicit return type fixes both matrix dimensions before Lean elaborates
   the homogeneous subtraction. -/
def correctedAction (C : Matrix ι ι K) (x : M) : ι → K :=
  let output : ι → K := fun j => D.detector.triangular.action
    (D.detector.encode x) j
  let correction : Matrix ι ι K :=
    (1 : Matrix ι ι K) - C
  Matrix.vecMul output correction

/-- The same finite weighted detection survives an explicitly nilpotent right
    correction, preserving the row/action order in the original coefficient
    ring. -/
theorem exists_bounded_and_detected_after_nilpotent_right_correction
    (C : Matrix ι ι K) (q : ℕ) (hC : C ^ q = 0)
    {x : M} (hx : x ≠ 0) :
    ∃ n : ℕ, ModuleHasDegreeAtMost D.moduleFiltration n x ∧
      ∃ i : ι, D.correctedAction C x i ≠ 0 := by
  rcases D.exhaustive x with ⟨n, hn⟩
  rcases D.detector.detect_after_nilpotent_right_correction C q hC hx with
    ⟨i, hi⟩
  exact ⟨n, hn, i, hi⟩

end GoodWeightedModuleData

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.GoodWeightedModuleData.exists_bounded_and_detected
#print axioms
  SymplecticStafford.Filtered.GoodWeightedModuleData.exists_bounded_and_detected_after_nilpotent_right_correction
