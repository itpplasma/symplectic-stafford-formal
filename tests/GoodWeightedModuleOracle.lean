module

public import Mathlib.Tactic
public import SymplecticStafford.Filtered.GoodWeightedModule
public import SymplecticStafford.Filtered.WeightedFaithfulCalibration

@[expose] public section

/- Independent behavioral oracle for the generic finite good-module/M04
   bridge.  This uses a constant filtered rational ring and a rank-one module,
   rather than the polynomial calibration, while assigning a negative weight
   to one detector slot. -/
namespace SymplecticStafford.Filtered.GoodWeightedModuleOracle

open GoodWeightedModuleData

def rationalFiltration : RingFiltrationData (R := ℚ) where
  carrier _ := ⊤
  one_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; exact le_rfl
  exhaustive := by intro x; exact ⟨0, by simp⟩

def generators : Fin 1 → ℚ := fun _ => 1

theorem generators_span_top :
    Submodule.span ℚ (Set.range generators) = (⊤ : Submodule ℚ ℚ) := by
  apply top_unique
  intro x hx
  have hone : (1 : ℚ) ∈ Submodule.span ℚ (Set.range generators) := by
    apply Submodule.subset_span
    exact ⟨0, rfl⟩
  simpa using Submodule.smul_mem
    (Submodule.span ℚ (Set.range generators)) x hone

def coordinateEncode : ℚ →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun x := fun _ => x
  map_add' x y := by funext i; simp
  map_smul' a x := by funext i; simp

def data : GoodWeightedModuleData
    (K := ℚ) (R := ℚ) (M := ℚ) (ι := Fin 2) 1 :=
  GoodWeightedModuleData.ofCoordinates rationalFiltration generators
    (fun _ => 3) generators_span_top coordinateEncode (by
      intro x y h
      exact congrFun h 0) (fun i => if i = 0 then (-7 : Int) else 2)

example : data.detector.triangular.action
    (data.detector.encode (5 : ℚ)) 0 = 5 := by
  norm_num [data, GoodWeightedModuleData.ofCoordinates, coordinateEncode,
    WeightedTriangularData.action,
    WeightedFaithfulCalibration.diagonalSystem, Fin.sum_univ_succ]

example : data.detector.triangular.action
    (data.detector.encode (5 : ℚ)) 1 = 5 := by
  norm_num [data, GoodWeightedModuleData.ofCoordinates, coordinateEncode,
    WeightedTriangularData.action,
    WeightedFaithfulCalibration.diagonalSystem, Fin.sum_univ_succ]

example : ModuleHasDegreeAtMost data.moduleFiltration 3 (5 : ℚ) := by
  change (5 : ℚ) ∈ GoodFiltration.carrier
    rationalFiltration.toFiltrationData generators (fun _ => 3) 3
  apply AddSubmonoid.subset_closure
  refine ⟨0, 0, 5, by simp, by simp [rationalFiltration], ?_⟩
  simp [generators]

example : ∃ n : ℕ,
    ModuleHasDegreeAtMost data.moduleFiltration n (5 : ℚ) ∧
      ∃ i, data.detector.triangular.action
        (data.detector.encode (5 : ℚ)) i ≠ 0 := by
  exact data.exists_bounded_and_detected (by norm_num)

def zeroCorrection : Matrix (Fin 2) (Fin 2) ℚ := fun _ _ => 0

example : ∃ n : ℕ,
    ModuleHasDegreeAtMost data.moduleFiltration n (5 : ℚ) ∧
      ∃ i, Matrix.vecMul
        (fun j => data.detector.triangular.action
          (data.detector.encode (5 : ℚ)) j)
        (1 - zeroCorrection) i ≠ 0 := by
  exact data.exists_bounded_and_detected_after_nilpotent_right_correction
    zeroCorrection 1 (by
      rw [pow_one]
      funext i j
      simp [zeroCorrection]) (by norm_num)

end SymplecticStafford.Filtered.GoodWeightedModuleOracle
