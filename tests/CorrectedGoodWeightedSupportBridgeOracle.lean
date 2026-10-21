module

public import Mathlib.Tactic
public import Mathlib.Data.Matrix.Basis
public import SymplecticStafford.Filtered.CorrectedGoodWeightedSupportBridge
public import SymplecticStafford.Filtered.WeightedFaithfulCalibration

@[expose] public section

/- Independent noncommutative calibration for the correction-aware bridge.
   The filtered ring is the noncommutative matrix ring Mat₂(ℚ), while the
   finite weighted detector uses scalar ℚ coordinates of its regular module. -/
namespace SymplecticStafford.Filtered.CorrectedGoodWeightedSupportBridgeOracle

abbrev R := Matrix (Fin 2) (Fin 2) ℚ
abbrev I := Fin 2 × Fin 2

def matrixFiltration : RingFiltrationData (R := R) where
  carrier _ := ⊤
  one_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; exact le_rfl
  exhaustive := by intro x; exact ⟨0, by simp⟩

def generators : Fin 1 → R := fun _ => 1

theorem generators_span_top :
    Submodule.span R (Set.range generators) = (⊤ : Submodule R R) := by
  apply top_unique
  intro x hx
  have hone : (1 : R) ∈ Submodule.span R (Set.range generators) := by
    apply Submodule.subset_span
    exact ⟨0, rfl⟩
  simpa [smul_eq_mul] using Submodule.smul_mem
    (Submodule.span R (Set.range generators)) x hone

def coordinateEncode : R →ₗ[ℚ] (I → ℚ) where
  toFun x := fun ij => x ij.1 ij.2
  map_add' x y := by funext ij; simp
  map_smul' a x := by funext ij; simp

def data : GoodWeightedModuleData
    (K := ℚ) (R := R) (M := R) (ι := I) 1 :=
  GoodWeightedModuleData.ofCoordinates matrixFiltration generators
    (fun _ => 3) generators_span_top coordinateEncode (by
      intro x y h
      funext a b
      exact congrFun h (a, b)) (fun ij =>
        if ij.1 = 0 then (-4 : Int) else 3)

def layers : FiniteFilteredModule (R := R) (M := R) where
  height := 1
  carrier := fun k => if k = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  separated := by simp

def classMap : R →+ (I → ℚ) where
  toFun x := fun ij => x ij.1 ij.2
  map_zero' := by funext ij; simp
  map_add' x y := by funext ij; simp

def classData : FilteredClassData layers ℚ (I → ℚ) where
  layer := ⟨0, by decide⟩
  classMap := classMap
  classMap_zero_iff_mem_next := by
    intro x
    constructor
    · intro h
      have hx : x = 0 := by
        funext a b
        simpa [classMap] using congrFun h (a, b)
      subst x
      simp [layers]
    · intro hx
      have hx0 : x = 0 := by simpa [layers] using hx
      subst x
      funext ij
      simp [classMap]

def classCoordinate (ij : I) : (I → ℚ) →+ ℚ where
  toFun v := v ij
  map_zero' := by simp
  map_add' v w := by simp

def correction : Matrix I I ℚ := Matrix.single
  ((0, 0) : I) ((0, 1) : I) 1

example : correction ((0, 0) : I) ((0, 1) : I) = (1 : ℚ) := by
  simp [correction]

def compatibility : CorrectedDetectorClassCompatibility
    data layers ℚ (I → ℚ) where
  classData := classData
  bounded_mem_layer := by
    intro x n hn
    simp [layers]
  classCoordinate := classCoordinate
  coordinate_factor := by
    intro x ij
    simp [classCoordinate, classData, classMap, data,
      GoodWeightedModuleData.ofCoordinates, coordinateEncode,
      WeightedTriangularData.action,
      WeightedFaithfulCalibration.diagonalSystem]
  correction := correction
  correctionExponent := 2
  correction_nilpotent := by
    rw [pow_two]
    change Matrix.single ((0, 0) : I) ((0, 1) : I) (1 : ℚ) *
      Matrix.single ((0, 0) : I) ((0, 1) : I) (1 : ℚ) = 0
    exact Matrix.single_mul_single_of_ne
      (l := I) (m := I) (n := I) (α := ℚ) (1 : ℚ)
      ((0, 0) : I) ((0, 1) : I) ((0, 0) : I) (by decide) 1
  correctedClassCoordinate := fun ij =>
    { toFun := fun v => Matrix.vecMul v
        ((1 : Matrix I I ℚ) - correction) ij
      map_zero' := by simp [Matrix.vecMul]
      map_add' := by
        intro v w
        simp [Matrix.vecMul] }
  corrected_coordinate_factor := by
    intro x ij
    simp [classCoordinate, classData, classMap, data,
      GoodWeightedModuleData.ofCoordinates,
      GoodWeightedModuleData.correctedAction, coordinateEncode,
      WeightedTriangularData.action,
      WeightedFaithfulCalibration.diagonalSystem]
    rfl

example : ∃ n : ℕ, ∃ i : I,
    ModuleHasDegreeAtMost data.moduleFiltration n
      (!![1, 0; 0, 0] : R) ∧
      data.correctedAction compatibility.correction
        (!![1, 0; 0, 0] : R) i ≠ 0 ∧
      ∃ k : ℕ, k < layers.height ∧
        (!![1, 0; 0, 0] : R) ∈ layers.carrier k ∧
        Submodule.mkQ (layers.carrier (k + 1))
          (!![1, 0; 0, 0] : R) ≠ 0 ∧
        classData.classMap (!![1, 0; 0, 0] : R) ≠ 0 ∧
        (SpecCharacteristicSupport ℚ (I → ℚ)).Nonempty := by
  apply compatibility.exists_corrected_detecting_layer_and_support
  intro h
  have hentry := congrFun (congrFun h 0) 0
  norm_num at hentry

end SymplecticStafford.Filtered.CorrectedGoodWeightedSupportBridgeOracle
