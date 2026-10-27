module

public import Mathlib.Tactic
public import SymplecticStafford.Filtered.GoodWeightedSupportBridge
public import SymplecticStafford.Filtered.WeightedFaithfulCalibration

@[expose] public section

/- Independent oracle for the good-module/associated-layer bridge.  The
   selected finite layer is concrete, and the class map is checked to factor
   both detector coordinates. -/
namespace SymplecticStafford.Filtered.GoodWeightedSupportBridgeOracle

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

def layers : FiniteFilteredModule (R := ℚ) (M := ℚ) where
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

def classMap : ℚ →+ (Fin 2 → ℚ) where
  toFun x := fun _ => x
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

def classData : FilteredClassData layers ℚ (Fin 2 → ℚ) where
  layer := ⟨0, by decide⟩
  classMap := classMap
  classMap_zero_iff_mem_next := by
    intro x
    constructor
    · intro h
      have hx : x = 0 := by simpa [classMap] using congrFun h 0
      subst x
      simp [layers]
    · intro hx
      have hx0 : x = 0 := by simpa [layers] using hx
      subst x
      funext i
      simp [classMap]

def classCoordinate (i : Fin 2) : (Fin 2 → ℚ) →+ ℚ where
  toFun v := v i
  map_zero' := by simp
  map_add' v w := by simp

def compatibility : DetectorClassCompatibility data layers ℚ (Fin 2 → ℚ) where
  classData := classData
  bounded_mem_layer := by
    intro x n hn
    simp [layers]
  classCoordinate := classCoordinate
  coordinate_factor := by
    intro x i
    simp [classCoordinate, classData, classMap, data,
      GoodWeightedModuleData.ofCoordinates, coordinateEncode,
      WeightedTriangularData.action,
      WeightedFaithfulCalibration.diagonalSystem, Fin.sum_univ_succ]

example : classData.classMap (5 : ℚ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [classData, classMap] at h0

example : Submodule.mkQ (layers.carrier (0 + 1)) (5 : ℚ) ≠ 0 := by
  intro hzero
  have hmk :
      (Submodule.Quotient.mk (5 : ℚ) :
        ℚ ⧸ layers.carrier (0 + 1)) = 0 := by
    simpa only [Submodule.mkQ_apply] using hzero
  have hmem : (5 : ℚ) ∈ layers.carrier (0 + 1) :=
    (Submodule.Quotient.mk_eq_zero (layers.carrier (0 + 1))).mp hmk
  norm_num [layers] at hmem

example : (SpecCharacteristicSupport ℚ (Fin 2 → ℚ)).Nonempty := by
  apply classData.specSupport_nonempty_of_filtered_class_ne_zero (x := (5 : ℚ))
  · simp [layers]
  · exact by
      intro h
      have h0 := congrFun h 0
      norm_num [classData, classMap] at h0

example : ∃ n : ℕ, ∃ i : Fin 2,
    ModuleHasDegreeAtMost data.moduleFiltration n (5 : ℚ) ∧
      data.detector.triangular.action (data.detector.encode (5 : ℚ)) i ≠ 0 ∧
      ∃ k : ℕ, k < layers.height ∧ (5 : ℚ) ∈ layers.carrier k ∧
        Submodule.mkQ (layers.carrier (k + 1)) (5 : ℚ) ≠ 0 ∧
        classData.classMap (5 : ℚ) ≠ 0 ∧
        (SpecCharacteristicSupport ℚ (Fin 2 → ℚ)).Nonempty := by
  exact compatibility.exists_detecting_layer_and_support (by norm_num)

example : (SpecCharacteristicSupport ℚ (Fin 2 → ℚ)).Nonempty := by
  rcases compatibility.exists_detecting_layer_and_support (x := (5 : ℚ))
      (by norm_num) with ⟨n, i, hn, hi, k, hk, hxk, hq, hclass, hs⟩
  exact hs

end SymplecticStafford.Filtered.GoodWeightedSupportBridgeOracle
