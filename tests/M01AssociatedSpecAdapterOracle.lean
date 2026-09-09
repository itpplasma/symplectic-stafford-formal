import SymplecticStafford.Filtered.M01AssociatedSpecAdapter

/-! Independent oracle for the structural-to-spectrum M01 adapter. -/

namespace SymplecticStafford.M01AssociatedSpecAdapterOracle

open SymplecticStafford.Filtered

abbrev Q := ℚ
abbrev R := ℚ

def constantFiltration : AdditiveFilteredRingData R where
  carrier := fun _ => ⊤
  one_mem := by simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij a ha; simp
  exhaustive := by intro a; exact ⟨0, by simp⟩

def structuralModel : M01FilteredAlgebra ℚ R where
  filtration := constantFiltration
  central := by intro k a; ring
  degree_zero := by
    ext a
    constructor
    · intro ha
      exact ⟨a, by simp⟩
    · rintro ⟨k, rfl⟩
      exact (show k ∈ (⊤ : AddSubgroup R) by simp)

def quotientToRat :
    AdditiveFilteredRingData.associatedLayer constantFiltration 0 →+ ℚ where
  toFun := Quotient.lift (fun x : constantFiltration.carrier 0 => x.1)
    (by
      intro x y hxy
      have hq := (Submodule.quotientRel_def
        (AdditiveFilteredRingData.layerSubmodule constantFiltration 0)).mp hxy
      have hz : x.1 - y.1 ∈
          AdditiveFilteredRingData.predecessor constantFiltration 0 :=
        Submodule.mem_comap.mp hq
      have hz0 : x.1 - y.1 = 0 := by
        simpa [AdditiveFilteredRingData.predecessor] using hz
      exact sub_eq_zero.mp hz0)
  map_zero' := by
    change (Quotient.lift _ _) (Submodule.Quotient.mk
      (0 : constantFiltration.carrier 0)) = 0
    rfl
  map_add' := by
    intro x y
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    obtain ⟨y, rfl⟩ := Quotient.exists_rep y
    change (x.1 + y.1) = x.1 + y.1
    rfl

theorem quotientToRat_surjective : Function.Surjective quotientToRat := by
  intro q
  have hq : q ∈ constantFiltration.carrier 0 := by
    change q ∈ (⊤ : AddSubgroup ℚ)
    simp
  refine ⟨AdditiveFilteredRingData.associatedClass constantFiltration 0 q
    hq, ?_⟩
  rfl

theorem quotientToRat_eq_zero_iff (x :
    AdditiveFilteredRingData.associatedLayer constantFiltration 0) :
    quotientToRat x = 0 ↔ x = 0 := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep x
  constructor
  · intro hx
    apply (Submodule.Quotient.eq
      (AdditiveFilteredRingData.layerSubmodule constantFiltration 0)).mpr
    change x.1 - 0 ∈ AdditiveFilteredRingData.predecessor constantFiltration 0
    have hx0 : x.1 = 0 := hx
    rw [hx0]
    simp [AdditiveFilteredRingData.predecessor]
  · intro hx
    exact congrArg quotientToRat hx

def bridge :
    AssociatedGradedSpecBridge constantFiltration ℚ ℚ where
  layer := 0
  layerMap := quotientToRat
  surjective := quotientToRat_surjective
  layerMap_eq_zero_iff := quotientToRat_eq_zero_iff

def adapter : M01AssociatedSpecAdapter structuralModel ℚ ℚ where
  bridge := bridge

example :
    Module.support ℚ ℚ = ∅ ↔
      ∀ x : structuralModel.filtration.carrier adapter.bridge.layer,
        (x : R) ∈ AdditiveFilteredRingData.predecessor
          structuralModel.filtration adapter.bridge.layer :=
  adapter.support_empty_iff_layer_killed

example : (Module.support ℚ ℚ).Nonempty := by
  apply adapter.support_nonempty_iff_exists_not_mem_predecessor.mpr
  refine ⟨⟨1, by
    change (1 : ℚ) ∈ (⊤ : AddSubgroup ℚ)
    simp⟩, ?_⟩
  intro h
  change (1 : ℚ) ∈ AdditiveFilteredRingData.predecessor
    structuralModel.filtration 0 at h
  have h0 : (1 : ℚ) = 0 := by
    have hbot : (1 : ℚ) ∈ (⊥ : AddSubgroup ℚ) := by
      simpa [AdditiveFilteredRingData.predecessor] using h
    simpa using hbot
  norm_num at h0

  example :
    Module.support ℚ ℚ =
      PrimeSpectrum.zeroLocus (Module.annihilator ℚ ℚ : Set ℚ) :=
  support_eq_zeroLocus_annihilator_of_m01_adapter structuralModel adapter

end SymplecticStafford.M01AssociatedSpecAdapterOracle

#print axioms SymplecticStafford.M01AssociatedSpecAdapterOracle.adapter
#print axioms SymplecticStafford.Filtered.M01AssociatedSpecAdapter.support_empty_iff_layer_killed
#print axioms SymplecticStafford.Filtered.support_eq_zeroLocus_annihilator_of_m01_adapter
