module

public import SymplecticStafford.Filtered.ReesModuleShift
public import Mathlib.Tactic.NormNum

@[expose] public section

/- Independent oracle for the degree-shifted, kernel-checked quotient map. -/
namespace SymplecticStaffordTest.ReesModuleShift

open SymplecticStafford.Filtered

noncomputable section

def scalarFiltration : FiltrationData ℤ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def moduleFiltration : ModuleFiltrationData scalarFiltration ℤ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  add_mem := by simp
  smul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def shiftIdentity (d : ℕ) :
    ShiftedFilteredLinearMap scalarFiltration moduleFiltration moduleFiltration d where
  toFun := id
  map_zero' := rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl
  filtered' := by intro n x hx; simp [moduleFiltration]

def scalar : ReesTerm scalarFiltration :=
  ⟨2, 3, by simp [scalarFiltration, HasDegreeAtMost]⟩

def vector : ReesModuleTerm moduleFiltration :=
  ⟨4, 5, by simp [moduleFiltration, ModuleHasDegreeAtMost]⟩

def scalarClass : ReesQuotient scalarFiltration := ReesQuotient.mk scalar
def vectorClass : ReesModuleQuotient moduleFiltration :=
  ReesModuleQuotient.mk vector

example :
    (ShiftedFilteredLinearMap.mapTerm (shiftIdentity 3) vector).degree = 7 := by
  rfl

example :
    ReesModuleQuotient.value
      (ShiftedFilteredLinearMap.mapQuotient (shiftIdentity 3) vectorClass) = 5 := by
  norm_num [vectorClass, vector,
    shiftIdentity,
    ShiftedFilteredLinearMap.value_mapQuotient,
    ReesModuleQuotient.value_mk]

example :
    ShiftedFilteredLinearMap.mapQuotient (shiftIdentity 3)
        (ReesModuleQuotient.add vectorClass vectorClass) =
      ReesModuleQuotient.add
        (ShiftedFilteredLinearMap.mapQuotient (shiftIdentity 3) vectorClass)
        (ShiftedFilteredLinearMap.mapQuotient (shiftIdentity 3) vectorClass) := by
  exact ShiftedFilteredLinearMap.mapQuotient_add _ _ _

example :
    ShiftedFilteredLinearMap.mapQuotient (shiftIdentity 3)
        (ReesModuleQuotient.smul scalarClass vectorClass) =
      ReesModuleQuotient.smul scalarClass
        (ShiftedFilteredLinearMap.mapQuotient (shiftIdentity 3) vectorClass) := by
  exact ShiftedFilteredLinearMap.mapQuotient_smul _ _ _

end

end SymplecticStaffordTest.ReesModuleShift
