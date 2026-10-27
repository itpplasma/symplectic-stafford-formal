module

public import SymplecticStafford.Filtered.ReesModule
public import Mathlib.Tactic.NormNum

@[expose] public section

/- Independent behavioral checks for the filtered module quotient. -/
namespace SymplecticStafford.Filtered.ReesModuleOracle

def natFiltration : FiltrationData ℕ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def natModuleFiltration : ModuleFiltrationData natFiltration ℕ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  add_mem := by simp
  smul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def scalar : ReesTerm natFiltration :=
  ⟨2, 6, by simp [natFiltration, HasDegreeAtMost]⟩

def vector : ReesModuleTerm natModuleFiltration :=
  ⟨4, 7, by simp [natModuleFiltration, ModuleHasDegreeAtMost]⟩

def scalarClass : ReesQuotient natFiltration := ReesQuotient.mk scalar

def vectorClass : ReesModuleQuotient natModuleFiltration :=
  ReesModuleQuotient.mk vector

example : (ReesModuleTerm.smul scalar vector).value = 42 := by
  norm_num [ReesModuleTerm.smul, scalar, vector]

example :
    ReesModuleQuotient.value
        (ReesModuleQuotient.smul scalarClass vectorClass) = 42 := by
  norm_num [scalarClass, vectorClass, scalar, vector,
    ReesModuleQuotient.value_smul, ReesQuotient.value_mk,
    ReesModuleQuotient.value_mk]

example : (ReesModuleQuotient.add vectorClass vectorClass).value = 14 := by
  norm_num [vectorClass, vector, ReesModuleQuotient.value_add,
    ReesModuleQuotient.value_mk]

example :
    ReesModuleQuotient.smul scalarClass
        (ReesModuleQuotient.add vectorClass vectorClass) =
      ReesModuleQuotient.add
        (ReesModuleQuotient.smul scalarClass vectorClass)
        (ReesModuleQuotient.smul scalarClass vectorClass) := by
  exact ReesModuleQuotient.smul_add _ _ _

example :
    ReesModuleQuotient.smul ReesQuotient.one vectorClass = vectorClass := by
  exact ReesModuleQuotient.one_smul _

example : ∃ x : ReesModuleQuotient natModuleFiltration,
    ReesModuleQuotient.value x = 19 := by
  exact ReesModuleQuotient.exists_value natModuleFiltration 19

end SymplecticStafford.Filtered.ReesModuleOracle
