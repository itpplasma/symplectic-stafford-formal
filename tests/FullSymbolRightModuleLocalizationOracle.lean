module

public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Filtered.FullSymbolRightModuleLocalization

@[expose] public section

/- Independent behavioral oracle: a finite family of localized rational
modules over the powers of 2 has one denominator in the original ring. -/
namespace SymplecticStaffordTest.FullSymbolRightModuleLocalization

open SymplecticStafford.Filtered

def powersData : FullSymbolRightLocalization.Data ℚ where
  denominators := Submonoid.powers (2 : ℚ)
  regular := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simp
  ore := inferInstance

abbrev ML := FullSymbolRightModuleLocalization.ModuleLocalization powersData ℚᵐᵒᵖ

def q₁ : ML := FullSymbolRightModuleLocalization.moduleFraction powersData (1 : ℚᵐᵒᵖ)
  ⟨1, by simp⟩

def q₂ : ML := FullSymbolRightModuleLocalization.moduleFraction powersData (3 : ℚᵐᵒᵖ)
  ⟨2, by
    change (2 : ℚ) ∈ Submonoid.powers (2 : ℚ)
    exact Submonoid.mem_powers (2 : ℚ)⟩

example : ∃ s : powersData.denominators, ∀ q ∈ [q₁, q₂], ∃ m : ℚᵐᵒᵖ,
  q = FullSymbolRightModuleLocalization.rightModuleFraction powersData m s := by
  exact FullSymbolRightModuleLocalization.common_right_module_fraction powersData [q₁, q₂]

example : Function.Injective powersData.numerator :=
  powersData.numerator_injective

end SymplecticStaffordTest.FullSymbolRightModuleLocalization
