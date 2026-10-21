module

public import SymplecticStafford.Filtered.FullSymbolRightPowerBridge
public import Mathlib.Tactic.NormNum

@[expose] public section

/- Independent behavioral oracle for the right-power bridge.  The chart is an
   actual Mathlib right Ore localization of ℚ at the powers of 2.  Its inverse,
   right clearing, and right Ore fields are therefore derived by the bridge,
   rather than entered in the power certificate. -/
namespace SymplecticStaffordTest.FullSymbolRightPowerBridge

open SymplecticStafford
open SymplecticStafford.Filtered
open AlgebraicAnalysis.OreRightLocalization

def rationalFiltration : FiltrationData ℚ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by intro i j a b ha hb; simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def powersLocalization : FullSymbolRightLocalization.Data ℚ where
  denominators := Submonoid.powers (2 : ℚ)
  regular := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simp
  ore := inferInstance

def chartFiltration : FiltrationData powersLocalization.Localization where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by intro i j a b ha hb; simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def symbolLift : ReesTerm rationalFiltration :=
  { degree := 1, value := 2,
    bounded := by simp [HasDegreeAtMost, rationalFiltration] }

theorem symbolLift_nonzero :
    ReesQuotient.mk symbolLift ≠ ReesQuotient.zero := by
  intro h
  have hv := congrArg ReesQuotient.value h
  change (2 : ℚ) = 0 at hv
  norm_num at hv

noncomputable def data : FullSymbolRightPowerBridge.Data ℚ where
  localization := powersLocalization
  sourceFiltration := rationalFiltration
  chartFiltration := chartFiltration
  map_filtered := by
    intro n a ha
    change powersLocalization.numerator a ∈ Set.univ
    exact Set.mem_univ _
  denominator := 2
  denominators_eq_powers := rfl
  denominator_mem := ⟨0, by simp [HasDegreeAtMost, rationalFiltration]⟩
  symbolLift := symbolLift
  symbolLift_value := rfl
  symbolLift_nonzero := symbolLift_nonzero

example : Function.Bijective
    (FullSymbolOreCertificate.fractionEval data.toCertificate) :=
  data.fractionEval_bijective

example (xs : List (ReesTerm data.sourceFiltration)) :
    ∃ n : Nat, ∀ x ∈ xs, ∃ a : ℚ,
      data.localization.numerator x.value =
        data.localization.numerator a * data.toPowerOre.inverse ^ n :=
  data.finite_symbol_common_fraction_power xs

example : Function.Injective data.toPowerOre.map :=
  data.toPowerOre_map_injective

end SymplecticStaffordTest.FullSymbolRightPowerBridge
