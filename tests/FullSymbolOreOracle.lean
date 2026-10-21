module

public import SymplecticStafford.Filtered.FullSymbolOre
public import Mathlib.Tactic.NormNum

@[expose] public section

/- Independent oracle for the full-symbol boundary.  The example uses the
   identity chart on ℚ, so all source/chart and original-U data are concrete. -/
namespace SymplecticStaffordTest.FullSymbolOre

open SymplecticStafford
open SymplecticStafford.Filtered

def rationalFiltration : FiltrationData ℚ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def rationalPowerOre : PowerOreLocalizationCertificate ℚ ℚ where
  sourceFiltration := rationalFiltration
  chartFiltration := rationalFiltration
  map := RingHom.id ℚ
  map_filtered := by intro n a ha; exact ha
  denominator := 2
  denominator_mem := ⟨0, by simp [HasDegreeAtMost, rationalFiltration]⟩
  right_clearable := by
    intro x
    exact ⟨0, x, by simp⟩
  inverse := (2 : ℚ)⁻¹
  denominator_mul_inverse := by norm_num
  inverse_mul_denominator := by norm_num
  right_ore := by
    intro a n
    exact ⟨n, a, by simp [mul_comm]⟩

def symbolLift : ReesTerm rationalFiltration :=
  { degree := 1, value := 2,
    bounded := by simp [HasDegreeAtMost, rationalFiltration] }

theorem symbolLift_nonzero :
    ReesQuotient.mk symbolLift ≠ ReesQuotient.zero := by
  intro h
  have hv := congrArg ReesQuotient.value h
  change (2 : ℚ) = 0 at hv
  norm_num at hv

def certificate : FullSymbolOreCertificate.Data ℚ ℚ where
  localization := rationalPowerOre
  symbolLift := symbolLift
  symbolLift_value := by rfl
  symbolLift_nonzero := symbolLift_nonzero
  map_injective := by
    intro x y h
    exact h

example : Function.Bijective (FullSymbolOreCertificate.fractionEval certificate) :=
  FullSymbolOreCertificate.fractionEval_bijective certificate

example : ∃! q : certificate.localization.PowerFraction,
    FullSymbolOreCertificate.fractionEval certificate q = (3 : ℚ) := by
  exact FullSymbolOreCertificate.exists_unique_fraction certificate 3

example :
    FullSymbolOreCertificate.fractionEval certificate
        (certificate.localization.fractionMk 3 2) =
      FullSymbolOreCertificate.fractionEval certificate
        (certificate.localization.fractionMk 12 4) ↔
      certificate.localization.fractionRel (3, 2) (12, 4) := by
  exact FullSymbolOreCertificate.fractionEval_eq_iff_fractionRel certificate
    (p := (3, 2)) (q := (12, 4))

example : ∃ n : Nat, ∀ x ∈
    ([symbolLift, symbolLift] : List (ReesTerm
      certificate.localization.sourceFiltration)),
    ∃ a : ℚ,
      certificate.localization.map x.value =
        certificate.localization.map a * certificate.localization.inverse ^ n := by
  exact FullSymbolOreCertificate.finite_symbol_common_fraction_power certificate _

end SymplecticStaffordTest.FullSymbolOre
