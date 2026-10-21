module

public import SymplecticStafford.Filtered.FullSymbolOre
public import SymplecticStafford.Filtered.FullSymbolRightLocalization

@[expose] public section

/-!
# Power-chart bridge from an actual right Ore localization

The power-Ore certificate used by the finite fraction API has three fields
which are often tempting to read off from a formal chart: an inverse, chart
wide right clearing, and right Ore equations.  This file derives those fields
from Mathlib's actual right Ore localization when the chosen denominator
monoid is explicitly the powers of one original-ring element.

The equality with a power monoid is an algebraic hypothesis, not a principal
symbol or completion argument.  Filtration bounds and the nonzero algebraic
Rees lift remain explicit, so this bridge does not claim the missing universal
quantum source theorem.
-/

namespace SymplecticStafford.Filtered

universe u

namespace FullSymbolRightPowerBridge

open AlgebraicAnalysis.OreRightLocalization

variable {R : Type u} [Ring R]

/-- Data for a genuine right-localized power chart.

The `localization` field carries regularity and the actual Ore structure on
the opposite ring.  The equation `denominators_eq_powers` identifies its full
denominator set with the powers of `denominator`; it is what permits the
power-oriented API to be recovered without any completion shortcut.
-/
structure Data (R : Type u) [Ring R] where
  localization : FullSymbolRightLocalization.Data R
  sourceFiltration : FiltrationData R
  chartFiltration : FiltrationData localization.Localization
  map_filtered : ∀ {n : ℕ} {a : R},
    HasDegreeAtMost sourceFiltration n a →
      HasDegreeAtMost chartFiltration n (localization.numerator a)
  denominator : R
  denominators_eq_powers :
    localization.denominators = Submonoid.powers denominator
  denominator_mem : ∃ n : ℕ,
    HasDegreeAtMost sourceFiltration n denominator
  symbolLift : ReesTerm sourceFiltration
  symbolLift_value : symbolLift.value = denominator
  symbolLift_nonzero :
    ReesQuotient.mk symbolLift ≠ ReesQuotient.zero

namespace Data

variable (C : Data R)

private theorem denominator_mem_localization :
    C.denominator ∈ C.localization.denominators := by
  rw [C.denominators_eq_powers]
  exact Submonoid.mem_powers C.denominator

private theorem denominator_power_mem_localization (n : ℕ) :
    C.denominator ^ n ∈ C.localization.denominators := by
  rw [C.denominators_eq_powers]
  exact ⟨n, rfl⟩

private theorem power_value_of_mem
    {s : R} (hs : s ∈ C.localization.denominators) :
    ∃ n : ℕ, s = C.denominator ^ n := by
  rw [C.denominators_eq_powers] at hs
  rcases (Submonoid.mem_powers_iff s C.denominator).mp hs with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

private theorem right_clear_power (q : C.localization.Localization) :
    ∃ n : ℕ, ∃ a : R,
      q * C.localization.numerator (C.denominator ^ n) =
        C.localization.numerator a := by
  rcases C.localization.right_clear q with ⟨a, s, hs, _, hq⟩
  rcases power_value_of_mem C hs with ⟨n, rfl⟩
  exact ⟨n, a, hq⟩

private theorem right_ore_power (a : R) (n : ℕ) :
    ∃ k : ℕ, ∃ c : R,
      a * C.denominator ^ k = C.denominator ^ n * c := by
  letI : OreLocalization.OreSet
      (oppositeSubmonoid C.localization.denominators) := C.localization.ore
  let t : oppositeSubmonoid C.localization.denominators :=
    ⟨MulOpposite.op (C.denominator ^ n),
      C.denominator_power_mem_localization n⟩
  rcases OreLocalization.oreCondition (MulOpposite.op a) t with ⟨u, v, huv⟩
  rcases power_value_of_mem C v.property with ⟨k, hk⟩
  refine ⟨k, u.unop, ?_⟩
  have hu := congrArg MulOpposite.unop huv
  change a * (↑v : Rᵐᵒᵖ).unop = (↑t : Rᵐᵒᵖ).unop * u.unop at hu
  rw [hk] at hu
  simpa [t] using hu

/-- Recover the finite power-Ore certificate from the actual localization. -/
noncomputable def toPowerOre : PowerOreLocalizationCertificate R C.localization.Localization
    where
  sourceFiltration := C.sourceFiltration
  chartFiltration := C.chartFiltration
  map := C.localization.numerator
  map_filtered := C.map_filtered
  denominator := C.denominator
  denominator_mem := C.denominator_mem
  right_clearable := by
    intro q
    rcases right_clear_power C q with ⟨n, a, hq⟩
    exact ⟨n, a, by simpa [map_pow] using hq⟩
  inverse :=
    ↑((C.localization.denominator_unit
      ⟨C.denominator, C.denominator_mem_localization⟩).unit⁻¹)
  denominator_mul_inverse := by
    exact (C.localization.denominator_unit
      ⟨C.denominator, C.denominator_mem_localization⟩).mul_val_inv
  inverse_mul_denominator := by
    exact (C.localization.denominator_unit
      ⟨C.denominator, C.denominator_mem_localization⟩).val_inv_mul
  right_ore := right_ore_power C

theorem toPowerOre_map_injective : Function.Injective C.toPowerOre.map := by
  exact C.localization.numerator_injective

/-- Add the explicit Rees symbol to obtain the full-symbol certificate API. -/
noncomputable def toCertificate : FullSymbolOreCertificate.Data R C.localization.Localization where
  localization := C.toPowerOre
  symbolLift := C.symbolLift
  symbolLift_value := C.symbolLift_value
  symbolLift_nonzero := C.symbolLift_nonzero
  map_injective := C.toPowerOre_map_injective

theorem fractionEval_bijective :
    Function.Bijective (FullSymbolOreCertificate.fractionEval C.toCertificate) :=
  FullSymbolOreCertificate.fractionEval_bijective C.toCertificate

theorem finite_symbol_common_fraction_power
    (xs : List (ReesTerm C.sourceFiltration)) :
    ∃ n : Nat, ∀ x ∈ xs, ∃ a : R,
      C.localization.numerator x.value =
        C.localization.numerator a * C.toPowerOre.inverse ^ n := by
  exact FullSymbolOreCertificate.finite_symbol_common_fraction_power C.toCertificate xs

end Data

end FullSymbolRightPowerBridge

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FullSymbolRightPowerBridge.Data.toPowerOre
#print axioms SymplecticStafford.Filtered.FullSymbolRightPowerBridge.Data.toCertificate
#print axioms SymplecticStafford.Filtered.FullSymbolRightPowerBridge.Data.fractionEval_bijective
#print axioms SymplecticStafford.Filtered.FullSymbolRightPowerBridge.Data.finite_symbol_common_fraction_power
