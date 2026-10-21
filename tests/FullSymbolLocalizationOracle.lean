module

public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Filtered.FullSymbolLocalization

@[expose] public section

/- Independent consumer for the full-symbol localization boundary.  The
  denominator set is the whole submonoid of powers of `2`; no single chosen
  power is used by the API. -/
namespace SymplecticStaffordTest.FullSymbolLocalization

open SymplecticStafford.Filtered

def powersData : FullSymbolLocalization.Data ℚ where
  denominators := Submonoid.powers (2 : ℚ)
  regular := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simp
  ore := inferInstance

example : Function.Injective powersData.numerator :=
  powersData.numerator_injective

example (a b : ℚ) (s t : powersData.denominators) :
    powersData.fraction a s = powersData.fraction b t ↔
      ∃ u : powersData.denominators, ∃ v : ℚ,
        (u : ℚ) * b = v * a ∧
          (u : ℚ) * (t : ℚ) = v * (s : ℚ) :=
  powersData.fraction_eq_iff

example (x : powersData.Localization) :
    ∃ (a : ℚ) (s : powersData.denominators),
      x = powersData.fraction a s :=
  powersData.exists_fraction x

example (a : ℚ) (s t : powersData.denominators) :
    powersData.fraction a s =
      powersData.fraction ((t : ℚ) * a) (t * s) :=
  powersData.fraction_expand a s t

example (a : ℚ) (s : powersData.denominators) :
    ∃ (b : ℚ) (t : powersData.denominators),
      (t : ℚ) * a = b * (s : ℚ) :=
  powersData.ore_witness a s

example (s : powersData.denominators) :
    IsUnit (powersData.fraction (s : ℚ) (1 : powersData.denominators)) :=
  powersData.denominator_unit s

example : Nontrivial powersData.Localization :=
  powersData.localization_nontrivial

end SymplecticStaffordTest.FullSymbolLocalization
