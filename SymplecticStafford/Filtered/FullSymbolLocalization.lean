module

public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.Algebra.Ring.NonZeroDivisors

@[expose] public section

/-!
# Full algebraic symbol localization

This file uses Mathlib's actual Ore-localization object for a *saturated*
denominator set.  It is intentionally different from
`PowerOreLocalizationCertificate`: the denominator set is an arbitrary
submonoid, so no power of one chosen lift is silently substituted for the
full symbol set.

The certificate records exactly the algebraic obligations which a filtered
symbol argument has to discharge: a submonoid of regular original-ring
elements and an Ore structure on that submonoid.  The resulting localization
is the quotient of original-ring numerator/denominator pairs supplied by
Mathlib.  We expose its exact fraction equality, expansion, Ore witnesses and
injective original-ring map.  No completion, principal-open argument, or
Noetherianity inference is made here.
-/

namespace SymplecticStafford.Filtered

universe u

namespace FullSymbolLocalization

variable {R : Type u} [Ring R]

/-! A saturated algebraic symbol set in the original ring. -/
structure Data (R : Type u) [Ring R] where
  denominators : Submonoid R
  /-- The symbol set consists of regular elements of the original ring. -/
  regular : denominators ≤ nonZeroDivisorsLeft R
  /-- The full symbol set satisfies the (left-oriented) Ore equations. -/
  ore : OreLocalization.OreSet denominators

namespace Data

variable (C : Data R)

/- The explicit instance argument keeps the certificate's Ore structure
  attached to every definition; a global, unrelated `OreSet` instance is
  never selected by elaboration. -/
abbrev Localization : Type u :=
  @OreLocalization R (inferInstance : Monoid R) C.denominators C.ore R
    (inferInstance : MulAction R R)

def numerator : R →* C.Localization :=
  @OreLocalization.numeratorHom R (inferInstance : Monoid R)
    C.denominators C.ore

def fraction (a : R) (s : C.denominators) : C.Localization :=
  @OreLocalization.oreDiv R (inferInstance : Monoid R)
    C.denominators C.ore R (inferInstance : MulAction R R) a s

theorem numerator_injective : Function.Injective C.numerator := by
  exact @OreLocalization.numeratorHom_inj R _ C.denominators C.ore C.regular

theorem fraction_eq_iff {a b : R} {s t : C.denominators} :
    C.fraction a s = C.fraction b t ↔
      ∃ u : C.denominators, ∃ v : R,
        (u : R) * b = v * a ∧
          (u : R) * (t : R) = v * (s : R) := by
  exact @OreLocalization.oreDiv_eq_iff R _ C.denominators C.ore R _ a b s t

theorem fraction_expand (a : R) (s t : C.denominators) :
    C.fraction a s = C.fraction ((t : R) * a) (t * s) := by
  letI : OreLocalization.OreSet C.denominators := C.ore
  exact @OreLocalization.expand' R _ C.denominators C.ore R _ a s t

theorem exists_fraction (x : C.Localization) :
    ∃ (a : R) (s : C.denominators), x = C.fraction a s := by
  induction x using @OreLocalization.ind R _ C.denominators C.ore R _ with
  | _ a s => exact ⟨a, s, rfl⟩

theorem ore_witness (a : R) (s : C.denominators) :
    ∃ (b : R) (t : C.denominators),
      (t : R) * a = b * (s : R) := by
  letI : OreLocalization.OreSet C.denominators := C.ore
  exact ⟨OreLocalization.oreNum a s, OreLocalization.oreDenom a s,
    OreLocalization.ore_eq a s⟩

/- Every denominator is an actual unit in the algebraic localization.  The
  two displayed products retain the order of the Ore construction. -/
theorem denominator_unit (s : C.denominators) :
    IsUnit (C.fraction (s : R) (1 : C.denominators)) := by
  exact (@OreLocalization.numeratorUnit R (inferInstance : Monoid R)
    C.denominators C.ore s).isUnit

theorem localization_nontrivial [Nontrivial R] :
    Nontrivial C.Localization := by
  letI : OreLocalization.OreSet C.denominators := C.ore
  exact OreLocalization.nontrivial_of_nonZeroDivisorsLeft C.regular

end Data

end FullSymbolLocalization

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FullSymbolLocalization.Data.numerator_injective
#print axioms SymplecticStafford.Filtered.FullSymbolLocalization.Data.fraction_eq_iff
#print axioms SymplecticStafford.Filtered.FullSymbolLocalization.Data.fraction_expand
#print axioms SymplecticStafford.Filtered.FullSymbolLocalization.Data.exists_fraction
#print axioms SymplecticStafford.Filtered.FullSymbolLocalization.Data.ore_witness
#print axioms SymplecticStafford.Filtered.FullSymbolLocalization.Data.denominator_unit
#print axioms SymplecticStafford.Filtered.FullSymbolLocalization.Data.localization_nontrivial
