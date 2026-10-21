module

public import AlgebraicAnalysis.Ore.RightLocalization
public import Mathlib.Algebra.Ring.NonZeroDivisors

@[expose] public section

/-!
# Full-symbol localization with original right denominators

The paper's source assembly is right-sided.  Mathlib's Ore localization is
left-oriented, so the algebraic-analysis package implements the right-sided
construction by passing to the opposite ring.  This file gives the filtered
lane a precise certificate for that construction.

`RightData.denominators` is an arbitrary saturated submonoid of the original
ring, not the powers of a selected lift.  Its `ore` field is an actual Ore
structure on the opposite submonoid.  The exported results provide the
injective original-ring map and the exact right-denominator clearing theorem
in the original localization.  The certificate is therefore suitable for a
future characteristic-symbol producer, while its Ore and regularity fields
remain explicit obligations of that producer.  No completion, principal
power shortcut, or Noetherianity claim is made.
-/

namespace SymplecticStafford.Filtered

universe u

namespace FullSymbolRightLocalization

variable {R : Type u} [Ring R]

structure Data (R : Type u) [Ring R] where
  denominators : Submonoid R
  /-- Right regularity of every original-ring denominator. -/
  regular : denominators ≤ nonZeroDivisorsRight R
  /-- The opposite denominator set has the genuine Ore equations. -/
  ore : OreLocalization.OreSet
    (AlgebraicAnalysis.OreRightLocalization.oppositeSubmonoid denominators)

namespace Data

open AlgebraicAnalysis.OreRightLocalization

variable (C : Data R)

abbrev Localization : Type u :=
  @RightOreLocalization R (inferInstance : Ring R) C.denominators C.ore

def numerator : R →+* C.Localization :=
  @rightNumeratorRingHom R (inferInstance : Ring R) C.denominators C.ore

theorem regular_opposite :
    oppositeSubmonoid C.denominators ≤ nonZeroDivisorsLeft Rᵐᵒᵖ := by
  intro s hs y hsy
  apply MulOpposite.unop_injective
  apply C.regular hs
  simpa only [MulOpposite.unop_mul, MulOpposite.unop_zero] using
    congrArg MulOpposite.unop hsy

theorem numerator_injective : Function.Injective C.numerator := by
  intro a b hab
  letI : OreLocalization.OreSet (oppositeSubmonoid C.denominators) := C.ore
  apply MulOpposite.op_injective
  apply OreLocalization.numeratorHom_inj C.regular_opposite
  exact congrArg MulOpposite.unop hab

/- Every right-localized element has one denominator in the original
  submonoid which clears it on the RIGHT. -/
theorem right_clear (q : C.Localization) :
    ∃ a s : R, s ∈ C.denominators ∧ IsUnit (C.numerator s) ∧
      q * C.numerator s = C.numerator a := by
  letI : OreLocalization.OreSet (oppositeSubmonoid C.denominators) := C.ore
  exact rightOre_clear q

theorem denominator_unit (s : C.denominators) :
    IsUnit (C.numerator (s : R)) := by
  letI : OreLocalization.OreSet (oppositeSubmonoid C.denominators) := C.ore
  exact isUnit_op.mpr (OreLocalization.numerator_isUnit
    (R := Rᵐᵒᵖ) (S := oppositeSubmonoid C.denominators)
      (⟨MulOpposite.op (s : R), s.property⟩ : oppositeSubmonoid C.denominators))

private theorem right_ore_common
    (a : R) (s : C.denominators) :
    ∃ t : C.denominators, ∃ c : R,
      a * (t : R) = (s : R) * c := by
  letI : OreLocalization.OreSet (oppositeSubmonoid C.denominators) := C.ore
  let s' : oppositeSubmonoid C.denominators :=
    ⟨MulOpposite.op (s : R), s.property⟩
  rcases OreLocalization.oreCondition (MulOpposite.op a) s' with
    ⟨c', t', ht⟩
  refine ⟨⟨(t' : Rᵐᵒᵖ).unop, t'.property⟩,
    (c' : Rᵐᵒᵖ).unop, ?_⟩
  have hu := congrArg MulOpposite.unop ht
  change a * (t' : Rᵐᵒᵖ).unop = (s : R) *
    (c' : Rᵐᵒᵖ).unop at hu
  exact hu

/- A finite family of localized ring elements admits one denominator from the
   original submonoid.  The numerator is always multiplied on the RIGHT:
   `q * numerator s = numerator a`.  The Ore step in the induction is what
   makes a denominator common to an element already cleared by `s` and an
   element cleared by a different denominator `t`; no commutativity is used. -/
theorem common_right_clear (qs : List C.Localization) :
    ∃ s : C.denominators, ∀ q ∈ qs, ∃ a : R,
      q * C.numerator (s : R) = C.numerator a := by
  induction qs with
  | nil =>
      refine ⟨1, ?_⟩
      simp
  | cons q qs ih =>
      rcases C.right_clear q with ⟨a, t, ht, _, hq⟩
      rcases ih with ⟨s, hs⟩
      rcases right_ore_common C t s with ⟨u, c, hts⟩
      let common : C.denominators :=
        ⟨t * (u : R), C.denominators.mul_mem ht u.property⟩
      refine ⟨common, ?_⟩
      intro q' hq'
      rcases List.mem_cons.mp hq' with hqeq | hqs
      · subst q'
        refine ⟨a * (u : R), ?_⟩
        calc
          q * C.numerator (common : R) =
              (q * C.numerator (t : R)) * C.numerator (u : R) := by
                rw [show (common : R) =
                    (t : R) * (u : R) by rfl, map_mul]
                simp only [mul_assoc]
          _ = C.numerator a * C.numerator (u : R) := by rw [hq]
          _ = C.numerator (a * (u : R)) := by rw [map_mul]
      · rcases hs q' hqs with ⟨b, hb⟩
        refine ⟨b * c, ?_⟩
        calc
          q' * C.numerator (common : R) =
              q' * C.numerator ((s * c : R)) := by
                rw [show (common : R) =
                    (s : R) * c by exact hts]
          _ = (q' * C.numerator (s : R)) * C.numerator c := by
                rw [map_mul]
                simp only [mul_assoc]
          _ = C.numerator b * C.numerator c := by rw [hb]
          _ = C.numerator (b * c) := by rw [map_mul]

end Data

end FullSymbolRightLocalization

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FullSymbolRightLocalization.Data.regular_opposite
#print axioms SymplecticStafford.Filtered.FullSymbolRightLocalization.Data.numerator_injective
#print axioms SymplecticStafford.Filtered.FullSymbolRightLocalization.Data.right_clear
#print axioms SymplecticStafford.Filtered.FullSymbolRightLocalization.Data.denominator_unit
#print axioms SymplecticStafford.Filtered.FullSymbolRightLocalization.Data.common_right_clear
