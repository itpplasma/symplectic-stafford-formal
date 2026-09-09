import SymplecticStafford.Filtered.FullSymbolRightLocalization

/-!
# Finite common denominators for right-localized modules

This is the module-level companion to `FullSymbolRightLocalization`.  It uses
the actual Ore localization of the opposite ring, while exposing a
right-sided fraction whose denominator is an element of the original ring.
The finite common-denominator result is unconditional once the chosen full
symbol set has supplied its genuine Ore certificate.  In particular, it does
not replace that certificate by powers of one symbol or by a completion.
-/

namespace SymplecticStafford.Filtered

universe u v

namespace FullSymbolRightModuleLocalization

open AlgebraicAnalysis.OreRightLocalization

variable {R : Type u} [Ring R]
variable (C : FullSymbolRightLocalization.Data R)
variable {M : Type v} [AddCommMonoid M] [Module Rᵐᵒᵖ M]

/-- The module localized at the opposite presentation of the original
right-denominator set. -/
abbrev ModuleLocalization (M : Type v) [AddCommMonoid M]
    [Module Rᵐᵒᵖ M] : Type (max u v) :=
  @OreLocalization Rᵐᵒᵖ (inferInstance : Monoid Rᵐᵒᵖ)
    (oppositeSubmonoid C.denominators) C.ore M
    (inferInstance : MulAction Rᵐᵒᵖ M)

/-- A fraction in the opposite Ore presentation. -/
def moduleFraction (m : M) (s : oppositeSubmonoid C.denominators) :
    ModuleLocalization C M :=
  @OreLocalization.oreDiv Rᵐᵒᵖ _ (oppositeSubmonoid C.denominators) C.ore M _ m s

/-- The same fraction, with its denominator displayed in the original ring. -/
def rightModuleFraction (m : M) (s : C.denominators) :
    ModuleLocalization C M :=
  moduleFraction C m
    (⟨MulOpposite.op (s : R), s.property⟩ : oppositeSubmonoid C.denominators)

private theorem common_aux (qs : List (ModuleLocalization C M)) :
    ∃ s : oppositeSubmonoid C.denominators, ∀ q ∈ qs, ∃ m : M,
      q = moduleFraction C m s := by
  letI : OreLocalization.OreSet (oppositeSubmonoid C.denominators) := C.ore
  induction qs with
  | nil =>
      refine ⟨1, ?_⟩
      simp [moduleFraction]
  | cons q qs ih =>
      rcases ih with ⟨s, hs⟩
      induction q using @OreLocalization.ind Rᵐᵒᵖ _
        (oppositeSubmonoid C.denominators) C.ore M _ with
      | _ m t =>
        rcases OreLocalization.oreCondition (s : Rᵐᵒᵖ) t with ⟨v, u, huv⟩
        refine ⟨u * s, ?_⟩
        intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq'
        · refine ⟨v • m, ?_⟩
          apply OreLocalization.oreDiv_eq_iff.mpr
          refine ⟨1, v, ?_, ?_⟩
          · simp
          · simpa using huv
        · rcases hs q' hq' with ⟨n, hn⟩
          refine ⟨(u : Rᵐᵒᵖ) • n, ?_⟩
          rw [hn]
          apply OreLocalization.oreDiv_eq_iff.mpr
          refine ⟨1, u, ?_, ?_⟩
          · simp
          · simp

theorem common_module_fraction (qs : List (ModuleLocalization C M)) :
    ∃ s : oppositeSubmonoid C.denominators, ∀ q ∈ qs, ∃ m : M,
      q = moduleFraction C m s :=
  common_aux C qs

theorem common_right_module_fraction (qs : List (ModuleLocalization C M)) :
    ∃ s : C.denominators, ∀ q ∈ qs, ∃ m : M,
      q = rightModuleFraction C m s := by
  rcases common_module_fraction C qs with ⟨t, ht⟩
  let s : C.denominators := ⟨(t : Rᵐᵒᵖ).unop, t.property⟩
  refine ⟨s, ?_⟩
  intro q hq
  rcases ht q hq with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  simpa [rightModuleFraction, moduleFraction, s] using hm

end FullSymbolRightModuleLocalization

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FullSymbolRightModuleLocalization.common_module_fraction
#print axioms SymplecticStafford.Filtered.FullSymbolRightModuleLocalization.common_right_module_fraction
