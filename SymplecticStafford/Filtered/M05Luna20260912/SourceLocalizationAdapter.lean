module

public import Mathlib.Tactic
public import SymplecticStafford.Filtered.SymbolFractionReesLocalization

@[expose] public section

/-!
# M05: the exact selected-source localization adapter

This file is deliberately disjoint from the draft source-map and localization
files. Those files already prove an injective and surjective map from the
actual right Ore localization of the original bounded Rees ring (at the
selected homogeneous source denominators) to the Laurent fraction Rees
subring. The adapter below turns that pair of facts into a reusable
RingEquiv and exposes the corresponding fraction formula.

This is the strongest comparison justified by the current definitions. It
does not identify this selected source localization with the paper's
homogeneous localization at a characteristic-support prime, does not construct
the corresponding localized module, and does not transfer a filtered length
bound. The first missing M05 hypothesis is therefore an actual filtered
algebra/module comparison (including strictness or faithful homogeneous
survival) between those paper objects and this selected localization.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

open SymplecticStafford
open SymbolFractionRees
open SymbolFractionReesMap
open SymbolFractionReesLocalization

namespace M05Luna20260912

variable {R : Type u} [Ring R]

/-- The actual selected-denominator localization comparison supplied by the
existing source-map and clearance constructions. -/
noncomputable def sourceLocalizationEquiv
    (C : SymbolFractionFiltration.Data R) :
    SymbolFractionReesLocalization.sourceLocalization C ≃+*
      SymbolFractionRees.ReesRing C :=
  RingEquiv.ofBijective
    (SymbolFractionReesLocalization.sourceLocalizationMap C)
    (SymbolFractionReesLocalization.sourceLocalizationMap_bijective C)

@[simp] theorem sourceLocalizationEquiv_apply
    (C : SymbolFractionFiltration.Data R)
    (x : SymbolFractionReesLocalization.sourceLocalization C) :
    sourceLocalizationEquiv C x =
      SymbolFractionReesLocalization.sourceLocalizationMap C x := rfl

/-- Every denominator in the actual source submonoid maps to a unit in the
Laurent Rees subring. This is the unit fact needed to turn right clearing into
an explicit homogeneous-localization fraction formula. -/
theorem sourceDenominator_map_isUnit
    (C : SymbolFractionFiltration.Data R)
    (s : SymbolFractionReesLocalization.sourceDenominators C) :
    IsUnit (SymbolFractionReesMap.map C
      (s : SymbolFractionReesMap.SourceReesRing C)) := by
  rcases s.property with ⟨s₀, _hs₀, hs₀⟩
  have hs₀' : (s : SymbolFractionReesMap.SourceReesRing C) =
      SymbolFractionReesMap.sourceHomogeneousDenominator C s₀ := hs₀.symm
  rw [hs₀', SymbolFractionReesMap.map_sourceHomogeneousDenominator]
  exact SymbolFractionRees.homogeneousDenominator_isUnit C s₀

/-- The equivalence commutes with the actual original-Rees numerator map. -/
theorem sourceLocalizationEquiv_commutes
    (C : SymbolFractionFiltration.Data R)
    (a : SymbolFractionReesMap.SourceReesRing C) :
    sourceLocalizationEquiv C
        (SymbolFractionReesLocalization.sourceNumerator C a) =
      SymbolFractionReesMap.map C a := by
  exact SymbolFractionReesLocalization.sourceLocalizationMap_commutes C a

/-- Explicit image of an actual source fraction. The denominator is a member
of the selected source submonoid, not an abstract or conditional denominator.
This is the degree-controlled localization interface consumed by the next M05
step. -/
theorem sourceLocalizationEquiv_sourceFraction
    (C : SymbolFractionFiltration.Data R)
    (a : SymbolFractionReesMap.SourceReesRing C)
    (s : SymbolFractionReesLocalization.sourceDenominators C) :
    sourceLocalizationEquiv C
        (SymbolFractionReesLocalization.sourceFraction C a s) =
      SymbolFractionReesMap.map C a *
        ((IsUnit.unit (sourceDenominator_map_isUnit C s)).inv :
          SymbolFractionRees.ReesRing C) := by
  let u : Units (SymbolFractionRees.ReesRing C) :=
    IsUnit.unit (sourceDenominator_map_isUnit C s)
  have hu : (u : SymbolFractionRees.ReesRing C) =
      SymbolFractionReesMap.map C
        (s : SymbolFractionReesMap.SourceReesRing C) :=
    IsUnit.unit_spec (sourceDenominator_map_isUnit C s)
  have hclear :=
    SymbolFractionReesLocalization.sourceLocalizationMap_fraction_clear C a s
  change sourceLocalizationEquiv C
      (SymbolFractionReesLocalization.sourceFraction C a s) *
        SymbolFractionReesMap.map C
          (s : SymbolFractionReesMap.SourceReesRing C) =
      SymbolFractionReesMap.map C a at hclear
  change sourceLocalizationEquiv C
      (SymbolFractionReesLocalization.sourceFraction C a s) =
      SymbolFractionReesMap.map C a * (u.inv : SymbolFractionRees.ReesRing C)
  calc
    sourceLocalizationEquiv C
        (SymbolFractionReesLocalization.sourceFraction C a s) =
        sourceLocalizationEquiv C
          (SymbolFractionReesLocalization.sourceFraction C a s) * 1 :=
      (mul_one
        (sourceLocalizationEquiv C
          (SymbolFractionReesLocalization.sourceFraction C a s))).symm
    _ = sourceLocalizationEquiv C
          (SymbolFractionReesLocalization.sourceFraction C a s) *
          ((u : SymbolFractionRees.ReesRing C) *
            (u.inv : SymbolFractionRees.ReesRing C)) := by
      rw [u.val_inv]
    _ = (sourceLocalizationEquiv C
          (SymbolFractionReesLocalization.sourceFraction C a s) *
          (u : SymbolFractionRees.ReesRing C)) *
          (u.inv : SymbolFractionRees.ReesRing C) := by
      rw [mul_assoc]
    _ = (sourceLocalizationEquiv C
          (SymbolFractionReesLocalization.sourceFraction C a s) *
          SymbolFractionReesMap.map C
            (s : SymbolFractionReesMap.SourceReesRing C)) *
          (u.inv : SymbolFractionRees.ReesRing C) := by
      rw [hu]
    _ = SymbolFractionReesMap.map C a *
          (u.inv : SymbolFractionRees.ReesRing C) := by
      rw [hclear]

end M05Luna20260912

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.M05Luna20260912.sourceLocalizationEquiv
#print axioms
  SymplecticStafford.Filtered.M05Luna20260912.sourceDenominator_map_isUnit
#print axioms
  SymplecticStafford.Filtered.M05Luna20260912.sourceLocalizationEquiv_sourceFraction
