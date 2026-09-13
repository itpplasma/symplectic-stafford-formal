import Mathlib.Tactic
import SymplecticStafford.Filtered.SymbolFractionReesLocalization

/-!
# M05: faithful module transport across the selected localization comparison

`SourceLocalizationAdapter` compares the actual selected original-Rees right
localization with the concrete Laurent-Rees subring.  The paper's M05 step
also needs a module comparison: a nonzero localized class and a strict
submodule inclusion must remain nonzero and strict after passing to the
homogeneous side, with the right action transported through the opposite-ring
map.

This file supplies exactly that faithful adapter.  Its input is an actual
additive equivalence between the two localized right modules, together with
the explicit action-compatibility equation.  The scalar action is the opposite
of the already-proved source-localization ring equivalence.  The adapter
proves nonzero survival, action compatibility, and strict-inclusion transport.

It does not assert that the Laurent-Rees subring is the paper's
`G_{Sigma_p}`, does not construct the characteristic-support prime, and does
not provide the missing filtered module/Rees-module equivalence.  Those remain
the hypotheses required to instantiate this exact adapter.
-/

namespace SymplecticStafford.Filtered

universe u v w

noncomputable section

open SymplecticStafford
open SymbolFractionRees
open SymbolFractionReesLocalization

namespace M05Luna20260912

variable {R : Type u} [Ring R]

abbrev SourceOppositeRing (C : SymbolFractionFiltration.Data R) :=
  (SymbolFractionReesLocalization.sourceLocalization C)ᵐᵒᵖ

abbrev HomogeneousOppositeRing (C : SymbolFractionFiltration.Data R) :=
  (SymbolFractionRees.ReesRing C)ᵐᵒᵖ

/-- The actual selected-denominator localization comparison supplied by the
existing source-map and clearance constructions. -/
noncomputable def sourceLocalizationEquiv
    (C : SymbolFractionFiltration.Data R) :
    SymbolFractionReesLocalization.sourceLocalization C ≃+*
      SymbolFractionRees.ReesRing C :=
  RingEquiv.ofBijective
    (SymbolFractionReesLocalization.sourceLocalizationMap C)
    (SymbolFractionReesLocalization.sourceLocalizationMap_bijective C)

/-- The exact right-module scalar map induced by the selected localization
equivalence.  The opposite is essential: the paper's modules are right
modules, represented as left modules over opposite rings. -/
noncomputable def sourceHomogeneousOppositeEquiv
    (C : SymbolFractionFiltration.Data R) :
    SourceOppositeRing C ≃+* HomogeneousOppositeRing C :=
  RingEquiv.op (sourceLocalizationEquiv C)

section ModuleTransport

variable {C : SymbolFractionFiltration.Data R}
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [AddCommGroup N]
variable [Module (SourceOppositeRing C) M]
variable [Module (HomogeneousOppositeRing C) N]

/- The paper-facing module comparison datum, with the scalar action fixed to
the actual selected source localization equivalence.  We keep the action
equation as an explicit field rather than hiding a potentially ambiguous
opposite-ring coercion inside a semilinear-map type. -/
structure FaithfulModuleComparison
    (C : SymbolFractionFiltration.Data R) (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N]
    [Module (SourceOppositeRing C) M]
    [Module (HomogeneousOppositeRing C) N] where
  toAddEquiv : M ≃+ N
  map_smul' : ∀ (r : SourceOppositeRing C) (x : M),
    toAddEquiv (r • x) = sourceHomogeneousOppositeEquiv C r • toAddEquiv x

instance : CoeFun (FaithfulModuleComparison C M N) (fun _ => M → N) :=
  ⟨fun e => e.toAddEquiv⟩

/-- The target of a source submodule under the actual semilinear module map. -/
def mapSubmodule (e : FaithfulModuleComparison (C := C) M N)
    (A : Submodule (SourceOppositeRing C) M) :
    Submodule (HomogeneousOppositeRing C) N :=
  { carrier := {y | e.toAddEquiv.symm y ∈ A}
    zero_mem' := by simpa using A.zero_mem
    add_mem' := by
      intro y z hy hz
      change e.toAddEquiv.symm (y + z) ∈ A
      rw [map_add]
      exact A.add_mem hy hz
    smul_mem' := by
      intro r y hy
      change e.toAddEquiv.symm (r • y) ∈ A
      have hreverse :
          e.toAddEquiv.symm (r • y) =
            (sourceHomogeneousOppositeEquiv C).symm r •
              e.toAddEquiv.symm y := by
        have h := congrArg e.toAddEquiv.symm
          (e.map_smul' ((sourceHomogeneousOppositeEquiv C).symm r)
            (e.toAddEquiv.symm y))
        simpa using h.symm
      rw [hreverse]
      exact A.smul_mem _ hy }

@[simp] theorem mapSubmodule_mem_iff
    (e : FaithfulModuleComparison (C := C) M N)
    (A : Submodule (SourceOppositeRing C) M) (y : N) :
    y ∈ mapSubmodule e A ↔ e.toAddEquiv.symm y ∈ A := by
  rfl

/-- Nonzero localized classes survive the faithful module comparison. -/
theorem map_ne_zero_iff
    (e : FaithfulModuleComparison (C := C) M N) (x : M) :
    e x ≠ 0 ↔ x ≠ 0 :=
  by
    constructor
    · intro h hx
      apply h
      simpa [hx]
    · intro h hx
      apply h
      apply e.toAddEquiv.injective
      simpa using hx

/-- The right action is transported with the opposite source-to-homogeneous
scalar map, not with an unrelated module instance. -/
theorem map_smul
    (e : FaithfulModuleComparison (C := C) M N)
    (r : SourceOppositeRing C) (x : M) :
    e (r • x) = sourceHomogeneousOppositeEquiv C r • e x :=
  e.map_smul' r x

private theorem map_le_iff
    (e : FaithfulModuleComparison (C := C) M N)
    {A B : Submodule (SourceOppositeRing C) M} :
    mapSubmodule e A ≤ mapSubmodule e B ↔ A ≤ B := by
  constructor
  · intro h x hx
    have hAx : e x ∈ mapSubmodule e A := by
      rw [mapSubmodule_mem_iff]
      simpa using hx
    have hBx := h hAx
    rw [mapSubmodule_mem_iff] at hBx
    simpa using hBx
  · intro h y hy
    rw [mapSubmodule_mem_iff] at hy ⊢
    exact h hy

/-- Proper source submodule inclusions remain proper after localization
transport.  This is the strictness half of the M05 filtered-chain bridge. -/
theorem map_strict_iff
    (e : FaithfulModuleComparison (C := C) M N)
    {A B : Submodule (SourceOppositeRing C) M} :
    mapSubmodule e A < mapSubmodule e B ↔ A < B := by
  constructor
  · intro h
    rw [lt_iff_le_not_ge] at h ⊢
    exact ⟨(map_le_iff e).mp h.1, by
      intro hBA
      exact h.2 ((map_le_iff e).mpr hBA)⟩
  · intro h
    rw [lt_iff_le_not_ge] at h ⊢
    exact ⟨(map_le_iff e).mpr h.1, by
      intro hBA
      exact h.2 ((map_le_iff e).mp hBA)⟩

end ModuleTransport

end M05Luna20260912

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.M05Luna20260912.mapSubmodule_mem_iff
#print axioms
  SymplecticStafford.Filtered.M05Luna20260912.map_ne_zero_iff
#print axioms
  SymplecticStafford.Filtered.M05Luna20260912.map_strict_iff
