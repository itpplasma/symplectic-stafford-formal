import Mathlib.Tactic
import SymplecticStafford.Filtered.FiniteFilteredStrictMap

/-!
# Independent oracle for the bounded strict filtered-map witness

The concrete filtration is `ℚ² ⊃ ℚ × 0 ⊃ 0`.  Its proper intermediate
submodule has an explicit nonzero zeroth ambient-layer class, represented by
`(0, 1)`.  The oracle proves directly that this class is missed by the
zeroth associated-layer map, and separately consumes the generic witness and
both finite length equations.
-/

namespace SymplecticStafford.Filtered.FiniteFilteredStrictMapOracle

noncomputable section

open SymplecticStafford.Filtered
open FiniteFilteredStrictMap

def axis : Submodule ℚ (ℚ × ℚ) where
  carrier := {x | x.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp [hx, hy]
  smul_mem' := by
    intro c x hx
    simp [hx]

def planeFiltration : FiniteFilteredModule (R := ℚ) (M := ℚ × ℚ) where
  height := 2
  carrier := fun n => if n = 0 then ⊤ else if n = 1 then axis else ⊥
  exhaustive := by simp
  descending := by
    intro n
    by_cases hzero : n = 0
    · subst n
      simp [axis]
    · by_cases hone : n = 1
      · subst n
        simp [axis]
      · have hsucc_zero : n + 1 ≠ 0 := by omega
        have hsucc_one : n + 1 ≠ 1 := by omega
        simp [hzero, hone, hsucc_zero, hsucc_one]
  separated := by simp

theorem axis_proper : axis < (⊤ : Submodule ℚ (ℚ × ℚ)) := by
  apply lt_of_le_of_ne le_top
  intro htop
  have hbad : ((0, 1) : ℚ × ℚ) ∈ axis := by
    rw [htop]
    trivial
  simpa [axis] using hbad

theorem zeroth_layer_has_unlifted_class :
    ∃ q : filteredLayerQuotient planeFiltration ⟨0, by decide⟩, q ≠ 0 := by
  let q : filteredLayerQuotient planeFiltration ⟨0, by decide⟩ :=
    Submodule.Quotient.mk
      (p := filteredLayerSubmodule planeFiltration ⟨0, by decide⟩)
      ⟨(0, 1), by simp [planeFiltration]⟩
  refine ⟨q, ?_⟩
  intro hq
  have hq' :
      Submodule.mkQ (filteredLayerSubmodule planeFiltration ⟨0, by decide⟩)
          ⟨(0, 1), by simp [planeFiltration]⟩ = 0 := by
    simpa [q] using hq
  have hmem : ((0, 1) : ℚ × ℚ) ∈ planeFiltration.carrier 1 := by
    apply (filteredLayerQuotient_mk_eq_zero_iff_mem
      planeFiltration ⟨0, by decide⟩).mp
    exact hq'
  simpa [planeFiltration, axis] using hmem

theorem zeroth_layer_map_misses_explicit_class :
    ∃ q : filteredLayerQuotient planeFiltration ⟨0, by decide⟩,
      q ≠ 0 ∧
        ∀ p : filteredLayerQuotient
            (inducedFiltration planeFiltration axis) ⟨0, by decide⟩,
          layerMap planeFiltration axis ⟨0, by decide⟩ p ≠ q := by
  let k : Fin planeFiltration.height := ⟨0, by decide⟩
  let x₀ : planeFiltration.carrier k.1 :=
    ⟨(0, 1), by simp [k, planeFiltration]⟩
  let q : filteredLayerQuotient planeFiltration k :=
    Submodule.Quotient.mk
      (p := filteredLayerSubmodule planeFiltration k) x₀
  have hq_ne_zero : q ≠ 0 := by
    intro hq
    have hq' :
        Submodule.mkQ (filteredLayerSubmodule planeFiltration k) x₀ = 0 := by
      simpa [q] using hq
    have hmem : (x₀ : ℚ × ℚ) ∈ planeFiltration.carrier (k.1 + 1) :=
      (filteredLayerQuotient_mk_eq_zero_iff_mem planeFiltration k x₀).mp hq'
    simpa [k, planeFiltration, axis, x₀] using hmem
  refine ⟨q, hq_ne_zero, ?_⟩
  intro p
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  have hxnext :
      ((x : (inducedFiltration planeFiltration axis).carrier k.1) : ℚ × ℚ)
        ∈ planeFiltration.carrier (k.1 + 1) := by
    simpa [k, planeFiltration, axis] using x.1.property
  have hzero :
      layerMap planeFiltration axis k
        (Submodule.Quotient.mk
          (p := filteredLayerSubmodule
            (inducedFiltration planeFiltration axis) k) x) = 0 := by
    rw [layerMap_mk]
    exact (filteredLayerQuotient_mk_eq_zero_iff_mem planeFiltration k _).mpr
      hxnext
  intro hq
  apply hq_ne_zero
  rw [← hq]
  exact hzero

theorem concrete_witness :
    Nonempty (Witness planeFiltration axis axis_proper) :=
  exists_witness planeFiltration axis axis_proper

theorem witness_retains_exact_length_formulas :
    ∃ W : Witness planeFiltration axis axis_proper,
      Module.length ℚ (ℚ × ℚ) =
          ∑ k ∈ Finset.Ico 0 planeFiltration.height,
            planeFiltration.layerLength k ∧
        Module.length ℚ axis =
          ∑ k ∈ Finset.Ico 0 planeFiltration.height,
            (inducedFiltration planeFiltration axis).layerLength k := by
  rcases concrete_witness with ⟨W⟩
  exact ⟨W, W.ambient_length, W.induced_length⟩

end

end SymplecticStafford.Filtered.FiniteFilteredStrictMapOracle

#print axioms
  SymplecticStafford.Filtered.FiniteFilteredStrictMapOracle.zeroth_layer_has_unlifted_class
#print axioms
  SymplecticStafford.Filtered.FiniteFilteredStrictMapOracle.zeroth_layer_map_misses_explicit_class
#print axioms
  SymplecticStafford.Filtered.FiniteFilteredStrictMapOracle.concrete_witness
#print axioms
  SymplecticStafford.Filtered.FiniteFilteredStrictMapOracle.witness_retains_exact_length_formulas
