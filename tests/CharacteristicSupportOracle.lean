module

public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Filtered.CharacteristicSupport

@[expose] public section

/-!
# Independent characteristic-support oracle

The two-layer integer filtration has one nonzero associated quotient layer.
The oracle checks both the concrete support witness and the derived
`WithBot Nat` zero/nonzero boundary, rather than restating the theorem as a
field of a support datum.
-/

namespace SymplecticStafford.Filtered.CharacteristicSupportOracle

open FiniteFilteredModule

def scalarFiltration : FiniteFilteredModule (R := ℤ) (M := ℤ) where
  height := 2
  carrier := fun k => if k = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  separated := by simp

example : (⟨0, by decide⟩ : Fin scalarFiltration.height) ∈
    scalarFiltration.QuotientSupport := by
  refine ⟨7, ?_, ?_⟩
  · simp [scalarFiltration]
  intro hzero
  have hmk :
      (Submodule.Quotient.mk (7 : ℤ) :
        ℤ ⧸ scalarFiltration.carrier (0 + 1)) = 0 := by
    simpa only [Submodule.mkQ_apply] using hzero
  have hmem : (7 : ℤ) ∈ scalarFiltration.carrier (0 + 1) :=
    (Submodule.Quotient.mk_eq_zero
      (scalarFiltration.carrier (0 + 1))).mp hmk
  norm_num [scalarFiltration] at hmem

example : scalarFiltration.QuotientSupport.Nonempty := by
  apply scalarFiltration.quotientSupport_nonempty_of_exists_ne_zero
  exact ⟨7, by norm_num⟩

example : scalarFiltration.QuotientSupportDimension ≠
    (⊥ : SupportDimension) := by
  exact scalarFiltration.quotientSupportDimension_ne_bot_of_quotient_nonzero
    (x := (7 : ℤ)) (by norm_num)

example : scalarFiltration.CharacteristicSupportDimension ≠
    (⊥ : SupportDimension) := by
  exact scalarFiltration.quotientSupportDimension_ne_bot_of_quotient_nonzero
    (x := (7 : ℤ)) (by norm_num)

example : ∃ k : Fin scalarFiltration.height, ∃ x : ℤ,
    x ∈ scalarFiltration.carrier k.1 ∧
      Submodule.mkQ (scalarFiltration.carrier (k.1 + 1)) x ≠ 0 := by
  apply scalarFiltration.exists_nonzero_quotient_of_quotientSupportDimension_ne_bot
  exact scalarFiltration.quotientSupportDimension_ne_bot_of_quotient_nonzero
    (x := (7 : ℤ)) (by norm_num)

example : ¬ (scalarFiltration.QuotientSupportDimension =
    (⊥ : SupportDimension)) := by
  exact scalarFiltration.quotientSupportDimension_ne_bot_of_quotient_nonzero
    (x := (7 : ℤ)) (by norm_num)

def zeroFiltration : FiniteFilteredModule (R := ℤ) (M := PUnit) where
  height := 1
  carrier := fun _ => ⊥
  exhaustive := by
    apply le_antisymm
    · exact bot_le
    · intro x hx
      exact (Submodule.mem_bot ℤ).2 (Subsingleton.elim x 0)
  descending := by
    intro k
    exact le_rfl
  separated := by
    rfl

example : zeroFiltration.QuotientSupport = ∅ := by
  exact zeroFiltration.quotientSupport_empty_iff_zero.mpr (by simp)

example : zeroFiltration.QuotientSupportDimension =
    (⊥ : SupportDimension) := by
  exact zeroFiltration.quotientSupportDimension_bot_iff_zero.mpr (by simp)

example : ∀ x : PUnit, x = 0 := by simp

end SymplecticStafford.Filtered.CharacteristicSupportOracle

#print axioms SymplecticStafford.Filtered.CharacteristicSupportOracle.scalarFiltration
#print axioms SymplecticStafford.Filtered.CharacteristicSupportOracle.zeroFiltration
