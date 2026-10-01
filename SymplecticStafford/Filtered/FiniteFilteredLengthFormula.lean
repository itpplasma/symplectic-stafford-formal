import Mathlib.RingTheory.Length
import Mathlib.Tactic
import SymplecticStafford.Filtered.ActualClassSupport

/-!
# Exact length accounting for a finite filtered module

For a genuine finite descending filtration by submodules, the length of every
filtered carrier is the sum of the lengths of the actual successive quotient
layers above it.  The proof uses the literal quotient sequence at each step;
it does not introduce a graded proxy or assume that a filtered quotient is
already identified with a localized associated-graded module.

This is the bounded filtered part of the M05 length bridge.  It supplies the
exact finite-chain accounting a future homogeneous-localization construction
can consume, but it does not construct that localization or the comparison
with the paper's noncommutative module.
-/

namespace SymplecticStafford.Filtered

universe u v

noncomputable section

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

namespace FiniteFilteredModule

variable (F : FiniteFilteredModule (R := R) (M := M))

/- The value is zero outside the finite range, so the carrier formula can be
   stated for every natural starting index without carrying a proof that the
   index is below the height. -/
def layerLength (n : ℕ) : ℕ∞ :=
  if hn : n < F.height then
    Module.length R (filteredLayerQuotient F ⟨n, hn⟩)
  else 0

theorem layerLength_of_lt {n : ℕ} (hn : n < F.height) :
    F.layerLength n =
      Module.length R (filteredLayerQuotient F ⟨n, hn⟩) := by
  simp [layerLength, hn]

/- The actual submodule in the next layer is linearly equivalent to the next
   filtered carrier.  This is the carrier-level bridge used in the induction
   below; no quotient or graded identification is supplied. -/
private def nextCarrierEquiv {n : ℕ} (hn : n < F.height) :
    filteredLayerSubmodule F ⟨n, hn⟩ ≃ₗ[R] F.carrier (n + 1) :=
  { toFun := fun x => ⟨x.1.1, x.2⟩
    invFun := fun y =>
      ⟨⟨y.1, F.descending n y.2⟩, y.2⟩
    left_inv := by
      intro x
      rfl
    right_inv := by
      intro y
      rfl
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro c x
      rfl }

private theorem carrier_length_step {n : ℕ} (hn : n < F.height) :
    Module.length R (F.carrier n) =
      Module.length R (F.carrier (n + 1)) +
        Module.length R (filteredLayerQuotient F ⟨n, hn⟩) := by
  let k : Fin F.height := ⟨n, hn⟩
  have hExact :
      Module.length R (F.carrier n) =
        Module.length R (filteredLayerSubmodule F k) +
          Module.length R (filteredLayerQuotient F k) :=
    Module.length_eq_add_of_exact
      (filteredLayerSubmodule F k).subtype
      (filteredLayerSubmodule F k).mkQ
      (Submodule.subtype_injective _)
      (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  have hnext := (nextCarrierEquiv F hn).length_eq
  simpa [k] using hExact.trans
    (congrArg (fun x => x + Module.length R (filteredLayerQuotient F k))
      hnext)

/-- Length of a real filtered carrier is the sum of its remaining actual
successive layer lengths.  The summation index is `Finset.Ico n F.height`,
so every quotient in the statement is a real layer of `F`. -/
theorem length_carrier_eq_sum_layerLength :
    ∀ n, n ≤ F.height →
      Module.length R (F.carrier n) =
        ∑ k ∈ Finset.Ico n F.height, F.layerLength k := by
  intro n
  induction hmeasure : F.height - n using Nat.strong_induction_on generalizing n with
  | h d ih =>
      intro hnle
      by_cases htop : n = F.height
      · subst n
        rw [F.separated]
        simp
      · have hnlt : n < F.height := lt_of_le_of_ne hnle htop
        have hnext :
            Module.length R (F.carrier (n + 1)) =
              ∑ k ∈ Finset.Ico (n + 1) F.height, F.layerLength k := by
          apply ih (F.height - (n + 1))
          · omega
          · rfl
          · omega
        calc
          Module.length R (F.carrier n) =
              Module.length R (F.carrier (n + 1)) +
                Module.length R (filteredLayerQuotient F ⟨n, hnlt⟩) :=
            carrier_length_step F hnlt
          _ =
              (∑ k ∈ Finset.Ico (n + 1) F.height, F.layerLength k) +
                F.layerLength n := by
            rw [hnext, F.layerLength_of_lt hnlt]
          _ = F.layerLength n +
              ∑ k ∈ Finset.Ico (n + 1) F.height, F.layerLength k := by
            exact add_comm _ _
          _ = ∑ k ∈ Finset.Ico n F.height, F.layerLength k := by
            rw [← Finset.insert_Ico_add_one_left_eq_Ico hnlt]
            rw [Finset.sum_insert (by simp)]

/-- The finite filtered module itself is obtained by summing all its actual
successive quotient layers. -/
theorem length_eq_sum_layerLength :
    Module.length R M =
      ∑ k ∈ Finset.Ico 0 F.height, F.layerLength k := by
  have h := F.length_carrier_eq_sum_layerLength 0 (Nat.zero_le _)
  rw [F.exhaustive] at h
  simpa using h

end FiniteFilteredModule

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.length_carrier_eq_sum_layerLength
#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.length_eq_sum_layerLength
