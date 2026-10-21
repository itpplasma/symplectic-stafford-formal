module

public import Mathlib.RingTheory.FiniteLength
public import SymplecticStafford.Filtered.ActualClassSupport

@[expose] public section

namespace SymplecticStafford.Filtered

universe u v

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

theorem FiniteFilteredModule.isFiniteLength_of_layers
    (F : FiniteFilteredModule (R := R) (M := M))
    (hlayer : ∀ k : Fin F.height,
      IsFiniteLength R (filteredLayerQuotient F k)) :
    IsFiniteLength R M := by
  have hcarrier : ∀ n, n ≤ F.height → IsFiniteLength R (F.carrier n) := by
    intro n
    induction hn : F.height - n using Nat.strong_induction_on generalizing n with
    | h d ih =>
        intro hnle
        by_cases htop : n = F.height
        · letI : Subsingleton (F.carrier n) := by
            constructor
            intro x y
            have hx : (x : M) ∈ (⊥ : Submodule R M) := by
              simpa [htop, F.separated] using x.property
            have hy : (y : M) ∈ (⊥ : Submodule R M) := by
              simpa [htop, F.separated] using y.property
            exact Subtype.ext (by simpa using hx.trans hy.symm)
          exact IsFiniteLength.of_subsingleton
        · have hnlt : n < F.height := lt_of_le_of_ne hnle htop
          let k : Fin F.height := ⟨n, hnlt⟩
          have hnext : IsFiniteLength R (F.carrier (n + 1)) := by
            apply ih (F.height - (n + 1))
            · omega
            · rfl
            · omega
          let e : filteredLayerSubmodule F k ≃ₗ[R] F.carrier (n + 1) :=
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
          have hsub :
              IsFiniteLength R (filteredLayerSubmodule F k) :=
            e.symm.isFiniteLength hnext
          rw [isFiniteLength_iff_isNoetherian_isArtinian] at hsub ⊢
          have hquot := hlayer k
          rw [isFiniteLength_iff_isNoetherian_isArtinian] at hquot
          exact ⟨
              (isNoetherian_iff_submodule_quotient (filteredLayerSubmodule F k)).mpr
              ⟨hsub.1, hquot.1⟩,
              (isArtinian_iff_submodule_quotient (filteredLayerSubmodule F k)).mpr
              ⟨hsub.2, hquot.2⟩⟩
  have hM : IsFiniteLength R (F.carrier 0) := hcarrier 0 (Nat.zero_le _)
  rw [F.exhaustive] at hM
  exact Submodule.topEquiv.isFiniteLength hM

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.isFiniteLength_of_layers
