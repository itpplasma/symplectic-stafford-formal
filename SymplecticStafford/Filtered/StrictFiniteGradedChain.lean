module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import SymplecticStafford.Filtered.ActualClassSupport

@[expose] public section

/-!
# Strictness for a finite filtered submodule

This file isolates the safe finite-chain statement needed when a graded
module is localized at the homogeneous set `Σ_p`.  Given a finite separated
filtration on `M` and a submodule `A`, the filtration on `A` is the actual
intersection filtration.  The inclusion `A → M` then induces an injective
map on every associated layer.  Thus a strict inclusion can fail to be
visible only through failure of surjectivity on some layer; the latter is an
explicit, checkable condition and is not replaced by ordinary prime
localization.

The theorem uses only finite exhaustiveness/separatedness and genuine
submodules.  A Zariskian or Rees hypothesis may be used by a later consumer
to construct this finite filtered chain, but is not silently inferred here.
-/

namespace SymplecticStafford.Filtered

universe u v

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace StrictFiniteGradedChain

/-- The actual intersection filtration on a filtered submodule. -/
def inducedFiltration
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Submodule R M) : FiniteFilteredModule (R := R) (M := A) where
  height := F.height
  carrier := fun n => (F.carrier n).comap A.subtype
  exhaustive := by
    rw [F.exhaustive]
    ext x
    simp
  descending := by
    intro n x hx
    exact F.descending n hx
  separated := by
    rw [F.separated]
    ext x
    simp

@[simp] theorem inducedFiltration_carrier
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Submodule R M) (n : ℕ) :
    (inducedFiltration F A).carrier n = (F.carrier n).comap A.subtype := rfl

private def layerInclusion
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Submodule R M) (k : Fin F.height) :
    (inducedFiltration F A).carrier k.1 →ₗ[R] F.carrier k.1 where
  toFun x := ⟨x.1, x.2⟩
  map_add' x y := rfl
  map_smul' c x := rfl

/-- The map induced on an associated layer by a strict submodule inclusion. -/
def layerMap
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Submodule R M) (k : Fin F.height) :
    filteredLayerQuotient (inducedFiltration F A) k →ₗ[R]
      filteredLayerQuotient F k := by
  let p := filteredLayerSubmodule (inducedFiltration F A) k
  let q := filteredLayerSubmodule F k
  let f := layerInclusion F A k
  exact p.liftQ (q.mkQ.comp f) (by
    intro x hx
    change q.mkQ (f x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx)

@[simp] theorem layerMap_mk
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Submodule R M) (k : Fin F.height)
    (x : (inducedFiltration F A).carrier k.1) :
    layerMap F A k
        (Submodule.Quotient.mk (p :=
          filteredLayerSubmodule (inducedFiltration F A) k) x) =
      Submodule.Quotient.mk (p := filteredLayerSubmodule F k)
        (layerInclusion F A k x) := by
  rfl

/-- The associated-layer map is injective: this is the kernel-checked
strictness statement for the intersection filtration. -/
theorem layerMap_injective
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Submodule R M) (k : Fin F.height) :
    Function.Injective (layerMap F A k) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Quotient.exists_rep x
  obtain ⟨y, rfl⟩ := Quotient.exists_rep y
  apply (Submodule.Quotient.eq
    (filteredLayerSubmodule (inducedFiltration F A) k)).mpr
  have hzero :
      Submodule.mkQ (filteredLayerSubmodule F k)
          (layerInclusion F A k (x - y)) = 0 := by
    have hmapeq :
        layerMap F A k (Submodule.Quotient.mk
            (p := filteredLayerSubmodule (inducedFiltration F A) k) x) -
          layerMap F A k (Submodule.Quotient.mk
            (p := filteredLayerSubmodule (inducedFiltration F A) k) y) = 0 := by
      have hxy' :
          layerMap F A k (Submodule.Quotient.mk
              (p := filteredLayerSubmodule (inducedFiltration F A) k) x) =
            layerMap F A k (Submodule.Quotient.mk
              (p := filteredLayerSubmodule (inducedFiltration F A) k) y) := hxy
      rw [hxy']
      simp
    have hdiff :
        Submodule.mkQ (filteredLayerSubmodule F k)
            (layerInclusion F A k x) -
          Submodule.mkQ (filteredLayerSubmodule F k)
            (layerInclusion F A k y) = 0 := by
      simpa only [layerMap_mk, Submodule.mkQ_apply] using hmapeq
    simpa only [map_sub] using hdiff
  have hzero' :
      Submodule.mkQ (filteredLayerSubmodule F k)
          (layerInclusion F A k (x - y)) = 0 := by
    exact hzero
  have hnext :
      ((x - y : (inducedFiltration F A).carrier k.1) : M) ∈
        F.carrier (k.1 + 1) := by
    exact (Submodule.Quotient.mk_eq_zero
      (filteredLayerSubmodule F k)).mp hzero'
  exact hnext

/-!
The finite separatedness hypotheses now have a concrete consequence.  If
every associated-layer map were surjective, downward induction would lift
each filtered class into `A`; at the separated terminal layer the remainder
is zero.  Hence a proper filtered submodule has a genuinely non-surjective
graded layer.  This is the finite-chain strictness statement that a later
`G_{Σ_p}` construction may consume.
-/
theorem exists_layerMap_not_surjective_of_lt_top
    (F : FiniteFilteredModule (R := R) (M := M))
    (A : Submodule R M) (hA : A < (⊤ : Submodule R M)) :
    ∃ k : Fin F.height, ¬ Function.Surjective (layerMap F A k) := by
  by_contra hnone
  push_neg at hnone
  have hAll' : ∀ m, ∀ n, F.height - n = m → n ≤ F.height → ∀ x : M,
      x ∈ F.carrier n → x ∈ A := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro n hmeasure hn x hx
        by_cases hlast : n = F.height
        · have hx0 : x = 0 := by
            have hx' : x ∈ (⊥ : Submodule R M) := by
              simpa [hlast, F.separated] using hx
            simpa using hx'
          exact hx0 ▸ A.zero_mem
        · have hnlt : n < F.height := lt_of_le_of_ne hn hlast
          let k : Fin F.height := ⟨n, hnlt⟩
          let qx : filteredLayerQuotient F k :=
            Submodule.Quotient.mk
              (p := filteredLayerSubmodule F k) ⟨x, hx⟩
          obtain ⟨qy, hqy⟩ := hnone k qx
          obtain ⟨y, rfl⟩ := Quotient.exists_rep qy
          have hclass :
              Submodule.Quotient.mk (p := filteredLayerSubmodule F k)
                  (layerInclusion F A k y) =
                Submodule.Quotient.mk (p := filteredLayerSubmodule F k)
                  ⟨x, hx⟩ := by
            change layerMap F A k
                (Submodule.Quotient.mk
                  (p := filteredLayerSubmodule (inducedFiltration F A) k) y) = _ at hqy
            rw [layerMap_mk] at hqy
            exact hqy
          have hmem :
              (layerInclusion F A k y) - ⟨x, hx⟩ ∈
                filteredLayerSubmodule F k :=
            (Submodule.Quotient.eq (filteredLayerSubmodule F k)).mp hclass
          have hnext : x - (y : M) ∈ F.carrier (n + 1) := by
            have hmem' := hmem
            change ((layerInclusion F A k y).1 - x) ∈ F.carrier (n + 1) at hmem'
            have hinc : (layerInclusion F A k y).1 = (y : M) := rfl
            rw [hinc] at hmem'
            simpa [sub_eq_add_neg, add_comm] using
              (F.carrier (n + 1)).neg_mem hmem'
          have hmeasure_next : F.height - (n + 1) < m := by
            omega
          have hrem : x - (y : M) ∈ A := by
            apply ih (F.height - (n + 1)) hmeasure_next (n + 1)
              rfl (by omega) (x - (y : M)) hnext
          have hadd : (x - (y : M)) + (y : M) ∈ A :=
            A.add_mem hrem y.1.property
          simpa [sub_add_cancel] using hadd
  have htop : ∀ x : M, x ∈ A := by
    intro x
    have hx : x ∈ F.carrier 0 := by
      rw [F.exhaustive]
      trivial
    exact hAll' (F.height - 0) 0 rfl (Nat.zero_le _) x hx
  apply hA.2
  intro x _
  exact htop x

end StrictFiniteGradedChain

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.StrictFiniteGradedChain.layerMap_injective
#print axioms SymplecticStafford.Filtered.StrictFiniteGradedChain.exists_layerMap_not_surjective_of_lt_top
