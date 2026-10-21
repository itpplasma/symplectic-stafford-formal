module

public import SymplecticStafford.Filtered.M05Luna20260912.FaithfulModuleAdapter

@[expose] public section

/-!
# M05: cover transport for the faithful module adapter

The existing adapter transports strict submodule inclusions across the actual
selected-localization module comparison.  This file records the next small
order-theoretic consequence: a composition-series step (`CovBy`) is preserved
in both directions.  The proof uses only the already explicit action
compatibility and additive equivalence; it does not identify the selected
localization with the paper's homogeneous localization.
-/

namespace SymplecticStafford.Filtered.M05Luna20260912

universe u v w

noncomputable section

open SymplecticStafford
open SymplecticStafford.Filtered

variable {R : Type u} [Ring R]
variable {C : SymbolFractionFiltration.Data R}
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [AddCommGroup N]
variable [Module (SourceOppositeRing C) M]
variable [Module (HomogeneousOppositeRing C) N]

def comapSubmodule (e : FaithfulModuleComparison (C := C) M N)
    (B : Submodule (HomogeneousOppositeRing C) N) :
    Submodule (SourceOppositeRing C) M :=
  { carrier := {x | e.toAddEquiv x ∈ B}
    zero_mem' := by simpa using B.zero_mem
    add_mem' := by
      intro x y hx hy
      simpa [map_add] using B.add_mem hx hy
    smul_mem' := by
      intro r x hx
      change e.toAddEquiv (r • x) ∈ B
      rw [map_smul e]
      exact B.smul_mem _ hx }

@[simp] theorem comapSubmodule_mem_iff
    (e : FaithfulModuleComparison (C := C) M N)
    (B : Submodule (HomogeneousOppositeRing C) N) (x : M) :
    x ∈ comapSubmodule e B ↔ e.toAddEquiv x ∈ B := Iff.rfl

@[simp] theorem mapSubmodule_comapSubmodule
    (e : FaithfulModuleComparison (C := C) M N)
    (B : Submodule (HomogeneousOppositeRing C) N) :
    mapSubmodule e (comapSubmodule e B) = B := by
  ext y
  rw [mapSubmodule_mem_iff]
  constructor
  · intro hy
    simpa using hy
  · intro hy
    simpa using hy

@[simp] theorem comapSubmodule_mapSubmodule
    (e : FaithfulModuleComparison (C := C) M N)
    (A : Submodule (SourceOppositeRing C) M) :
    comapSubmodule e (mapSubmodule e A) = A := by
  ext x
  rw [comapSubmodule_mem_iff, mapSubmodule_mem_iff]
  simp

/-- The cover relation between two source submodules is preserved by the
faithful selected-source module transport. -/
theorem map_covBy_iff
    (e : FaithfulModuleComparison (C := C) M N)
    {A B : Submodule (SourceOppositeRing C) M} :
    mapSubmodule e A ⋖ mapSubmodule e B ↔ A ⋖ B := by
  constructor
  · intro h
    rw [CovBy] at h ⊢
    refine ⟨(map_strict_iff e).mp h.1, ?_⟩
    intro D hAD
    intro hDB
    exact h.2 ((map_strict_iff e).mpr hAD)
      ((map_strict_iff e).mpr hDB)
  · intro h
    rw [CovBy] at h ⊢
    refine ⟨(map_strict_iff e).mpr h.1, ?_⟩
    intro D hAD
    intro hDB
    let D₀ := comapSubmodule e D
    have hAD' : A < D₀ := by
      apply (map_strict_iff e).mp
      simpa [D₀] using hAD
    have hDB' : D₀ < B := by
      apply (map_strict_iff e).mp
      simpa [D₀] using hDB
    exact h.2 hAD' hDB'

end

end SymplecticStafford.Filtered.M05Luna20260912

#print axioms SymplecticStafford.Filtered.M05Luna20260912.map_covBy_iff
