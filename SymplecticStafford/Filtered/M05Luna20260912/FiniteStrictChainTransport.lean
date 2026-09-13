import SymplecticStafford.Filtered.M05Luna20260912.FaithfulModuleAdapter

/-!
# M05: finite strict-chain transport for the selected localization adapter

The faithful module adapter transports one strict submodule inclusion at a
time.  This file packages the same fact for an arbitrary finite indexed
chain.  It is an exact consequence of the supplied additive equivalence and
its opposite-ring action law; it does not identify the selected localization
with the paper's homogeneous localization or prove filtered-to-graded
survival.
-/

namespace SymplecticStafford.Filtered

universe u v w

noncomputable section

open SymplecticStafford
open SymbolFractionRees
open SymbolFractionReesLocalization

namespace M05Luna20260912

variable {R : Type u} [Ring R]
variable {C : SymbolFractionFiltration.Data R}
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [AddCommGroup N]
variable [Module (SourceOppositeRing C) M]
variable [Module (HomogeneousOppositeRing C) N]

/-- The pointwise image of a finite chain under the faithful adapter. -/
def mapChain (e : FaithfulModuleComparison (C := C) M N) {n : ℕ}
    (level : Fin (n + 1) → Submodule (SourceOppositeRing C) M) :
    Fin (n + 1) → Submodule (HomogeneousOppositeRing C) N :=
  fun i => mapSubmodule e (level i)

/-- Every finite strict chain is preserved, and reflected, by the selected
localization module transport. -/
theorem mapChain_strict_iff
    (e : FaithfulModuleComparison (C := C) M N) {n : ℕ}
    (level : Fin (n + 1) → Submodule (SourceOppositeRing C) M) :
    (∀ i : Fin n,
      mapChain e level i.castSucc < mapChain e level i.succ) ↔
      (∀ i : Fin n, level i.castSucc < level i.succ) := by
  constructor
  · intro h i
    exact (map_strict_iff e).mp (h i)
  · intro h i
    exact (map_strict_iff e).mpr (h i)

end M05Luna20260912

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.M05Luna20260912.mapChain_strict_iff
