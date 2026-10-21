module

public import tests.M05Luna20260912.FaithfulModuleAdapterOracle
public import SymplecticStafford.Filtered.M05Luna20260912.FaithfulModuleCoverTransport

@[expose] public section

/-!
# Independent oracle for M05 cover transport

The concrete selected-localization regular modules are not simple, so the
oracle checks the non-covering reflexive interval at an actual submodule pair.
The first two facts are proved directly from the definition of `CovBy`; the
transport theorem is then checked on that concrete adapter instance.
-/

namespace SymplecticStaffordTest.M05Luna20260912

noncomputable section

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.M05Luna20260912
open SymplecticStaffordTest.SymbolFractionReesOracle

theorem regular_bottom_not_cover :
    ¬ mapSubmodule regularComparison
        (⊥ : Submodule sourceOpposite sourceOpposite) ⋖
      mapSubmodule regularComparison
        (⊥ : Submodule sourceOpposite sourceOpposite) := by
  simp [CovBy]

theorem source_bottom_not_cover :
    ¬ ((⊥ : Submodule sourceOpposite sourceOpposite) ⋖
      (⊥ : Submodule sourceOpposite sourceOpposite)) := by
  simp [CovBy]

theorem regular_cover_transport :
    (mapSubmodule regularComparison
        (⊥ : Submodule sourceOpposite sourceOpposite) ⋖
      mapSubmodule regularComparison
        (⊥ : Submodule sourceOpposite sourceOpposite)) ↔
      ((⊥ : Submodule sourceOpposite sourceOpposite) ⋖
        (⊥ : Submodule sourceOpposite sourceOpposite)) := by
  exact map_covBy_iff regularComparison

end

end SymplecticStaffordTest.M05Luna20260912

#print axioms SymplecticStaffordTest.M05Luna20260912.regular_bottom_not_cover
#print axioms SymplecticStaffordTest.M05Luna20260912.source_bottom_not_cover
#print axioms SymplecticStaffordTest.M05Luna20260912.regular_cover_transport
