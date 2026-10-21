module

public import tests.SymbolFractionReesOracle
public import SymplecticStafford.Filtered.M05Luna20260912.FaithfulModuleAdapter

@[expose] public section

/-!
# Independent oracle for the faithful M05 module adapter

The concrete polynomial source datum supplies the already-proved selected
source-localization equivalence.  The regular opposite modules instantiate
the adapter without adding any paper hypothesis.  The oracle checks a
nonzero Laurent-Rees class, the exact right-action equation, and transport of
the proper bottom/top submodule inclusion.
-/

namespace SymplecticStaffordTest.M05Luna20260912

noncomputable section

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.M05Luna20260912
open SymplecticStafford.Filtered.SymbolFractionRees
open SymplecticStafford.Filtered.SymbolFractionReesLocalization
open SymplecticStaffordTest.SymbolFractionReesOracle

abbrev sourceOpposite :=
  SourceOppositeRing concreteData

abbrev homogeneousOpposite :=
  HomogeneousOppositeRing concreteData

def regularComparison :
    FaithfulModuleComparison concreteData sourceOpposite homogeneousOpposite :=
  { toAddEquiv := (sourceHomogeneousOppositeEquiv concreteData).toAddEquiv
    map_smul' := by
      intro r x
      change sourceHomogeneousOppositeEquiv concreteData (r * x) =
        sourceHomogeneousOppositeEquiv concreteData r *
          sourceHomogeneousOppositeEquiv concreteData x
      exact (sourceHomogeneousOppositeEquiv concreteData).map_mul r x }

theorem regular_nonzero_survival :
    regularComparison.toAddEquiv.symm
        (MulOpposite.op xTerm) ≠ 0 := by
  intro hzero
  have htarget := congrArg
    regularComparison hzero
  apply xTerm_ne_zero
  simpa [regularComparison, sourceHomogeneousOppositeEquiv] using htarget

theorem regular_action_is_exact (r x : sourceOpposite) :
    regularComparison (r • x) =
      sourceHomogeneousOppositeEquiv concreteData r •
        regularComparison x := by
  exact map_smul (C := concreteData)
    regularComparison r x

theorem regular_strict_transport :
    mapSubmodule
        regularComparison
        (⊥ : Submodule sourceOpposite sourceOpposite) <
      mapSubmodule
        regularComparison
        (⊤ : Submodule sourceOpposite sourceOpposite) := by
  apply (map_strict_iff (C := concreteData)
    regularComparison).mpr
  apply lt_of_le_of_ne bot_le
  intro hEq
  apply regular_nonzero_survival
  let x₀ : sourceOpposite := regularComparison.toAddEquiv.symm (MulOpposite.op xTerm)
  have hx₀ : x₀ ∈ (⊥ : Submodule sourceOpposite sourceOpposite) := by
    rw [hEq]
    exact Submodule.mem_top
  simpa [x₀] using hx₀

end

end SymplecticStaffordTest.M05Luna20260912

#print axioms
  SymplecticStaffordTest.M05Luna20260912.regular_nonzero_survival
#print axioms
  SymplecticStaffordTest.M05Luna20260912.regular_action_is_exact
#print axioms
  SymplecticStaffordTest.M05Luna20260912.regular_strict_transport
