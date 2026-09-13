import tests.SymbolFractionReesOracle
import SymplecticStafford.Filtered.M05Luna20260912.FiniteStrictChainTransport

/-!
# Independent oracle for finite strict-chain transport

The regular opposite module over the concrete selected localization has the
two-step chain `⊥ < ⊤`.  The oracle checks both directions of the finite-chain
statement on that actual carrier and action.
-/

namespace SymplecticStaffordTest.M05Luna20260912

noncomputable section

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.M05Luna20260912
open SymplecticStafford.Filtered.SymbolFractionRees
open SymplecticStafford.Filtered.SymbolFractionReesLocalization
open SymplecticStaffordTest.SymbolFractionReesOracle

abbrev sourceOpposite := SourceOppositeRing concreteData
abbrev homogeneousOpposite := HomogeneousOppositeRing concreteData

def regularComparison :
    FaithfulModuleComparison concreteData sourceOpposite homogeneousOpposite :=
  { toAddEquiv := (sourceHomogeneousOppositeEquiv concreteData).toAddEquiv
    map_smul' := by
      intro r x
      change sourceHomogeneousOppositeEquiv concreteData (r * x) =
        sourceHomogeneousOppositeEquiv concreteData r *
          sourceHomogeneousOppositeEquiv concreteData x
      exact (sourceHomogeneousOppositeEquiv concreteData).map_mul r x }

def twoStep : Fin (1 + 1) → Submodule sourceOpposite sourceOpposite :=
  fun i => if i = 0 then ⊥ else ⊤

theorem twoStep_strict :
    ∀ i : Fin 1, twoStep i.castSucc < twoStep i.succ := by
  intro i
  fin_cases i
  change (⊥ : Submodule sourceOpposite sourceOpposite) < ⊤
  apply lt_of_le_of_ne bot_le
  intro hEq
  let x₀ : sourceOpposite :=
    regularComparison.toAddEquiv.symm (MulOpposite.op xTerm)
  have hx₀ : x₀ ∈ (⊥ : Submodule sourceOpposite sourceOpposite) := by
    rw [hEq]
    exact Submodule.mem_top
  have hx₀_ne : x₀ ≠ 0 := by
    intro hzero
    apply xTerm_ne_zero
    have htarget := congrArg regularComparison hzero
    simpa [x₀, regularComparison] using htarget
  exact hx₀_ne (by simpa using hx₀)

theorem transported_twoStep_strict :
    ∀ i : Fin 1,
      mapChain regularComparison twoStep i.castSucc <
        mapChain regularComparison twoStep i.succ := by
  exact (mapChain_strict_iff regularComparison twoStep).mpr twoStep_strict

theorem transport_reflects_twoStep :
    (∀ i : Fin 1,
      mapChain regularComparison twoStep i.castSucc <
        mapChain regularComparison twoStep i.succ) ↔
      (∀ i : Fin 1, twoStep i.castSucc < twoStep i.succ) := by
  exact mapChain_strict_iff regularComparison twoStep

end

end SymplecticStaffordTest.M05Luna20260912

#print axioms
  SymplecticStaffordTest.M05Luna20260912.twoStep_strict
#print axioms
  SymplecticStaffordTest.M05Luna20260912.transported_twoStep_strict
#print axioms
  SymplecticStaffordTest.M05Luna20260912.transport_reflects_twoStep
