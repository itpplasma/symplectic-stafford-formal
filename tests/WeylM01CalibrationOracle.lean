import Mathlib.Tactic
import SymplecticStafford.Filtered.WeylM01Calibration

/-! Independent oracle for the concrete Stafford38 Weyl M01 calibration.

This checks the actual original-ring filtration, rather than the historical
proposition-valued `AdmissibleSymplecticClass`.  It also checks the separate
Stafford38 associated-graded symbol equivalence.  No statement here lifts
these Weyl facts to arbitrary conic quantizations.
-/

namespace SymplecticStafford.WeylM01CalibrationOracle

open SymplecticStafford.Filtered
open Stafford38.Characteristic
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylAssociatedGraded

noncomputable section

abbrev W := PresentedWeyl ℚ 2

def model : M01FilteredAlgebra ℚ W := presentedWeylM01 ℚ 2

example :
    (model.filtration.carrier 0 : Set W) =
      Set.range (algebraMap ℚ W) :=
  model.degree_zero

example (a : W) :
    ∃ N : ℕ, a ∈ model.filtration.carrier N := by
  exact exists_mem_bernsteinPiece ℚ a

example {N M : ℕ} {a b : W}
    (ha : a ∈ model.filtration.carrier N)
    (hb : b ∈ model.filtration.carrier M) :
    a * b ∈ model.filtration.carrier (N + M) := by
  exact mul_mem_bernsteinPiece ℚ ha hb

example (c : ℚ) (a : W) :
    algebraMap ℚ W c * a = a * algebraMap ℚ W c :=
  model.central c a

example (a b : presentedWeylBernsteinGraded ℚ 2) :
    a * b = b * a := by
  exact presentedWeylBernsteinGraded_mul_comm ℚ 2 a b

example :
    Function.Injective (presentedWeylBernsteinGradedSymbolEquiv ℚ 2) :=
  presentedWeylBernsteinGraded_symbol_equiv_injective ℚ 2

end
end SymplecticStafford.WeylM01CalibrationOracle

#print axioms SymplecticStafford.Filtered.presentedWeylM01
#print axioms SymplecticStafford.Filtered.presentedWeylBernsteinGradedSymbolEquiv
