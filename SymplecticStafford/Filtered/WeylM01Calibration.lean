module

public import SymplecticStafford.Filtered.M01StructuralClass
public import Stafford38.Weyl.MonicNormalization
public import Stafford38.Weyl.GradedAlgebra

@[expose] public section

namespace SymplecticStafford.Filtered

open SymplecticStafford
open Stafford38.Characteristic
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBW
open Stafford38.WeylSymbolCompatibility
open Stafford38.WeylMonicNormalization
open Stafford38.WeylAssociatedGraded

noncomputable section

universe u
variable (k : Type u) [Field k]

/-- The checked PBW normal form separates one and zero in the presented Weyl
    algebra, supplying the nontriviality needed by the structural class. -/
noncomputable instance presentedWeylNontrivial (n : ℕ) :
    Nontrivial (PresentedWeyl k n) := by
  refine ⟨1, 0, ?_⟩
  intro h
  have h' : (1 : SymbolRing k n) = 0 := by
    rw [← presentedNormalFormLinearEquiv_one k n]
    simpa [h] using congrArg (presentedNormalFormLinearEquiv k n) h
  exact one_ne_zero h'

/-- The Bernstein pieces, viewed as additive subgroups, form an actual
    exhaustive multiplicative filtration of the presented Weyl algebra. -/
def presentedWeylBernsteinFiltration (n : ℕ) :
    AdditiveFilteredRingData (PresentedWeyl k n) where
  carrier := fun N => (bernsteinPiece k n N).toAddSubgroup
  one_mem := by
    exact one_mem_bernsteinPiece k n
  mul_mem := by
    intro i j a b ha hb
    exact mul_mem_bernsteinPiece k ha hb
  monotone := by
    intro i j hij
    exact Submodule.toAddSubgroup_mono
      (presentedWeightPiece_mono k bernsteinWeight hij)
  exhaustive := by
    intro a
    exact exists_mem_bernsteinPiece k a

/-- The concrete Bernstein M01 record for the presented Weyl algebra. -/
def presentedWeylM01 (n : ℕ) :
    M01FilteredAlgebra k (PresentedWeyl k n) := by
  refine
    { filtration := presentedWeylBernsteinFiltration k n
      central := ?_
      degree_zero := ?_ }
  · intro c a
    exact Algebra.commutes c a
  · ext a
    constructor
    · intro ha
      obtain ⟨c, hc⟩ := eq_algebraMap_of_mem_bernsteinPiece_zero k ha
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, rfl⟩
      have h1 := (bernsteinPiece k n 0).smul_mem c
          (one_mem_bernsteinPiece k n)
      simpa [presentedWeylBernsteinFiltration, Algebra.smul_def] using h1

/-!
The preceding record is the original-ring side of the M01 bridge.  The
Stafford38 construction also supplies the *specific* associated graded object
for this Weyl model.  Keeping this as a named calibration is important: the
global commutative graded object is not inferred from the abstract
`AdditiveFilteredRingData` fields, and this file makes no claim for arbitrary
conic quantizations.
-/

abbrev presentedWeylBernsteinGraded (n : ℕ) :=
  PresentedAssociatedGraded k (@bernsteinWeight n)

noncomputable instance presentedWeylBernsteinGradedCommRing (n : ℕ) :
    CommRing (presentedWeylBernsteinGraded k n) :=
  presentedAssociatedGradedCommRing k (@bernsteinWeight n)

def presentedWeylBernsteinGradedSymbolEquiv (n : ℕ) :
    presentedWeylBernsteinGraded k n ≃ₐ[k] SymbolRing k n :=
  presentedAssociatedGradedAlgEquiv k (@bernsteinWeight n)

theorem presentedWeylBernsteinGraded_mul_comm (n : ℕ)
    (x y : presentedWeylBernsteinGraded k n) : x * y = y * x :=
  mul_comm x y

theorem presentedWeylBernsteinGraded_symbol_equiv_injective (n : ℕ) :
    Function.Injective (presentedWeylBernsteinGradedSymbolEquiv k n) :=
  (presentedWeylBernsteinGradedSymbolEquiv k n).injective

end
end SymplecticStafford.Filtered
