module

public import Mathlib.Data.ZMod.Basic
public import SymplecticStafford.Filtered.FiniteCoordinateDetectorBoundary

@[expose] public section

/- Independent behavioral oracle for the finite-coordinate detector boundary. -/
namespace SymplecticStafford.Filtered.FiniteCoordinateDetectorBoundaryOracle

example : (1 : ZMod 2) ≠ 0 := by
  norm_num

example : Module.Finite ℤ (ZMod 2) := by
  infer_instance

example :
    Submodule.span ℤ (Set.range zmodTwoGenerator) =
      (⊤ : Submodule ℤ (ZMod 2)) := by
  apply top_unique
  intro x hx
  rcases ZMod.intCast_surjective x with ⟨z, rfl⟩
  have hgen : (1 : ZMod 2) ∈
      Submodule.span ℤ (Set.range zmodTwoGenerator) := by
    apply Submodule.subset_span
    exact ⟨0, by simp [zmodTwoGenerator]⟩
  have hsmul := Submodule.smul_mem
    (Submodule.span ℤ (Set.range zmodTwoGenerator)) z hgen
  simpa using hsmul

example : (1 : ZMod 2) ∈ zmodTwoGoodFiltration.carrier 0 := by
  change (1 : ZMod 2) ∈
    GoodFiltration.carrier integerConstantFiltration.toFiltrationData
      zmodTwoGenerator (fun _ => 0) 0
  apply AddSubmonoid.subset_closure
  exact ⟨⟨0, by decide⟩, 0, 1, by simp,
    by simp [integerConstantFiltration], by simp [zmodTwoGenerator]⟩

theorem oracle_no_detector {ι : Type} [Nonempty ι] [Fintype ι] [DecidableEq ι] :
    ¬ Nonempty (FaithfulWeightedDetector (ι := ι) (K := ℤ) (M := ZMod 2)) :=
  by
    rintro ⟨D⟩
    have htwo : (2 : ℤ) • (1 : ZMod 2) = 0 := by
      rw [show (2 : ℤ) = (2 : ℕ) by norm_num]
      exact ZMod.natCast_self 2
    have hmapped := congrArg D.encode htwo
    have hencode : D.encode (1 : ZMod 2) = 0 := by
      funext i
      have hi := congrFun hmapped i
      have hi' : (2 : ℤ) * D.encode (1 : ZMod 2) i = 0 := by
        simpa only [map_smul, map_zero, Pi.smul_apply, Pi.zero_apply,
          smul_eq_mul] using hi
      rcases mul_eq_zero.mp hi' with htwo' | hi'
      · norm_num at htwo'
      · exact hi'
    apply (by norm_num : (1 : ZMod 2) ≠ 0)
    apply D.encode_injective
    rw [hencode, map_zero]

/- The obstruction persists for the smallest concrete finite detector. -/
example :
    ¬ Nonempty (FaithfulWeightedDetector (ι := Fin 1) (K := ℤ) (M := ZMod 2)) := by
  exact oracle_no_detector

end SymplecticStafford.Filtered.FiniteCoordinateDetectorBoundaryOracle
