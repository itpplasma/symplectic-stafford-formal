module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Filtered.GoodFiltration
public import SymplecticStafford.Filtered.RingFiltrationBridge
public import SymplecticStafford.Filtered.GoodWeightedModule

@[expose] public section

/-!
# A finite-generation boundary for integer weighted detectors

Finite bounded generation of a filtered module does not, by itself, produce
an injective finite coordinate detector with coefficients in the filtered
ring.  The smallest obstruction is the cyclic torsion module `ZMod 2` over
`ℤ`: it has a one-element bounded generating set and an exhaustive good
filtration, but every `ℤ`-linear map into a finite product of copies of `ℤ`
kills its generator.

This is a genuine boundary for the weighted API.  It is independent of the
negative weights (which are allowed by `FaithfulWeightedDetector`); the
failure occurs before weights or triangularity can be used.  Thus a proposed
universal construction must supply a torsion-sensitive coefficient module,
or an additional torsion-freeness/embedding hypothesis.  No assertion about
the conditional detector results is made here.
-/

namespace SymplecticStafford.Filtered

/-! The constant filtration on `ℤ` supplies the filtered-ring input. -/
def integerConstantFiltration : RingFiltrationData (R := ℤ) where
  carrier := fun _ => ⊤
  one_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; exact le_rfl
  exhaustive := by intro a; exact ⟨0, by simp⟩

/-! A bounded good filtration of the cyclic module `ZMod 2`. -/
def zmodTwoGenerator : Fin 1 → ZMod 2 := fun _ => 1

theorem zmodTwoGenerator_span_top :
    Submodule.span ℤ (Set.range zmodTwoGenerator) = (⊤ : Submodule ℤ (ZMod 2)) := by
  apply top_unique
  intro x hx
  have hgen : (1 : ZMod 2) ∈
      Submodule.span ℤ (Set.range zmodTwoGenerator) := by
    apply Submodule.subset_span
    exact ⟨0, by simp [zmodTwoGenerator]⟩
  rcases ZMod.intCast_surjective x with ⟨z, rfl⟩
  have hsmul := Submodule.smul_mem
    (Submodule.span ℤ (Set.range zmodTwoGenerator)) z hgen
  simpa using hsmul

def zmodTwoGoodFiltration : ModuleFiltrationData
    integerConstantFiltration.toFiltrationData (ZMod 2) :=
  GoodFiltration.moduleFiltration integerConstantFiltration.toFiltrationData
    zmodTwoGenerator (fun _ => 0) zmodTwoGenerator_span_top

theorem zmodTwo_has_bounded_generator :
    (1 : ZMod 2) ∈ zmodTwoGoodFiltration.carrier 0 := by
  change (1 : ZMod 2) ∈
    GoodFiltration.carrier integerConstantFiltration.toFiltrationData
      zmodTwoGenerator (fun _ => 0) 0
  simpa [zmodTwoGenerator] using
    (GoodFiltration.generator_mem integerConstantFiltration.toFiltrationData
      zmodTwoGenerator (fun _ => 0) ⟨0, by decide⟩)

theorem zmodTwo_nontrivial : (1 : ZMod 2) ≠ 0 := by
  norm_num

/- The obstruction already occurs for a finitely generated module itself. -/
theorem zmodTwo_module_finite : Module.Finite ℤ (ZMod 2) := by
  infer_instance

/-!
No finite integer-coordinate detector can be faithful on this module.  The
proof uses only `2 • 1 = 0` in `ZMod 2` and that `ℤ` has no 2-torsion, so it
applies to every finite, nonempty coordinate type and does not depend on an
ordering or on the chosen integer weights.
-/
theorem no_integer_finite_coordinate_detector
    {ι : Type} [Nonempty ι] [Fintype ι] [DecidableEq ι] :
    ¬ Nonempty (FaithfulWeightedDetector (ι := ι) (K := ℤ) (M := ZMod 2)) := by
  rintro ⟨D⟩
  have htwo : (2 : ℤ) • (1 : ZMod 2) = 0 := by
    rw [show (2 : ℤ) = (2 : ℕ) by norm_num]
    exact ZMod.natCast_self 2
  have hmapped := congrArg D.encode htwo
  have hencode : D.encode (1 : ZMod 2) = 0 := by
    funext i
    have hi := congrFun hmapped i
    have hi' : (2 : ℤ) * D.encode (1 : ZMod 2) i = 0 := by
      simpa only [map_smul, map_zero, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using hi
    rcases mul_eq_zero.mp hi' with htwo' | hi'
    · norm_num at htwo'
    · exact hi'
  apply zmodTwo_nontrivial
  apply D.encode_injective
  rw [hencode, map_zero]

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.zmodTwoGenerator_span_top
#print axioms SymplecticStafford.Filtered.zmodTwo_has_bounded_generator
#print axioms SymplecticStafford.Filtered.zmodTwo_module_finite
#print axioms SymplecticStafford.Filtered.no_integer_finite_coordinate_detector
