import Mathlib.Algebra.Polynomial.AlgebraMap
import SymplecticStafford.Filtered.BoundedLayerSupport

/-!
# Q[X] oracle for bounded layer support transport

The finite filtration has two top layers followed by the zero terminal layer;
only the second top layer contributes a nonzero successive quotient.  It is
deliberately concrete and easy to audit: both presentations are the same
filtration, transported by the identity index equivalence.  The oracle
checks an actual polynomial class at layer one and the transported
support/defect conclusions.
-/

namespace SymplecticStafford.Filtered

namespace BoundedLayerSupportOracle

noncomputable section

local instance : Algebra ℚ (Polynomial ℚ) := Polynomial.algebraOfAlgebra

def polynomialTwoLayer : FiniteFilteredModule (R := ℚ) (M := Polynomial ℚ) where
  height := 2
  carrier n := if n < 2 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro n x hx
    by_cases hn : n < 2
    · simp [hn]
    · have hn1 : ¬n + 1 < 2 := by omega
      simpa [hn, hn1] using hx
  separated := by simp

def identityTransport :
    BoundedLayerReindex polynomialTwoLayer polynomialTwoLayer where
  index := Equiv.refl _
  layer_mem_iff := by intro k x; rfl
  next_mem_iff := by intro k x; rfl

example : (1 : Fin 2) ∈ polynomialTwoLayer.QuotientSupport := by
  refine ⟨1, ?_, ?_⟩
  · simp [polynomialTwoLayer]
  · rw [FiniteFilteredModule.quotient_ne_zero_iff_not_mem]
    simp [polynomialTwoLayer]

example :
    polynomialTwoLayer.QuotientSupport =
      identityTransport.index '' polynomialTwoLayer.QuotientSupport := by
  exact BoundedLayerReindex.quotientSupport_eq_image identityTransport

example :
    polynomialTwoLayer.QuotientSupportDimension =
      polynomialTwoLayer.QuotientSupportDimension := by
  exact BoundedLayerReindex.quotientSupportDimension_eq identityTransport

example :
    supportDimensionDefect polynomialTwoLayer.QuotientSupportDimension =
      supportDimensionDefect polynomialTwoLayer.QuotientSupportDimension := by
  exact BoundedLayerReindex.quotientSupportDefect_eq identityTransport

end

end BoundedLayerSupportOracle

end SymplecticStafford.Filtered
