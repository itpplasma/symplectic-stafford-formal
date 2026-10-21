module

public import SymplecticStafford.Filtered.M01PolynomialFiltrationBoundary

@[expose] public section

/-! Independent oracle for the concrete polynomial filtration boundary. -/

namespace SymplecticStafford.M01PolynomialFiltrationBoundaryOracle

open SymplecticStafford.Filtered

example :
    polynomialOneStepFiltration.carrier 0 = polynomialScalarLayer := by
  exact polynomialOneStepFiltration_degree_zero

example :
    ∀ {i j : ℕ} {a b : PolynomialRing},
      a ∈ polynomialOneStepFiltration.carrier i →
      b ∈ polynomialOneStepFiltration.carrier j →
      a * b ∈ polynomialOneStepFiltration.carrier (i + j) := by
  intro i j a b ha hb
  exact polynomialOneStepFiltration.mul_mem ha hb

example :
    Polynomial.X ∉ polynomialScalarLayer := by
  intro h
  rcases h with ⟨q, hq⟩
  have hcoeff := congrArg (fun p : PolynomialRing => p.coeff 1) hq
  simpa using hcoeff

example :
    ¬ ∃ G : SymplecticStafford.Filtered.RingFiltrationData
      (R := PolynomialRing),
      (G.carrier 0 : Set PolynomialRing) =
        polynomialOneStepFiltration.carrier 0 :=
  polynomial_filtration_cannot_upgrade_to_ring_filtration

end SymplecticStafford.M01PolynomialFiltrationBoundaryOracle

#print axioms SymplecticStafford.Filtered.polynomialOneStepFiltration
#print axioms SymplecticStafford.Filtered.polynomial_filtration_cannot_upgrade_to_ring_filtration
