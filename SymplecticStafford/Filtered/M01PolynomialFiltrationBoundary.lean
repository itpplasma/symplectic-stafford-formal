module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic
public import SymplecticStafford.Filtered.RingFiltrationBridge

@[expose] public section

/-!
# Polynomial M01 boundary: base-field layers are not right ideals

The standard degree-zero layer of `ℚ[X]` is the scalar image, and the
filtration with that layer followed by the whole ring is an actual exhaustive
multiplicative `FiltrationData`.  It is not a `RingFiltrationData`: the latter
requires every layer to be a submodule for the opposite-ring action, hence a
right ideal of the original ring.  Right multiplication by `X` leaves the
scalar layer.

This is the precise type mismatch that prevents the current concrete
`RingFiltrationData` API from representing the usual ℚ[X,Y]-style filtered
algebras.  The positive filtration below is genuine; the rejected upgrade is
proved by an explicit coefficient calculation.
-/

namespace SymplecticStafford.Filtered

open SymplecticStafford
open RingFiltrationData

abbrev PolynomialRing := Polynomial ℚ

def polynomialScalarLayer : Set PolynomialRing :=
  Set.range (algebraMap ℚ PolynomialRing)

/-- Scalar degree zero, with all positive layers present. -/
def polynomialOneStepFiltration : FiltrationData PolynomialRing where
  carrier := fun n => if n = 0 then polynomialScalarLayer else Set.univ
  zero_mem := by
    exact ⟨0, by simp⟩
  one_mem := by
    exact ⟨1, by simp⟩
  add_mem := by
    intro i j a b ha hb
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · rcases (show a ∈ polynomialScalarLayer by simpa [hi] using ha) with ⟨a₀, ha₀⟩
        rcases (show b ∈ polynomialScalarLayer by simpa [hj] using hb) with ⟨b₀, hb₀⟩
        subst i
        subst j
        refine ⟨a₀ + b₀, ?_⟩
        rw [← ha₀, ← hb₀]
        simp [map_add]
      · have hmax : max i j ≠ 0 := by omega
        simp only [hmax, if_false, Set.mem_univ]
    · have hmax : max i j ≠ 0 := by omega
      simp only [hmax, if_false, Set.mem_univ]
  mul_mem := by
    intro i j a b ha hb
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · rcases (show a ∈ polynomialScalarLayer by simpa [hi] using ha) with ⟨a₀, ha₀⟩
        rcases (show b ∈ polynomialScalarLayer by simpa [hj] using hb) with ⟨b₀, hb₀⟩
        subst i
        subst j
        refine ⟨a₀ * b₀, ?_⟩
        rw [← ha₀, ← hb₀]
        simp [map_mul]
      · have hsum : i + j ≠ 0 := by omega
        simp only [hsum, if_false, Set.mem_univ]
    · have hsum : i + j ≠ 0 := by omega
      simp only [hsum, if_false, Set.mem_univ]
  monotone := by
    intro i j hij a ha
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simpa [hi, hj] using ha
      · subst i
        simp [hj]
    · have hj : j ≠ 0 := by omega
      simp [hj]
  exhaustive := by
    intro p
    exact ⟨1, by simp⟩

theorem polynomialOneStepFiltration_degree_zero :
    polynomialOneStepFiltration.carrier 0 = polynomialScalarLayer := by
  rfl

theorem polynomial_scalar_layer_not_right_ideal :
    ¬ ∃ P : Submodule PolynomialRingᵐᵒᵖ PolynomialRing,
      (P : Set PolynomialRing) = polynomialScalarLayer := by
  rintro ⟨P, hP⟩
  have hone : (1 : PolynomialRing) ∈ P := by
    change (1 : PolynomialRing) ∈ (P : Set PolynomialRing)
    rw [hP]
    exact ⟨1, by simp⟩
  have hX : Polynomial.X ∈ P := by
    have hsmul := P.smul_mem (MulOpposite.op Polynomial.X) hone
    simpa using hsmul
  have hXscalar : Polynomial.X ∈ polynomialScalarLayer := by
    rw [← hP]
    exact hX
  rcases hXscalar with ⟨q, hq⟩
  have hcoeff := congrArg (fun p : PolynomialRing => p.coeff 1) hq
  simpa using hcoeff

theorem polynomial_filtration_cannot_upgrade_to_ring_filtration :
    ¬ ∃ G : SymplecticStafford.Filtered.RingFiltrationData
      (R := PolynomialRing),
      (G.carrier 0 : Set PolynomialRing) =
        polynomialOneStepFiltration.carrier 0 := by
  rintro ⟨G, hG⟩
  apply polynomial_scalar_layer_not_right_ideal
  refine ⟨G.carrier 0, ?_⟩
  rw [hG, polynomialOneStepFiltration_degree_zero]

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.polynomialOneStepFiltration
#print axioms SymplecticStafford.Filtered.polynomial_filtration_cannot_upgrade_to_ring_filtration
