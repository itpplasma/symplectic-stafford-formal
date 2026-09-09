import Mathlib.Tactic
import Stafford38.Weyl.IteratedEquivalence
import SymplecticStafford.Source.WeylHigherDimensionalEvolutionary

/-! Independent consumer for the higher-rank finite-potential calibration.

The oracle instantiates the adapter at rank two with transverse coordinate and
momentum coefficients. It proves their required commutation with the
distinguished pair from the independent old-generator lemmas, then invokes the
generic evolutionary certificate directly rather than the adapter under test.
The theorem is bounded and does not claim universal S1.
-/

namespace SymplecticStafford.WeylHigherDimensionalEvolutionaryOracle

open Stafford38
open Stafford38.Evolution
open Stafford38.WeylIteratedEquivalence

abbrev W := PresentedWeyl ℚ 2

private def x : W := presentedCoordinate ℚ 1
private def p : W := presentedMomentum ℚ 1
private def a : W := previousWeylEmbedding ℚ 1 (presentedCoordinate ℚ 0)
private def b : W := previousWeylEmbedding ℚ 1 (presentedMomentum ℚ 0)

private theorem a_commutes_x : a * x = x * a := by
  exact (presentedCoordinate_commutes_previous ℚ 1
    (presentedCoordinate ℚ 0)).symm

private theorem a_commutes_p : a * p = p * a := by
  exact (presentedMomentum_commutes_previous ℚ 1
    (presentedCoordinate ℚ 0)).symm

private theorem b_commutes_x : b * x = x * b := by
  exact (presentedCoordinate_commutes_previous ℚ 1
    (presentedMomentum ℚ 0)).symm

private theorem b_commutes_p : b * p = p * b := by
  exact (presentedMomentum_commutes_previous ℚ 1
    (presentedMomentum ℚ 0)).symm

example :
    ∃ R S : W,
      1 = (p ^ 2 - (a + b * x)) * R + x ^ 2 *
        (p ^ 2 - (a + b * x)) * S := by
  let terms : List (PresentedWeyl ℚ 1 × ℕ) :=
    [(presentedCoordinate ℚ 0, 0), (presentedMomentum ℚ 0, 1)]
  let d : W := p ^ 2 - potentialSum x
    (terms.map fun t =>
      (previousWeylEmbedding ℚ 1 t.1, t.2))
  have hd : d = p ^ 2 - (a + b * x) := by
    simp [d, terms, potentialSum, x, p, a, b]
  obtain ⟨R, S, h⟩ := evolutionaryCorollary
    (D := W) (x := x) (p := p) ℚ
    (presentedMomentum_mul_coordinate ℚ 1) (r := 2)
    (by decide) (terms.map fun t =>
      (previousWeylEmbedding ℚ 1 t.1, t.2))
    (by
      intro t ht
      rcases List.mem_map.mp ht with ⟨⟨c, j⟩, hc, rfl⟩
      simp [terms] at hc
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact a_commutes_x
      · exact b_commutes_x)
    (by
      intro t ht
      rcases List.mem_map.mp ht with ⟨⟨c, j⟩, hc, rfl⟩
      simp [terms] at hc
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact a_commutes_p
      · exact b_commutes_p)
    (by rfl)
  refine ⟨R, S, ?_⟩
  simpa [d, hd, terms, x, p, a, b, potentialSum] using h

#print axioms a_commutes_x
#print axioms b_commutes_p

end SymplecticStafford.WeylHigherDimensionalEvolutionaryOracle
