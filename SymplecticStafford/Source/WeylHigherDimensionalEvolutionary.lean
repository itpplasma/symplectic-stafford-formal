import Stafford38.EvolutionaryCorollary
import Stafford38.Weyl.IteratedEquivalence

/-!
# Higher-rank original-ring Weyl evolutionary calibration

The coefficients are elements of the recursively embedded old `A_n`, so this
adapter stays in the presented original `A_(n+1)` rather than switching to an
abstract tensor-product model. It is a bounded finite-potential family, not a
claim of universal S1.
-/

namespace SymplecticStafford.Source

open Stafford38
open Stafford38.Evolution
open Stafford38.WeylIteratedEquivalence

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- Every finite potential in the old embedded `A_n` admits the literal
same-divisor certificate in the original presented `A_(n+1)`, with fixed
source the distinguished coordinate power. -/
theorem presentedWeyl_iterated_evolutionary
    (n r : ℕ) (hr : 0 < r) (terms : List (PresentedWeyl k n × ℕ))
    {d : PresentedWeyl k (n + 1)}
    (hd : d = presentedMomentum k n ^ r -
      potentialSum (presentedCoordinate k n)
        (terms.map fun t =>
          (previousWeylEmbedding k n t.1, t.2))) :
    ∃ R S : PresentedWeyl k (n + 1),
      1 = d * R + presentedCoordinate k n ^ r * d * S := by
  let lifted : List (PresentedWeyl k (n + 1) × ℕ) :=
    terms.map fun t => (previousWeylEmbedding k n t.1, t.2)
  have hx : ∀ t ∈ lifted,
      t.1 * presentedCoordinate k n =
        presentedCoordinate k n * t.1 := by
    rintro t ht
    rcases List.mem_map.mp ht with ⟨⟨b, j⟩, _, rfl⟩
    exact (presentedCoordinate_commutes_previous k n b).symm
  have hp : ∀ t ∈ lifted,
      t.1 * presentedMomentum k n =
        presentedMomentum k n * t.1 := by
    rintro t ht
    rcases List.mem_map.mp ht with ⟨⟨b, j⟩, _, rfl⟩
    exact (presentedMomentum_commutes_previous k n b).symm
  have hw : presentedMomentum k n * presentedCoordinate k n =
      presentedCoordinate k n * presentedMomentum k n + 1 :=
    presentedMomentum_mul_coordinate k n
  obtain ⟨R, S, h⟩ := evolutionaryCorollary
    (D := PresentedWeyl k (n + 1))
    (x := presentedCoordinate k n) (p := presentedMomentum k n)
    k hw hr lifted hx hp (by simpa [lifted] using hd)
  exact ⟨R, S, h⟩

#print axioms presentedWeyl_iterated_evolutionary

end SymplecticStafford.Source
