import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite central division-pencil challenge

This Palomar-shaped challenge asks for the finite bad-parameter theorem for a
finite affine pencil over a division ring that is finite-dimensional over its
central field. It is independent of the project library. The single `sorry`
is the challenge hole filled by `Solution.lean`.
-/

namespace SymplecticStaffordChallenge

universe u v w

/-- The exact finite-central division-pencil statement submitted for comparison. -/
def FiniteCentralPencilStatement : Prop :=
  ∀ (K : Type u) (E : Type v) (V : Type w) (ι : Type*)
    [Field K] [Infinite K] [DivisionRing E]
    [AddCommGroup V] [Module K V] [Module E V] [Module K E]
    [FiniteDimensional K E] [Fintype ι]
    (ιmap : K →+* E)
    (central_coeff : ∀ (k : K) (e : E), k • e = ιmap k * e)
    (central_embedding : ∀ (k : K) (e : E), ιmap k * e = e * ιmap k)
    (central_vector : ∀ (k : K) (x : V), k • x = (ιmap k) • x)
    (x y : ι → V),
    LinearIndependent E x →
      Set.Finite {z : K | ¬ LinearIndependent E
        (fun i => x i + (ιmap z) • y i)}

/-- The compared challenge theorem. -/
theorem universalStatement : FiniteCentralPencilStatement := by
  sorry

end SymplecticStaffordChallenge
