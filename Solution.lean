import SymplecticStafford.FiniteLength.FiniteCentralDivisionLLD

/-!
# Solution of the finite central division-pencil challenge

The definition below is repeated independently from `Challenge.lean` for the
statement comparator. The proof applies the project's determinant-free
finite-spectrum theorem and does not import the challenge module.
-/

namespace SymplecticStaffordChallenge

universe u v w

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

theorem universalStatement : FiniteCentralPencilStatement := by
  intro K E V ι _ _ _ _ _ _ _ _ _ ιmap central_coeff central_embedding
    central_vector x y hx
  exact
    SymplecticStafford.FiniteLength.finite_bad_of_finite_central_division_pencil_spectrum
      ιmap central_coeff central_embedding central_vector x y hx

end SymplecticStaffordChallenge
