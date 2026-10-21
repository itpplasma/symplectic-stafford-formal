module

public import SymplecticStafford.Paper.Induction

@[expose] public section

/-!
# Solution of the affine same-divisor challenge

The structure and statement below are repeated independently from
`Challenge.lean` for the statement comparator; this file does not import the
challenge module.  The proof transfers the data to the project's
`SymplecticStafford.Paper.FilteredAlgebraData` and applies
`FilteredAlgebraData.targetA`, the formalization of the controlled codimension
induction of the manuscript.
-/

namespace SymplecticStaffordChallenge

universe u v w

/-- The standing filtered-algebra hypotheses, with the associated graded ring
identified with `G = ⨁ 𝒜 n`. -/
structure FilteredAlgebraData (k U G : Type*) [Field k] [Ring U] [Algebra k U]
    [CommRing G] [Algebra k G] (𝒜 : ℕ → Submodule k G) [GradedAlgebra 𝒜] where
  /-- The filtration pieces `F n = Fₙ U`. -/
  F : ℕ → Submodule k U
  mono : Monotone F
  exhaustive : ∀ u : U, ∃ n, u ∈ F n
  /-- `F₀U = k`. -/
  zero_piece : F 0 = LinearMap.range (Algebra.linearMap k U)
  finiteDimensional : ∀ n, FiniteDimensional k (F n)
  mul_mem : ∀ {i j : ℕ} {u v : U}, u ∈ F i → v ∈ F j → u * v ∈ F (i + j)
  /-- The symbol maps `Fₙ U → Fₙ U / Fₙ₋₁ U ≃ 𝒜 n`. -/
  gr : ∀ n, F n →ₗ[k] 𝒜 n
  gr_surjective : ∀ n, Function.Surjective (gr n)
  gr_zero_eq_zero_iff : ∀ x : F 0, gr 0 x = 0 ↔ x = 0
  gr_succ_eq_zero_iff : ∀ n (x : F (n + 1)), gr (n + 1) x = 0 ↔ (x : U) ∈ F n
  gr_mul : ∀ {i j : ℕ} (x : F i) (y : F j),
    ((gr (i + j) ⟨x * y, mul_mem x.2 y.2⟩ : 𝒜 (i + j)) : G) = (gr i x : G) * (gr j y : G)

/-- Target theorem A: the affine same-divisor identity in the original algebra. -/
def AffineSameDivisorStatement : Prop :=
  ∀ (k : Type u) (U : Type v) (G : Type w) [Field k] [CharZero k] [Ring U] [Algebra k U]
    [IsSimpleRing U] [CommRing G] [IsDomain G] [Algebra k G] [Algebra.FiniteType k G]
    (𝒜 : ℕ → Submodule k G) [GradedAlgebra 𝒜],
    ¬ FiniteDimensional k U → ringKrullDim G < ⊤ → FilteredAlgebraData k U G 𝒜 →
      ∀ d a : U, d ≠ 0 → a ≠ 0 → ∀ B : U, ∃ H R S : U, 1 = d * R + (B + H * a) * d * S

theorem universalStatement : AffineSameDivisorStatement.{u, v, w} := by
  intro k U G _ _ _ _ _ _ _ _ _ 𝒜 _ _ hdim D d a hd ha B
  have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  have : IsNoetherianRing G := Algebra.FiniteType.isNoetherianRing k G
  let D' : SymplecticStafford.Paper.FilteredAlgebraData k U G 𝒜 :=
    { F := D.F
      mono := D.mono
      exhaustive := D.exhaustive
      zero_piece := D.zero_piece
      finiteDimensional := D.finiteDimensional
      mul_mem := D.mul_mem
      gr := D.gr
      gr_surjective := D.gr_surjective
      gr_zero_eq_zero_iff := D.gr_zero_eq_zero_iff
      gr_succ_eq_zero_iff := D.gr_succ_eq_zero_iff
      gr_mul := D.gr_mul }
  exact D'.targetA hdim d a hd ha B

end SymplecticStaffordChallenge
