import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Algebra.Opposite

/-!
# The affine same-divisor theorem (Symplectic Stafford, Target theorem A)

Let `k` be a field of characteristic zero and `U` a simple, infinite-dimensional
`k`-algebra with an exhaustive, nonnegative, multiplicative filtration
`F₀U ⊆ F₁U ⊆ ⋯` by finite-dimensional subspaces with `F₀U = k`, whose
associated graded ring is a commutative affine domain `G` of finite Krull
dimension.  Then for all nonzero `d, a ∈ U` and every `B ∈ U` there are
`H, R, S ∈ U` with

  `1 = d R + (B + H a) d S`.

The associated graded ring is encoded by a commutative `ℕ`-graded `k`-algebra
`G = ⨁ₙ 𝒜 n` together with `k`-linear symbol maps `gr n : FₙU → 𝒜 n` that are
surjective, have kernel `Fₙ₋₁U` (kernel `0` for `n = 0`) and are
multiplicative; equivalently `FₙU / Fₙ₋₁U ≃ 𝒜 n` and `gr U ≃ G` as graded rings.

This file is independent of the project library.  The single `sorry` is the
challenge hole filled by `Solution.lean`.
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

/-- The compared challenge theorem. -/
theorem universalStatement : AffineSameDivisorStatement.{u, v, w} := by
  sorry

end SymplecticStaffordChallenge
