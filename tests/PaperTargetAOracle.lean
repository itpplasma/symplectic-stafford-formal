import SymplecticStafford.Paper

/-!
# Independent consumers of the formal Target A development

These examples use the main theorems in forms not stated in the library:
the plain same-divisor identity (`B = 0`, `a = 1`), its opposite-handed
version, the free-ring identities of Remark 5.2 in a concrete matrix ring,
and Corollary 4.8 in a concrete rational vector space.
-/

namespace SymplecticStaffordTest

open SymplecticStafford.Paper

/-- The same-divisor identity `1 = d R + F d S` (Stafford's 3.8 shape). -/
example {k U G : Type*} [Field k] [Infinite k] [Ring U] [Algebra k U] [IsSimpleRing U]
    [CommRing G] [IsDomain G] [IsNoetherianRing G] [Algebra k G]
    {𝒜 : ℕ → Submodule k G} [GradedAlgebra 𝒜] (D : FilteredAlgebraData k U G 𝒜)
    (hdim : ringKrullDim G < ⊤) (d : U) (hd : d ≠ 0) :
    ∃ F R S : U, 1 = d * R + F * d * S := by
  obtain ⟨H, R, S, h⟩ := D.targetA hdim d 1 hd one_ne_zero 0
  exact ⟨H, R, S, by simpa using h⟩

/-- Both handedness versions hold simultaneously. -/
example {k U G : Type*} [Field k] [Infinite k] [Ring U] [Algebra k U] [IsSimpleRing U]
    [CommRing G] [IsDomain G] [IsNoetherianRing G] [Algebra k G]
    {𝒜 : ℕ → Submodule k G} [GradedAlgebra 𝒜] (D : FilteredAlgebraData k U G 𝒜)
    (hdim : ringKrullDim G < ⊤) (d : U) (hd : d ≠ 0) :
    (∃ F R S : U, 1 = d * R + F * d * S) ∧ ∃ F R S : U, 1 = R * d + S * d * F := by
  refine ⟨?_, D.targetA_left hdim d hd⟩
  obtain ⟨H, R, S, h⟩ := D.targetA hdim d 1 hd one_ne_zero 0
  exact ⟨H, R, S, by simpa using h⟩

/-- Remark 5.2 in the noncommutative ring of `2 × 2` rational matrices. -/
example (d a₀ v b₀ C₀ z₀ w L₀ : Matrix (Fin 2) (Fin 2) ℚ) :
    d * (a₀ + C₀ * z₀ * w * b₀) + v * (b₀ - L₀ * z₀ * w * b₀) - 1 =
      (d * a₀ + v * b₀ - 1) + (d * C₀ - v * L₀) * z₀ * w * b₀ :=
  FilteredAlgebraData.remark52_const d a₀ v b₀ C₀ z₀ w L₀

/-- Corollary 4.8 for the generator `1` of `ℚ` over itself. -/
example (y : ℚ) : {l : ℚ | Submodule.span ℚ {(1 : ℚ) + algebraMap ℚ ℚ l • y} ≠ ⊤}.Finite :=
  generator_pencil_finite (k := ℚ) (A := ℚ) (by simp) y

#print axioms FilteredAlgebraData.targetA
#print axioms FilteredAlgebraData.targetA_left
#print axioms Test.exists_source

end SymplecticStaffordTest
