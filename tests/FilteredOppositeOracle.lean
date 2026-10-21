module

public import Mathlib.Algebra.Field.Rat
public import SymplecticStafford.Package.FilteredOpposite

@[expose] public section

/- Independent oracle for concrete opposite transport of the M01 filtered
algebra data.  The filtration is the exhaustive constant filtration on the
rational field, so every carrier and degree-zero statement is checked at the
actual opposite type. -/

namespace SymplecticStaffordTest.FilteredOpposite

open SymplecticStafford.Filtered
open MulOpposite

def rationalFiltration : AdditiveFilteredRingData ℚ where
  carrier _ := ⊤
  one_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; simp
  exhaustive := by intro a; exact ⟨0, by simp⟩

def rationalAlgebra : M01FilteredAlgebra ℚ ℚ where
  filtration := rationalFiltration
  central := by intro k a; exact mul_comm _ _
  degree_zero := by
    ext a
    constructor
    · intro ha
      exact ⟨a, by simp⟩
    · intro ha
      change a ∈ (⊤ : AddSubgroup ℚ)
      simp

def rationalOpposite := rationalAlgebra.opposite

example (n : ℕ) (x : ℚᵐᵒᵖ) :
    x ∈ rationalOpposite.filtration.carrier n := by
  change unop x ∈ (⊤ : AddSubgroup ℚ)
  simp

example (k : ℚ) (x : ℚᵐᵒᵖ) :
    algebraMap ℚ ℚᵐᵒᵖ k * x = x * algebraMap ℚ ℚᵐᵒᵖ k := by
  exact rationalOpposite.central k x

example :
    (rationalOpposite.filtration.carrier 0 : Set ℚᵐᵒᵖ) =
      Set.range (algebraMap ℚ ℚᵐᵒᵖ) :=
  rationalOpposite.degree_zero

end SymplecticStaffordTest.FilteredOpposite

#print axioms SymplecticStaffordTest.FilteredOpposite.rationalOpposite
