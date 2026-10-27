module

public import SymplecticStafford.Filtered.ReesAlgebra
public import Mathlib.Tactic.NormNum

@[expose] public section

/- Independent behavioral checks for the bounded Rees-like subobject. -/
namespace SymplecticStafford.Filtered.ReesAlgebraOracle

open Multiplicative

noncomputable section

def natFiltration : FiltrationData ℕ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def p : ReesAlgebra natFiltration :=
  ReesAlgebra.monomial natFiltration 2 7 (by simp [natFiltration])

def q : ReesAlgebra natFiltration :=
  ReesAlgebra.monomial natFiltration 3 11 (by simp [natFiltration])

example : ReesBounded natFiltration ((p : ReesPolynomial ℕ) + q) :=
  ReesBounded.add p.property q.property

example : ReesBounded natFiltration ((p : ReesPolynomial ℕ) * q) :=
  ReesBounded.mul p.property q.property

example : ReesAlgebra.degreeCoefficient natFiltration 2 p = 7 := by
  change (SkewPolynomial.monomial 2 7).coeff 2 = 7
  simp [SkewPolynomial.coeff_monomial]

example : ReesAlgebra.degreeCoefficient natFiltration 1 p = 0 := by
  change (SkewPolynomial.monomial 2 7).coeff 1 = 0
  simp [SkewPolynomial.coeff_monomial]

example :
    ReesAlgebra.degreeCoefficient natFiltration 2 (p + q) =
      ReesAlgebra.degreeCoefficient natFiltration 2 p +
        ReesAlgebra.degreeCoefficient natFiltration 2 q :=
  ReesAlgebra.degreeCoefficient_add natFiltration 2 p q

def term : ReesTerm natFiltration :=
  ⟨2, 13, by simp [natFiltration, HasDegreeAtMost]⟩

example :
    quotientMap natFiltration (ReesTerm.reindex term (n := 4) (by simp [term])) =
      quotientMap natFiltration term := by
  exact quotientMap_reindex natFiltration term (n := 4) (by simp [term])

example :
    ReesQuotient.value (quotientMap natFiltration term) = 13 := by
  exact quotientMap_value natFiltration term

end

end SymplecticStafford.Filtered.ReesAlgebraOracle
