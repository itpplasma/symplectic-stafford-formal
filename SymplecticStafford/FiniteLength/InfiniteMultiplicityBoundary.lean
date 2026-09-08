import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The finite-generation boundary in the minimal-prime length step

M05 concerns a *finite good* module.  A support statement by itself is not a
finite-length statement: even over a field, countably many copies of the
residue module have the same one-point support but infinite composition
length.  The standard basis of `ℕ →₀ ℚ` gives a compact kernel-checked model
of this obstruction.

The result below is deliberately a boundary, not a claim about the paper's
finite good modules.  It records exactly why finite generation (or an
equivalent good-filtration input) must be proved before invoking minimal-prime
local length.
-/

namespace SymplecticStafford.FiniteLength

open scoped BigOperators

theorem finsupp_nat_rat_not_moduleFinite :
    ¬ Module.Finite ℚ (ℕ →₀ ℚ) := by
  intro hfinite
  letI : Module.Finite ℚ (ℕ →₀ ℚ) := hfinite
  have hli : LinearIndependent ℚ (fun n : ℕ => Finsupp.single n (1 : ℚ)) :=
    Finsupp.linearIndependent_single_one ℚ ℕ
  haveI : Finite ℕ := LinearIndependent.finite hli
  exact not_finite ℕ

theorem finsupp_nat_rat_not_isFiniteLength :
    ¬ IsFiniteLength ℚ (ℕ →₀ ℚ) := by
  intro hlength
  have hnoetherian : IsNoetherian ℚ (ℕ →₀ ℚ) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).1
  letI : IsNoetherian ℚ (ℕ →₀ ℚ) := hnoetherian
  exact finsupp_nat_rat_not_moduleFinite inferInstance

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.finsupp_nat_rat_not_moduleFinite
#print axioms SymplecticStafford.FiniteLength.finsupp_nat_rat_not_isFiniteLength
