import AlgebraicAnalysis.RingTheory.TwoGeneratorIdentity
import AlgebraicAnalysis.Module.MinimalPrimeFiniteLengthLocalization
import Stafford38.LocalizationCorollaries

/-!
# Pinned dependency bridge

This module is a deliberately small compile-time bridge to the current pinned
`algebraic-analysis` and `stafford38-formal` releases.  It exposes the two
dependency results which are reusable in the symplectic-Stafford proof:

* right-unit clearing transports the ordered two-generator identity; and
* a finite commutative module has a nonzero finite-length localization at a
  minimal annihilator prime.

The Stafford38 endpoint is exported only in its actual Weyl-algebra scope.
None of these declarations turns a general filtered quantum algebra into a
Weyl algebra, constructs the missing algebraic chart, or supplies an original
`U` source.  Those obligations therefore remain visible in the local M01--M06
interfaces.
-/

namespace SymplecticStafford.Dependency

universe u v

section Identity

variable {R : Type u} {L : Type v} [Ring R] [Ring L]

/-- Reusable right-denominator transport from AlgebraicAnalysis, retaining
the exact multiplication order of the project target. -/
theorem twoGeneratorIdentity_of_rightUnitClearing
    {f : R →+* L}
    (hR : AlgebraicAnalysis.TwoGeneratorIdentity R)
    (hclear : ∀ q : L, q ≠ 0 →
      ∃ a s : R, IsUnit (f s) ∧ q * f s = f a) :
    AlgebraicAnalysis.TwoGeneratorIdentity L :=
  AlgebraicAnalysis.TwoGeneratorIdentity.of_rightUnitClearing hR hclear

end Identity

section MinimalPrime

variable {A : Type u} [CommRing A]
variable {G : Type v} [AddCommGroup G] [Module A G]

/-- Reusable M05 endpoint from AlgebraicAnalysis, with the actual canonical
`Localization`/`LocalizedModule` pair. -/
theorem minimalPrime_nontrivial_and_finiteLength
    [IsNoetherianRing A] [Module.Finite A G]
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Module.annihilator A G).minimalPrimes) :
    Nontrivial (LocalizedModule P.primeCompl G) ∧
      IsFiniteLength (Localization P.primeCompl)
        (LocalizedModule P.primeCompl G) :=
  AlgebraicAnalysis.MinimalPrimeFiniteLengthLocalization.localizedModule_nontrivial_and_isFiniteLength
    P hP

end MinimalPrime

section Stafford38

variable {R : Type u} [Ring R] {S : Submonoid R}

/-- Stafford38's right-Ore transport is available at the same generic scope
as the neutral AlgebraicAnalysis theorem.  The required identity on `R` is
still an explicit premise. -/
theorem stafford38_rightOre_localization
    [OreLocalization.OreSet
      (Stafford38.LocalizationCorollaries.oppositeSubmonoid S)]
    (hR : AlgebraicAnalysis.TwoGeneratorIdentity R) :
    AlgebraicAnalysis.TwoGeneratorIdentity
      (Stafford38.LocalizationCorollaries.RightOreLocalization R S) :=
  Stafford38.LocalizationCorollaries.s38_rightOreLocalization hR

end Stafford38

end SymplecticStafford.Dependency

#print axioms SymplecticStafford.Dependency.twoGeneratorIdentity_of_rightUnitClearing
#print axioms SymplecticStafford.Dependency.minimalPrime_nontrivial_and_finiteLength
#print axioms SymplecticStafford.Dependency.stafford38_rightOre_localization
