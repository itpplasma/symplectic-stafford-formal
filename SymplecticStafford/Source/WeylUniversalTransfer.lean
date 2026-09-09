import Stafford38.FoundationClosure
import SymplecticStafford.Semantics.S1Consequences
import SymplecticStafford.Semantics.Contract

/-!
# Transfer of the all-rank Weyl endpoint through an actual algebra equivalence

`Stafford38.universalStatement` proves the ordered same-divisor identity in
the presented Weyl algebra.  This file records the exact transport to any
ring which is *actually* algebra-isomorphic to that Weyl algebra.  The
equivalence is an input, so this is a concrete family closure and not an
algebraization theorem for the general filtered class.
-/

namespace SymplecticStafford.Source

universe u v

variable {k : Type u} [Field k] [CharZero k]
variable {U : Type v} [Ring U] [Algebra k U]

theorem sameDivisor_of_weylAlg_algEquiv
    {n : ℕ} (e : Stafford38.WeylAlg k n ≃ₐ[k] U) :
    SymplecticStafford.SameDivisorS1 (R := U) := by
  intro d hd
  let d₀ : Stafford38.WeylAlg k n := e.symm d
  have hd₀ : d₀ ≠ 0 := by
    intro hzero
    apply hd
    have hzero' : e d₀ = 0 := by
      simpa using congrArg e hzero
    simpa [d₀] using hzero'
  obtain ⟨F₀, R₀, S₀, h₀⟩ := Stafford38.universalStatement k n d₀ hd₀
  refine ⟨e F₀, e R₀, e S₀, ?_⟩
  have h := congrArg e h₀
  have hmap : (1 : U) = e d₀ * e R₀ + (e F₀ * e d₀) * e S₀ := by
    simpa only [map_one, map_add, map_mul] using h
  simpa [d₀] using hmap

theorem originalSameDivisor_of_weylAlg_algEquiv
    {n : ℕ} (e : Stafford38.WeylAlg k n ≃ₐ[k] U) :
    SymplecticStafford.OriginalSameDivisor U :=
  sameDivisor_of_weylAlg_algEquiv e

end SymplecticStafford.Source

#print axioms SymplecticStafford.Source.sameDivisor_of_weylAlg_algEquiv
#print axioms SymplecticStafford.Source.originalSameDivisor_of_weylAlg_algEquiv
