import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Noetherian.Basic
import SymplecticStafford.FiniteLength.MinimalPrimeLength

/-!
# Good-module to local finite-length bridge

This file records the exact algebraic bridge available before the filtered
localization theorem.  A finite good module may be sent onto a local model
over a (possibly different) Noetherian ring by a semilinear map.  If the
local model is Artinian, Mathlib then supplies its finite composition length.

The Artinian field is intentional: it is the local finite-length conclusion
that the characteristic-support and minimal-prime argument still has to
construct.  No localization, spectrum, or associated-graded theorem is
hidden in this bridge.
-/

namespace SymplecticStafford.FiniteLength

universe u v w z

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type z}
variable [Semiring R] [Ring S]
variable [AddCommMonoid M] [Module R M]
variable [AddCommGroup N] [Module S N]
variable {σ : R →+* S}

/-- A local model reached from a finite (good) module.

The support labels are retained so that this certificate can be attached to a
minimal homogeneous characteristic point later.  They do not themselves
provide a spectrum or a minimal-prime construction.
-/
structure GoodLocalMinimalPrimeInput (σ : R →+* S) (α : Type*) [Preorder α] where
  good_finite : Module.Finite R M
  support : Set α
  minimalPoint : MinimalSupportPoint support
  source : M →ₛₗ[σ] N
  source_surjective : Function.Surjective source
  local_noetherian_ring : IsNoetherianRing S
  local_artinian : IsArtinian S N

theorem local_module_finite_of_goodLocalMinimalPrime
    {α : Type*} [Preorder α]
    (W : GoodLocalMinimalPrimeInput (R := R) (S := S) (M := M) (N := N)
      (σ := σ) α) :
    Module.Finite S N := by
  letI : Module.Finite R M := W.good_finite
  exact Module.Finite.of_surjective W.source W.source_surjective

/-- The local Noetherian module property is derived from finite generation and
the local Noetherian-ring hypothesis, rather than supplied independently. -/
theorem local_module_noetherian_of_goodLocalMinimalPrime
    {α : Type*} [Preorder α]
    (W : GoodLocalMinimalPrimeInput (R := R) (S := S) (M := M) (N := N)
      (σ := σ) α) :
    IsNoetherian S N := by
  letI : IsNoetherianRing S := W.local_noetherian_ring
  letI : Module.Finite S N := local_module_finite_of_goodLocalMinimalPrime W
  infer_instance

/-- M05's finite local composition-length endpoint under explicit local
Noetherian and Artinian inputs. -/
theorem local_isFiniteLength_of_goodLocalMinimalPrime
    {α : Type*} [Preorder α]
    (W : GoodLocalMinimalPrimeInput (R := R) (S := S) (M := M) (N := N)
      (σ := σ) α) :
    IsFiniteLength S N := by
  letI : IsNoetherian S N := local_module_noetherian_of_goodLocalMinimalPrime W
  letI : IsArtinian S N := W.local_artinian
  exact (isFiniteLength_iff_isNoetherian_isArtinian).2
    ⟨inferInstance, inferInstance⟩

theorem local_module_length_ne_top_of_goodLocalMinimalPrime
    {α : Type*} [Preorder α]
    (W : GoodLocalMinimalPrimeInput (R := R) (S := S) (M := M) (N := N)
      (σ := σ) α) :
    Module.length S N ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (local_isFiniteLength_of_goodLocalMinimalPrime W)

end

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.local_module_finite_of_goodLocalMinimalPrime
#print axioms SymplecticStafford.FiniteLength.local_module_noetherian_of_goodLocalMinimalPrime
#print axioms SymplecticStafford.FiniteLength.local_isFiniteLength_of_goodLocalMinimalPrime
#print axioms SymplecticStafford.FiniteLength.local_module_length_ne_top_of_goodLocalMinimalPrime
