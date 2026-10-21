module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Length

@[expose] public section

/-!
# Conditional minimal-prime finite-length infrastructure

This module isolates the formal part of the minimal-support step.  A genuine
filtered/Rees localization has to supply the local module, its support point,
and the Noetherian/Artinian hypotheses.  Once those hypotheses are supplied,
Mathlib's composition-series theorem gives finite length and the usual
submodule/quotient closure.  No characteristic-support construction or
localization theorem is asserted here.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section Composition

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- A compact name for the composition-series endpoint used by M05. -/
def HasCompositionSeries : Prop :=
  ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤

theorem isFiniteLength_of_hasCompositionSeries
    (h : HasCompositionSeries (R := R) (M := M)) :
    IsFiniteLength R M :=
  isFiniteLength_of_exists_compositionSeries h

theorem hasCompositionSeries_of_isFiniteLength
    (h : IsFiniteLength R M) :
    HasCompositionSeries (R := R) (M := M) :=
  isFiniteLength_iff_exists_compositionSeries.mp h

theorem isFiniteLength_submodule_of_isFiniteLength
    (h : IsFiniteLength R M) (N : Submodule R M) :
    IsFiniteLength R N := by
  apply IsFiniteLength.of_injective (f := N.subtype) h
  intro x y hxy
  exact Subtype.ext hxy

theorem isFiniteLength_quotient_of_isFiniteLength
    (h : IsFiniteLength R M) (N : Submodule R M) :
    IsFiniteLength R (M ⧸ N) := by
  exact IsFiniteLength.of_surjective h (Submodule.mkQ_surjective N)

theorem moduleLength_ne_top_of_isFiniteLength
    (h : IsFiniteLength R M) : Module.length R M ≠ ⊤ :=
  Module.length_ne_top_iff.mpr h

end Composition

section MinimalSupport

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {α : Type v} [Preorder α]

/-!
`MinimalSupportPoint` records only the order-theoretic meaning of a minimal
point.  The type `α` may later be instantiated by homogeneous characteristic
primes, but this file does not claim that such a support or order exists.
-/
structure MinimalSupportPoint (support : Set α) where
  point : α
  mem_support : point ∈ support
  minimal : ∀ q, q ∈ support → q ≤ point → point ≤ q

theorem minimalSupportPoint_le_of_mem
    {support : Set α} (p : MinimalSupportPoint support)
    {q : α} (hq : q ∈ support) (hqp : q ≤ p.point) :
    p.point ≤ q :=
  p.minimal q hq hqp

variable {N : Type w} [AddCommGroup N] [Module R N]

/-!
The local input expected from the filtered/Rees lane.  `source` and
`surjective` make explicit that `N` is a local model obtained from the good
module `M`; `noetherian` and `artinian` are hypotheses about that model, not
conclusions of a formal localization shell.
-/
structure MinimalPrimeLocalInput (R : Type u) (M : Type v) (N : Type w)
    [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (α : Type v) [Preorder α] where
  good_finite : Module.Finite R M
  support : Set α
  minimalPoint : MinimalSupportPoint support
  source : M →ₗ[R] N
  source_surjective : Function.Surjective source
  local_noetherian : IsNoetherian R N
  local_artinian : IsArtinian R N

/- A local model of an arbitrary good module has finite length at a supplied
minimal support point.  The proof is exactly the Noetherian+Artinian
characterization; no prime-local construction is hidden in the theorem. -/
theorem local_isFiniteLength_of_minimalPrime
    (W : MinimalPrimeLocalInput R M N α) :
    IsFiniteLength R N := by
  letI : IsNoetherian R N := W.local_noetherian
  letI : IsArtinian R N := W.local_artinian
  exact (isFiniteLength_iff_isNoetherian_isArtinian).2 ⟨inferInstance, inferInstance⟩

theorem local_module_finite_of_minimalPrime
    (W : MinimalPrimeLocalInput R M N α) :
    Module.Finite R N := by
  letI : Module.Finite R M := W.good_finite
  exact Module.Finite.of_surjective W.source W.source_surjective

theorem local_module_length_ne_top_of_minimalPrime
    (W : MinimalPrimeLocalInput R M N α) :
    Module.length R N ≠ ⊤ :=
  moduleLength_ne_top_of_isFiniteLength (local_isFiniteLength_of_minimalPrime W)

end MinimalSupport

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.isFiniteLength_submodule_of_isFiniteLength
#print axioms SymplecticStafford.FiniteLength.isFiniteLength_quotient_of_isFiniteLength
#print axioms SymplecticStafford.FiniteLength.local_isFiniteLength_of_minimalPrime
#print axioms SymplecticStafford.FiniteLength.local_module_finite_of_minimalPrime
