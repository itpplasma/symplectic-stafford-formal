import SymplecticStafford.Filtered.CharacteristicSupport
import SymplecticStafford.Induction.StrongPh
import Mathlib.Algebra.Polynomial.Roots

/-!
# Central-field support-removal obstruction

An actual finite filtered module supplies a genuine quotient support, but it
need not be a support of the source-dependent quotient `Q_F`.  This file
isolates the obstruction in the smallest form that still carries a central
field: the two-layer filtration of the underlying scalar module of any
nontrivial ambient ring has nonempty support independent of the source.  At
the same time the constant polynomial `1` has no exceptional scalar over an
infinite central field.  Therefore scalar avoidance cannot by itself imply
strict pencil support removal.

The result does not refute source-dependent removal for the paper's actual
quotients.  It identifies the missing local-module input: a theorem tying
the source `F` to the filtered quotient whose support is being removed.
-/

namespace SymplecticStafford.Induction

open SymplecticStafford.Filtered

universe u v

variable {K : Type v} [Field K] [Infinite K]
variable {U : Type u} [Ring U] [Nontrivial U] [Module K U]

/-- The simplest genuine finite filtered scalar module: the full module at
layer zero and zero from layer one onwards. -/
def twoLayerScalarModule : FiniteFilteredModule (R := K) (M := U) where
  height := 1
  carrier := fun n => if n = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro n
    by_cases hn : n = 0 <;> simp [hn]
  separated := by simp

/-- Its actual quotient support, deliberately indexed by a source that does
not occur in the filtered module. -/
def sourceIndependentActualSupport (_f : U) : Set (Fin (twoLayerScalarModule (K := K) (U := U)).height) :=
  (twoLayerScalarModule (K := K) (U := U)).QuotientSupport

theorem sourceIndependentActualSupport_nonempty :
    (sourceIndependentActualSupport (K := K) (U := U) 0).Nonempty := by
  apply (twoLayerScalarModule (K := K) (U := U)).quotientSupport_nonempty_of_exists_ne_zero
  exact ⟨1, one_ne_zero⟩

theorem sourceIndependentActualSupport_eq (f g : U) :
    sourceIndependentActualSupport (K := K) (U := U) f =
      sourceIndependentActualSupport (K := K) (U := U) g := rfl

noncomputable def constantAvoidancePolynomial (_ : Unit) : Polynomial K := 1

theorem constantAvoidancePolynomial_good (z : K) :
    (constantAvoidancePolynomial (K := K) ()).eval z ≠ 0 := by
  simp [constantAvoidancePolynomial]

/-- The strict-removal assertion that would be inferred from this support
alone, with an arbitrary central pencil parameter. -/
def SourceIndependentCentralPencilStrictRemoval
    (P : CentralParameters U K) : Prop :=
  ∀ old new : U, ∀ z : K,
    sourceIndependentActualSupport (K := K) (U := U)
        (pencilMember P old new z) ⊂
      sourceIndependentActualSupport (K := K) (U := U) old

theorem not_sourceIndependentCentralPencilStrictRemoval
    (P : CentralParameters U K) :
    ¬ SourceIndependentCentralPencilStrictRemoval (K := K) (U := U) P := by
  intro h
  exact ssubset_irrefl _ (h 0 0 0)

theorem actual_support_and_scalar_avoidance_do_not_supply_strict_removal
    (P : CentralParameters U K) :
    (sourceIndependentActualSupport (K := K) (U := U) 0).Nonempty ∧
      (∀ z : K, (constantAvoidancePolynomial (K := K) ()).eval z ≠ 0) ∧
      ¬ SourceIndependentCentralPencilStrictRemoval (K := K) (U := U) P := by
  exact ⟨sourceIndependentActualSupport_nonempty,
    constantAvoidancePolynomial_good,
    not_sourceIndependentCentralPencilStrictRemoval P⟩

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.twoLayerScalarModule
#print axioms SymplecticStafford.Induction.actual_support_and_scalar_avoidance_do_not_supply_strict_removal
