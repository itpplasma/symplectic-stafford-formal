import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A sufficient strictness contract for filtered chains

The strict filtered-chain implication needed by the proposed Part I.5 repair
is not a consequence of exhaustiveness and separatedness alone: the adjacent
`GradedLengthFilteredChainBoundary` gives an unbounded-below counterexample.
This file records a small sufficient replacement.  For a filtration indexed
by `ℕ`, with bottom layer zero, monotonicity and exhaustiveness let one peel a
representative one layer at a time.  If every layer of `B` has a representative
in `A` modulo the preceding layer, then `A = B`; consequently a strict
inclusion must be visible in some associated layer.

This is a conditional contract, not an assertion that the localized `T_p`
filtration has a bounded-below reindexing.  Establishing an equivalent
Zariskian/strict Rees hypothesis for the actual localization remains a
separate obligation.
-/

namespace SymplecticStafford.FiniteLength

universe u v

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

structure NatFiltration where
  carrier : ℕ → Submodule R M
  mono : Monotone carrier
  exhaustive : ∀ x : M, ∃ n, x ∈ carrier n
  bottom : carrier 0 = ⊥

def previousLayer (F : NatFiltration (R := R) (M := M)) (n : ℕ) : Submodule R M :=
  match n with
  | 0 => ⊥
  | n + 1 => F.carrier n

/-!
Every layer of `B` is represented in `A`, with the error in the preceding
layer.  This is the quotient-free formulation of surjectivity on associated
layers for induced filtrations.
-/
def natLayerSurjective (F : NatFiltration (R := R) (M := M))
    (A B : Submodule R M) : Prop :=
  A ≤ B ∧ ∀ n : ℕ, ∀ x ∈ B, x ∈ F.carrier n →
    ∃ y, y ∈ A ∧ y ∈ F.carrier n ∧ x - y ∈ previousLayer F n

theorem layerSurjective_eq_of_boundedBelow
    (F : NatFiltration (R := R) (M := M))
    {A B : Submodule R M} (h : natLayerSurjective F A B) : A = B := by
  rcases h with ⟨hAB, hsurj⟩
  apply le_antisymm hAB
  intro x hx
  obtain ⟨n, hxn⟩ := F.exhaustive x
  induction n generalizing x with
  | zero =>
      obtain ⟨y, hyA, hyF, hdiff⟩ := hsurj 0 x hx hxn
      have hdiff0 : x - y = 0 := by
        rw [show previousLayer F 0 = ⊥ by rfl] at hdiff
        exact (Submodule.mem_bot R).mp hdiff
      rw [sub_eq_zero.mp hdiff0]
      exact hyA
  | succ n ih =>
      obtain ⟨y, hyA, hyF, hdiff⟩ := hsurj (n + 1) x hx hxn
      have hdiffB : x - y ∈ B := B.sub_mem hx (hAB hyA)
      have hdiffF : x - y ∈ F.carrier n := by
        simpa [previousLayer] using hdiff
      have hxyA : x - y ∈ A := ih hdiffB hdiffF
      have hsum : (x - y) + y ∈ A := A.add_mem hxyA hyA
      simpa [sub_add_cancel] using hsum

theorem strict_inclusion_has_strict_layer
    (F : NatFiltration (R := R) (M := M))
    {A B : Submodule R M} (hAB : A ≤ B) (hne : A ≠ B) :
    ¬ (∀ n : ℕ, ∀ x ∈ B, x ∈ F.carrier n →
      ∃ y, y ∈ A ∧ y ∈ F.carrier n ∧ x - y ∈ previousLayer F n) := by
  intro hsurj
  apply hne
  exact layerSurjective_eq_of_boundedBelow F ⟨hAB, hsurj⟩

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.layerSurjective_eq_of_boundedBelow
#print axioms SymplecticStafford.FiniteLength.strict_inclusion_has_strict_layer
