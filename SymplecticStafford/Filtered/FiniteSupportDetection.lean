import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Defs

/-!
# Finite associated-top detection

This file isolates the elementary finite-filtration step used by the M04/M05
boundary.  A descending filtration is indexed by natural numbers only for a
finite cutoff; a nonzero element has a maximal layer in which it occurs, and
the class at the next quotient boundary is therefore nonzero.

The filtration and separatedness data are explicit hypotheses.  In
particular, this does not construct a Rees algebra, a good filtration, a
characteristic support, a localization, or a minimal-prime composition
series.  The predicate `AssociatedTopNonzero` is the exact membership
criterion for a nonzero class in a putative layer quotient; no quotient object
is silently introduced.
-/

namespace SymplecticStafford.Filtered

universe u

variable {M : Type u} [Zero M]

/-- A finite descending filtration with a separated terminal layer. -/
structure FiniteDescendingFiltration (M : Type u) [Zero M] where
  height : Nat
  carrier : Nat → Set M
  zero_mem : ∀ k, 0 ∈ carrier k
  exhaustive : ∀ x : M, x ∈ carrier 0
  descending : ∀ k, carrier (k + 1) ⊆ carrier k
  separated : ∀ {x : M}, x ∈ carrier height → x = 0

namespace FiniteDescendingFiltration

variable (F : FiniteDescendingFiltration M)

/-- The nonzero-class criterion at layer `k`.

An element is in layer `k` but not in the next layer.  When an actual
quotient is later constructed, this is precisely the condition that its
class modulo the next layer is nonzero.
-/
def AssociatedTopNonzero (x : M) (k : Nat) : Prop :=
  x ∈ F.carrier k ∧ x ∉ F.carrier (k + 1)

theorem associatedTop_mem
    {x : M} {k : Nat} (h : F.AssociatedTopNonzero x k) :
    x ∈ F.carrier k := h.1

theorem associatedTop_not_mem_next
    {x : M} {k : Nat} (h : F.AssociatedTopNonzero x k) :
    x ∉ F.carrier (k + 1) := h.2

/-- Every nonzero element has a finite maximal layer with a nonzero next-layer
class.  No assumption that the filtration degrees are nonnegative beyond the
finite natural cutoff is used in the argument; an independently supplied
integer weight may be attached to the layers later.
-/
theorem exists_associatedTopNonzero
    {x : M} (hx : x ≠ 0) :
    ∃ k, k < F.height ∧ F.AssociatedTopNonzero x k := by
  classical
  let support : Finset Nat :=
    (Finset.range (F.height + 1)).filter (fun k => x ∈ F.carrier k)
  have hsupport : support.Nonempty := by
    refine ⟨0, ?_⟩
    exact Finset.mem_filter.mpr ⟨by simp, F.exhaustive x⟩
  let k : Nat := support.max' hsupport
  have hk_support : k ∈ support := Finset.max'_mem support hsupport
  have hxk : x ∈ F.carrier k := (Finset.mem_filter.mp hk_support).2
  have hk_range : k ∈ Finset.range (F.height + 1) :=
    (Finset.mem_filter.mp hk_support).1
  have hk_le : k ≤ F.height := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_range)
  have hk_ne : k ≠ F.height := by
    intro hkeq
    apply hx
    exact F.separated (hkeq ▸ hxk)
  have hk_lt : k < F.height := lt_of_le_of_ne hk_le hk_ne
  have hknext : x ∉ F.carrier (k + 1) := by
    intro hnext
    have hnext_range : k + 1 ∈ Finset.range (F.height + 1) := by
      apply Finset.mem_range.mpr
      simpa [Nat.succ_eq_add_one] using Nat.succ_lt_succ hk_lt
    have hnext_support : k + 1 ∈ support :=
      Finset.mem_filter.mpr ⟨hnext_range, hnext⟩
    have hle : k + 1 ≤ k := by
      simpa [k] using (Finset.le_max' support (k + 1) hnext_support)
    exact (Nat.not_succ_le_self k) (by simpa [Nat.succ_eq_add_one] using hle)
  exact ⟨k, hk_lt, ⟨hxk, hknext⟩⟩

/-- A nonzero element is detected by at least one finite associated layer. -/
theorem exists_detecting_layer
    {x : M} (hx : x ≠ 0) :
    ∃ k, k < F.height ∧ x ∈ F.carrier k ∧ x ∉ F.carrier (k + 1) := by
  rcases F.exists_associatedTopNonzero hx with ⟨k, hk, htop⟩
  exact ⟨k, hk, htop.1, htop.2⟩

end FiniteDescendingFiltration

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FiniteDescendingFiltration.exists_associatedTopNonzero
#print axioms SymplecticStafford.Filtered.FiniteDescendingFiltration.exists_detecting_layer
