import SymplecticStafford.Induction.StrongPh
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite-test retention for the two-call successor interface

This module isolates the bookkeeping needed by M09--M10.  A successor proof
has two calls at a lower index.  The local tests passed to those calls may be
different lists (for example, an auxiliary divisor changes the local
coordinates), so a carried test list is related to each call by an explicit
inclusion and an explicit pass predicate.  No transport of a test between
different divisors is inferred here.

The old/new component split and the integer defect calculation are likewise
separate contracts.  In particular, the arithmetic theorem below consumes
the asserted common-defect formula; it does not prove support union, scalar
avoidance, a base case, a source producer, or a universal `P_h` theorem.
-/

namespace SymplecticStafford.Induction

universe u v w

/-! ## Finite-list bookkeeping -/

variable {α : Type u}

/-- Every member of the first finite list is retained in the second list. -/
def ListCarried (xs ys : List α) : Prop :=
  ∀ ⦃x : α⦄, x ∈ xs → x ∈ ys

theorem listCarried_refl (xs : List α) : ListCarried xs xs := by
  intro x hx
  exact hx

theorem listCarried_trans {xs ys zs : List α}
    (hxy : ListCarried xs ys) (hyz : ListCarried ys zs) :
    ListCarried xs zs := by
  intro x hx
  exact hyz (hxy hx)

theorem listCarried_cons_left {x : α} {xs ys : List α}
    (hx : x ∈ ys) (hxy : ListCarried xs ys) :
    ListCarried (x :: xs) ys := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hxy hy

theorem all_admissible_mono
    {δ : Type v} {Adm : δ → α → Prop}
    {d : δ} {xs ys : List α}
    (hys : ∀ x, x ∈ ys → Adm d x)
    (hxy : ListCarried xs ys) :
    ∀ x, x ∈ xs → Adm d x := by
  intro x hx
  exact hys x (hxy hx)

/-- A finite list carried through two lower-index calls.

`firstInput` and `secondInput` are deliberately independent: when the
auxiliary divisor changes, the caller must exhibit the corresponding local
test data and its relation to `carried`.  The two pass fields are the exact
retention obligations and do not hide an existential test transformation.
-/
structure TwoCallTestRetention
    (δ : Type v) (Test : Type w) (Source : Type u)
    (Adm : δ → Test → Prop) (Pass : Test → Source → Prop)
    (firstDivisor secondDivisor : δ)
    (firstSource secondSource : Source) where
  carried : List Test
  firstInput : List Test
  secondInput : List Test
  carried_admissible : ∀ t, t ∈ carried → Adm firstDivisor t
  firstInput_admissible : ∀ t, t ∈ firstInput → Adm firstDivisor t
  secondInput_admissible : ∀ t, t ∈ secondInput → Adm secondDivisor t
  carried_in_first : ListCarried carried firstInput
  carried_in_second : ListCarried carried secondInput
  first_passes : ∀ t, t ∈ carried → Pass t firstSource
  second_passes : ∀ t, t ∈ carried → Pass t secondSource

theorem TwoCallTestRetention.first_admissible
    {δ : Type v} {Test : Type w} {Source : Type u}
    {Adm : δ → Test → Prop} {Pass : Test → Source → Prop}
    {d₁ d₂ : δ} {s₁ s₂ : Source}
    (r : TwoCallTestRetention δ Test Source Adm Pass d₁ d₂ s₁ s₂) :
    ∀ t, t ∈ r.carried → Adm d₁ t := by
  exact r.carried_admissible

theorem TwoCallTestRetention.second_admissible
    {δ : Type v} {Test : Type w} {Source : Type u}
    {Adm : δ → Test → Prop} {Pass : Test → Source → Prop}
    {d₁ d₂ : δ} {s₁ s₂ : Source}
    (r : TwoCallTestRetention δ Test Source Adm Pass d₁ d₂ s₁ s₂) :
    ∀ t, t ∈ r.carried → Adm d₂ t := by
  intro t ht
  exact r.secondInput_admissible t (r.carried_in_second ht)

theorem TwoCallTestRetention.retains_both
    {δ : Type v} {Test : Type w} {Source : Type u}
    {Adm : δ → Test → Prop} {Pass : Test → Source → Prop}
    {d₁ d₂ : δ} {s₁ s₂ : Source}
    (r : TwoCallTestRetention δ Test Source Adm Pass d₁ d₂ s₁ s₂) :
    (∀ t, t ∈ r.carried → Pass t s₁ ∧ Pass t s₂) := by
  intro t ht
  exact ⟨r.first_passes t ht, r.second_passes t ht⟩

/-! ## Old/new component bookkeeping -/

variable {κ : Type v}

/-- The explicit component information used by a two-call successor.

The split only records what the caller has proved: disjoint old/new lists,
their cover, and a cover for the components declared common.  No support
operation or finiteness theorem is smuggled into this structure.
-/
structure OldNewSplit (κ : Type v) where
  oldComponents : List κ
  newComponents : List κ
  commonComponents : List κ
  old_new_disjoint : ∀ p, p ∈ oldComponents → p ∉ newComponents
  old_new_cover : ∀ p, p ∈ oldComponents ++ newComponents →
    p ∈ oldComponents ∨ p ∈ newComponents
  common_component_cover : ∀ p, p ∈ commonComponents →
    p ∈ oldComponents ∨ p ∈ newComponents

theorem OldNewSplit.union_mem
    (split : OldNewSplit κ) {p : κ}
    (hp : p ∈ split.oldComponents ++ split.newComponents) :
    p ∈ split.oldComponents ∨ p ∈ split.newComponents := by
  exact split.old_new_cover p hp

theorem OldNewSplit.common_mem_union
    (split : OldNewSplit κ) {p : κ}
    (hp : p ∈ split.commonComponents) :
    p ∈ split.oldComponents ∨ p ∈ split.newComponents := by
  exact split.common_component_cover p hp

theorem OldNewSplit.not_new_of_old
    (split : OldNewSplit κ) {p : κ}
    (hp : p ∈ split.oldComponents) : p ∉ split.newComponents := by
  exact split.old_new_disjoint p hp

/-! ## Exact integer defect step -/

/-- The defect formula needed after combining the two lower-index calls.

`oldDefect` and `newDefect` are the two recursive bounds.  The common defect
and output defect are fields because their relation is supplied by the actual
support-removal argument; this module proves only the resulting integer
inequality.
-/
structure TwoCallDefectArithmetic (D h : Nat) where
  oldDefect : Int
  newDefect : Int
  commonDefect : Int
  outputDefect : Int
  old_bound : oldDefect ≤ defectBound D h
  new_bound : newDefect ≤ defectBound D h
  common_eq_min : commonDefect = min oldDefect newDefect
  output_eq_common_sub_one : outputDefect = commonDefect - 1

theorem defectBound_succ (D h : Nat) :
    defectBound D (h + 1) = defectBound D h - 1 := by
  simp only [defectBound, Nat.cast_add, Nat.cast_one]
  ring

theorem TwoCallDefectArithmetic.output_bound
    {D h : Nat} (a : TwoCallDefectArithmetic D h) :
    a.outputDefect ≤ defectBound D (h + 1) := by
  rw [defectBound_succ]
  rw [a.output_eq_common_sub_one, a.common_eq_min]
  exact sub_le_sub_right
    (le_trans (min_le_left _ _) a.old_bound) 1

theorem TwoCallDefectArithmetic.output_bound_using_new
    {D h : Nat} (a : TwoCallDefectArithmetic D h) :
    a.outputDefect ≤ defectBound D (h + 1) := by
  rw [defectBound_succ]
  rw [a.output_eq_common_sub_one, a.common_eq_min]
  exact sub_le_sub_right
    (le_trans (min_le_right _ _) a.new_bound) 1

/-! The two contracts can be consumed together without asserting a producer. -/

structure TwoCallRetentionCertificate
    (D h : Nat) (δ : Type v) (Test : Type w) (Source : Type u)
    (Adm : δ → Test → Prop) (Pass : Test → Source → Prop)
    (firstDivisor secondDivisor : δ)
    (firstSource secondSource : Source) (κ : Type v) where
  tests : TwoCallTestRetention δ Test Source Adm Pass
    firstDivisor secondDivisor firstSource secondSource
  components : OldNewSplit κ
  arithmetic : TwoCallDefectArithmetic D h

theorem TwoCallRetentionCertificate.retains_and_bounds
    {D h : Nat} {δ : Type v} {Test : Type w} {Source : Type u}
    {Adm : δ → Test → Prop} {Pass : Test → Source → Prop}
    {d₁ d₂ : δ} {s₁ s₂ : Source} {κ : Type v}
    (c : TwoCallRetentionCertificate D h δ Test Source Adm Pass
      d₁ d₂ s₁ s₂ κ) :
    (∀ t, t ∈ c.tests.carried → Pass t s₁ ∧ Pass t s₂) ∧
      c.arithmetic.outputDefect ≤ defectBound D (h + 1) := by
  exact ⟨c.tests.retains_both, c.arithmetic.output_bound⟩

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.TwoCallTestRetention.retains_both
#print axioms SymplecticStafford.Induction.TwoCallDefectArithmetic.output_bound
#print axioms SymplecticStafford.Induction.TwoCallRetentionCertificate.retains_and_bounds
