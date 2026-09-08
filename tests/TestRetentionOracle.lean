import SymplecticStafford.Induction.TestRetention
import Mathlib.Data.Int.Basic

/-!
# Independent oracle for finite-test retention and M09--M10 arithmetic

The oracle uses finite natural-number test labels and concrete predicates.  It
checks list retention through two calls, an old/new split, and both ways of
deriving the successor defect bound.  It supplies no source producer or
support theorem.
-/

namespace SymplecticStafford.TestRetentionOracle

open SymplecticStafford.Induction

def adm (d t : Nat) : Prop := t ≤ d

def pass (t s : Nat) : Prop := t ≤ s

def retention : TwoCallTestRetention Nat Nat Nat adm pass 2 3 4 5 where
  carried := [2]
  firstInput := [2, 0]
  secondInput := [2, 1]
  carried_admissible := by
    intro t ht
    simp at ht
    subst t
    norm_num [adm]
  firstInput_admissible := by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl <;> norm_num [adm]
  secondInput_admissible := by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl <;> norm_num [adm]
  carried_in_first := by
    intro t ht
    simp at ht
    simpa [ht]
  carried_in_second := by
    intro t ht
    simp at ht
    simpa [ht]
  first_passes := by
    intro t ht
    simp at ht
    subst t
    norm_num [pass]
  second_passes := by
    intro t ht
    simp at ht
    subst t
    norm_num [pass]

example : ∀ t, t ∈ retention.carried → pass t 4 ∧ pass t 5 := by
  exact retention.retains_both

def split : OldNewSplit Nat where
  oldComponents := [0]
  newComponents := [1]
  commonComponents := [0, 1]
  old_new_disjoint := by
    intro p hp hn
    have hp' : p = 0 := by simpa using hp
    subst p
    simpa using hn
  old_new_cover := by
    intro p hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr hp
  common_component_cover := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)

example : 0 ∈ split.oldComponents := by decide

example : 1 ∈ split.newComponents := by decide

example : 1 ∈ split.commonComponents →
    1 ∈ split.oldComponents ∨ 1 ∈ split.newComponents := by
  intro h
  exact split.common_mem_union h

def arithmetic : TwoCallDefectArithmetic 4 2 where
  oldDefect := 2
  newDefect := 1
  commonDefect := 1
  outputDefect := 0
  old_bound := by norm_num [defectBound]
  new_bound := by norm_num [defectBound]
  common_eq_min := by norm_num
  output_eq_common_sub_one := by norm_num

example : arithmetic.outputDefect ≤ defectBound 4 (2 + 1) := by
  exact arithmetic.output_bound

example : arithmetic.outputDefect ≤ defectBound 4 (2 + 1) := by
  exact arithmetic.output_bound_using_new

def certificate : TwoCallRetentionCertificate 4 2 Nat Nat Nat adm pass
    2 3 4 5 Nat where
  tests := retention
  components := split
  arithmetic := arithmetic

example :
    (∀ t, t ∈ certificate.tests.carried → pass t 4 ∧ pass t 5) ∧
      certificate.arithmetic.outputDefect ≤ defectBound 4 (2 + 1) := by
  exact certificate.retains_and_bounds

end SymplecticStafford.TestRetentionOracle
