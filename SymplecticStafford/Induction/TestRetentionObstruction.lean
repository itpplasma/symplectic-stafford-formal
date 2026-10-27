module

public import SymplecticStafford.Induction.TestRetention
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Boundary for source-dependent test retention

The two lower calls can both pass a carried test while the affine pencil
source fails it.  This tiny model isolates the missing M09--M10 implication:
the generation predicate must be proved stable under the *chosen* central
pencil parameter.  List carriage and the two lower pass certificates alone
do not provide that stability.

This is a behavioral boundary only.  It does not refute the paper's actual
local generation theorem, where pencil stability is an additional
module-theoretic statement to be proved.
-/

namespace SymplecticStafford.Induction

/- The first and second lower sources are both zero, while the pencil source
   is one.  The pass predicate intentionally recognizes only zero. -/
def retentionBoundaryPass (_ : Unit) (source : Nat) : Prop := source ≤ 1

def retentionBoundaryParameters : CentralParameters Nat Unit where
  embed := fun _ => 2
  central := by
    intro scalar x
    simp [Nat.mul_comm]

def retentionBoundary :
    TwoCallTestRetention Unit Unit Nat
      (fun _ _ => True) retentionBoundaryPass () () 0 1 where
  carried := [()]
  firstInput := [()]
  secondInput := [()]
  carried_admissible := by
    intro t ht
    trivial
  firstInput_admissible := by
    intro t ht
    trivial
  secondInput_admissible := by
    intro t ht
    trivial
  carried_in_first := by
    intro t ht
    simp at ht ⊢
  carried_in_second := by
    intro t ht
    simp at ht ⊢
  first_passes := by
    intro t ht
    simp [retentionBoundaryPass]
  second_passes := by
    intro t ht
    simp [retentionBoundaryPass]

theorem retention_boundary_lower_passes :
    ∀ t, t ∈ retentionBoundary.carried →
      retentionBoundaryPass t 0 ∧
        retentionBoundaryPass t 1 := by
  exact retentionBoundary.retains_both

theorem retention_boundary_pencil_fails :
    ¬ (∀ t, t ∈ retentionBoundary.carried →
      retentionBoundaryPass t
        (pencilMember retentionBoundaryParameters
          0 1 ())) := by
  intro h
  have hp := h () (by simp [retentionBoundary])
  norm_num [retentionBoundaryPass, pencilMember,
    retentionBoundaryParameters] at hp

theorem lower_passes_do_not_supply_pencil_retention :
    (∀ t, t ∈ retentionBoundary.carried →
      retentionBoundaryPass t 0 ∧
        retentionBoundaryPass t 1) ∧
      ¬ (∀ t, t ∈ retentionBoundary.carried →
        retentionBoundaryPass t
          (pencilMember retentionBoundaryParameters
            0 1 ())) := by
  exact ⟨retention_boundary_lower_passes, retention_boundary_pencil_fails⟩

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.retention_boundary_lower_passes
#print axioms SymplecticStafford.Induction.retention_boundary_pencil_fails
