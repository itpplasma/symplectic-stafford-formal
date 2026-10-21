module

public import Mathlib
public import SymplecticStafford.Induction.TestRetention

@[expose] public section

/-!
# Finite-support arithmetic for the M10 successor

The paper's successor removes a common support component after two lower
index calls.  This file isolates the part that is genuinely finite-set
arithmetic: if the new support is a strict subset of each lower support, its
integer defect drops by one.  It does not construct the supports, choose a
central scalar, or provide either lower call.  Those remain the geometric and
module-theoretic M09--M10 obligations.

Unlike the older `common_eq_min` field, this boundary derives the successor
bound from actual finite supports and strict removal.  The support hypotheses
are explicit and are not hidden inside a pre-built successor witness.
-/

namespace SymplecticStafford.Induction

universe u

variable {α : Type u} [DecidableEq α]

def finiteSupportDefect (S : Finset α) : Int := (S.card : Int) - 1

theorem finiteSupportDefect_le_sub_one_of_ssubset
    {S T : Finset α} (hTS : T ⊂ S) :
    finiteSupportDefect T ≤ finiteSupportDefect S - 1 := by
  have hcard : T.card < S.card := Finset.card_lt_card hTS
  simp only [finiteSupportDefect]
  omega

/- A two-call support-removal certificate.  `output` is the support after the
   pencil step; strictness records that at least one common component was
   removed, while the two inclusions retain both recursive bounds. -/
structure SupportRemovalArithmetic (D h : Nat) where
  oldSupport : Finset α
  newSupport : Finset α
  outputSupport : Finset α
  output_subset_old : outputSupport ⊆ oldSupport
  output_subset_new : outputSupport ⊆ newSupport
  output_strict_old : outputSupport ⊂ oldSupport
  output_strict_new : outputSupport ⊂ newSupport
  old_bound : finiteSupportDefect oldSupport ≤ defectBound D h
  new_bound : finiteSupportDefect newSupport ≤ defectBound D h

theorem SupportRemovalArithmetic.output_bound_old
    {D h : Nat} (c : SupportRemovalArithmetic (α := α) D h) :
    finiteSupportDefect c.outputSupport ≤ defectBound D (h + 1) := by
  calc
    finiteSupportDefect c.outputSupport ≤
        finiteSupportDefect c.oldSupport - 1 :=
      finiteSupportDefect_le_sub_one_of_ssubset c.output_strict_old
    _ ≤ defectBound D h - 1 := sub_le_sub_right c.old_bound 1
    _ = defectBound D (h + 1) := (defectBound_succ D h).symm

theorem SupportRemovalArithmetic.output_bound_new
    {D h : Nat} (c : SupportRemovalArithmetic (α := α) D h) :
    finiteSupportDefect c.outputSupport ≤ defectBound D (h + 1) := by
  calc
    finiteSupportDefect c.outputSupport ≤
        finiteSupportDefect c.newSupport - 1 :=
      finiteSupportDefect_le_sub_one_of_ssubset c.output_strict_new
    _ ≤ defectBound D h - 1 := sub_le_sub_right c.new_bound 1
    _ = defectBound D (h + 1) := (defectBound_succ D h).symm

theorem SupportRemovalArithmetic.output_bound
    {D h : Nat} (c : SupportRemovalArithmetic (α := α) D h) :
    finiteSupportDefect c.outputSupport ≤ defectBound D (h + 1) :=
  c.output_bound_old

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.finiteSupportDefect_le_sub_one_of_ssubset
#print axioms SymplecticStafford.Induction.SupportRemovalArithmetic.output_bound
