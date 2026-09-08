import SymplecticStafford.Induction.StrongPh
import Mathlib

/-!
# M11 obstruction: a terminal defect bound is not a cofactor

The terminal `StrongPh` contract controls only an integer defect.  This file
exhibits a model in which the terminal contract is inhabited but the original
right-ideal cofactor is impossible.  Thus the zero-quotient/zero-support to
cofactor bridge in `TerminationInterface` is a genuine mathematical input;
it cannot be recovered from terminal arithmetic or source/test retention.
-/

namespace SymplecticStafford.Induction

/- A terminal defect of `-2` is below the `D = 0, h = 1` bound `-1`. -/
def terminalFlatDefect : Nat → Nat → List (LocalTest Nat Unit Empty) → Int :=
  fun _ _ _ => -2

def terminalStrong : StrongPh 0 1 terminalFlatDefect := by
  intro d hd A Ω hΩ
  refine {
    H := 0
    source := A.B
    source_eq := by simp
    defect_bound := by norm_num [terminalFlatDefect, defectBound]
    tests_pass := ?_ }
  intro t ht
  exact nomatch t.cyclicModule

/- 2 cannot generate 1 in the displayed right ideal, regardless of the
   second generator.  The proof uses only order arithmetic and preserves the
   original factor order. -/
theorem no_original_cofactor_for_two (f : Nat) :
    ¬ Nonempty (OriginalCofactors (U := Nat) 2 f) := by
  rintro ⟨w⟩
  have hR : 2 * w.R ≤ 1 := by
    calc
      2 * w.R ≤ 2 * w.R + (f * 2) * w.S := Nat.le_add_right _ _
      _ = 1 := w.identity.symm
  have hRzero : w.R = 0 := by omega
  have hEq : 1 = (f * 2) * w.S := by
    simpa [hRzero] using w.identity
  by_cases hf : f = 0
  · subst f
    simp at hEq
  · have hfpos : 0 < f := Nat.pos_of_ne_zero hf
    by_cases hs : w.S = 0
    · rw [hs] at hEq
      simp at hEq
    · have hspos : 0 < w.S := Nat.pos_of_ne_zero hs
      have hf2 : 2 ≤ f * 2 := by omega
      have hprod : f * 2 ≤ (f * 2) * w.S :=
        Nat.le_mul_of_pos_right _ hspos
      have hbig : 2 ≤ (f * 2) * w.S := hf2.trans hprod
      omega

/- This is the exact missing M11 bridge in implication form. -/
theorem no_zero_extraction_for_terminal_flat_defect :
    ¬ (∀ {d f : Nat} {Ω : List (LocalTest Nat Unit Empty)},
      terminalFlatDefect d f Ω ≤ -1 → Nonempty (OriginalCofactors d f)) := by
  intro extraction
  have hc : Nonempty (OriginalCofactors (U := Nat) 2 0) :=
    extraction (d := 2) (f := 0) (Ω := []) (by
      norm_num [terminalFlatDefect])
  exact no_original_cofactor_for_two 0 hc

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.terminalStrong
#print axioms SymplecticStafford.Induction.no_original_cofactor_for_two
#print axioms SymplecticStafford.Induction.no_zero_extraction_for_terminal_flat_defect
