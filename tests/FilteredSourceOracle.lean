module

public import SymplecticStafford.Filtered.Localization
public import SymplecticStafford.Source.Assembly
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SymplecticStafford.FilteredSourceOracle

open SymplecticStafford

/- A concrete filtered chart over Nat.  The test exercises the contract's
  elementary filtration laws without asserting a universal source theorem. -/
def natFiltration : Filtered.FiltrationData ℕ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

example : Filtered.HasDegreeAtMost natFiltration 4 (2 + 2) := by
  have h := Filtered.degreeAtMost_add (F := natFiltration)
    (i := 4) (j := 4) (a := 2) (b := 2)
    (by simp [Filtered.HasDegreeAtMost, natFiltration])
    (by simp [Filtered.HasDegreeAtMost, natFiltration])
  simpa using h

example : Filtered.HasDegreeAtMost natFiltration (3 + 5) (2 * 3) := by
  have h := Filtered.degreeAtMost_mul (F := natFiltration)
    (i := 4) (j := 4) (a := 2) (b := 3)
    (by simp [Filtered.HasDegreeAtMost, natFiltration])
    (by simp [Filtered.HasDegreeAtMost, natFiltration])
  simpa using h

def natLocalization : Filtered.FilteredLocalizationCertificate ℕ ℕ where
  sourceFiltration := natFiltration
  chartFiltration := natFiltration
  map := RingHom.id ℕ
  map_filtered := by intro n a ha; exact ha
  denominator := 1
  denominator_mem := ⟨0, by simp [Filtered.HasDegreeAtMost, natFiltration]⟩
  right_clearable := by
    intro x
    exact ⟨0, x, by simp⟩

example : ∃ n : ℕ, ∀ x ∈ [2, 5], ∃ y : ℕ,
    x * (natLocalization.map natLocalization.denominator) ^ n =
      natLocalization.map y := by
  exact Filtered.common_right_clear_from_certificate natLocalization [2, 5]

open SymplecticStafford.Source

def unitCandidates : CandidateFamily (ZMod 2) where
  candidates := {1}
  candidate_nonzero := by
    intro f hf
    simp at hf
    simpa [hf]

def unitSelection : DivisorSelection unitCandidates where
  select := by
    intro d hd
    have hd1 : d = 1 := by
      fin_cases d
      · exact (hd rfl).elim
      · rfl
    subst d
    refine ⟨1, Finset.mem_singleton_self 1, ?_⟩
    exact ⟨⟨1, 0, by simp⟩⟩

example : SameDivisorS1 (R := ZMod 2) :=
  unitSelection.sameDivisor

end SymplecticStafford.FilteredSourceOracle
