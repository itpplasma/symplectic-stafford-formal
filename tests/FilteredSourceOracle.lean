import SymplecticStafford.Filtered.Localization
import SymplecticStafford.Source.Assembly
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

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
  apply Filtered.degreeAtMost_add
  · simp [Filtered.HasDegreeAtMost, natFiltration]
  · simp [Filtered.HasDegreeAtMost, natFiltration]

example : Filtered.HasDegreeAtMost natFiltration (3 + 5) (2 * 3) := by
  apply Filtered.degreeAtMost_mul <;>
    simp [Filtered.HasDegreeAtMost, natFiltration]

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

def unitCandidates : CandidateFamily ℕ where
  candidates := {1}
  candidate_nonzero := by
    intro f hf
    simp at hf
    omega

def unitSelection : DivisorSelection unitCandidates where
  select := by
    intro d hd
    refine ⟨1, by simp, ?_⟩
    refine ⟨⟨1, 0, ?_⟩⟩
    simp

example : SameDivisorS1 (R := ℕ) :=
  unitSelection.sameDivisor

end SymplecticStafford.FilteredSourceOracle
