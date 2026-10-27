module

public import SymplecticStafford.Filtered.ReesQuotient
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace SymplecticStafford.Filtered.ReesQuotientOracle

def trivialFiltration : FiltrationData ℕ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def x : ReesTerm (R := ℕ) trivialFiltration where
  degree := 2
  value := 7
  bounded := by simp [HasDegreeAtMost, trivialFiltration]

def y : ReesTerm (R := ℕ) trivialFiltration where
  degree := 4
  value := 11
  bounded := by simp [HasDegreeAtMost, trivialFiltration]

example : ReesQuotient.value (ReesQuotient.mk x) = 7 := by
  simp [x]

example :
    ReesQuotient.mk (ReesTerm.reindex x (n := 6) (by simp [x])) =
      ReesQuotient.mk x := by
  exact ReesQuotient.reindex_mk x (by simp [x])

example :
    ReesQuotient.value
      (ReesQuotient.add (ReesQuotient.mk x) (ReesQuotient.mk y)) = 18 := by
  norm_num [x, y]

example :
    ReesQuotient.value
      (ReesQuotient.mul (ReesQuotient.mk x) (ReesQuotient.mk y)) = 77 := by
  norm_num [x, y]

example :
    ReesQuotient.add (ReesQuotient.mk x) (ReesQuotient.mk y) =
      ReesQuotient.add (ReesQuotient.mk y) (ReesQuotient.mk x) := by
  exact ReesQuotient.add_comm _ _

example :
    ReesQuotient.mul (ReesQuotient.mk x)
      (ReesQuotient.add (ReesQuotient.mk x) (ReesQuotient.mk y)) =
      ReesQuotient.add
        (ReesQuotient.mul (ReesQuotient.mk x) (ReesQuotient.mk x))
        (ReesQuotient.mul (ReesQuotient.mk x) (ReesQuotient.mk y)) := by
  exact ReesQuotient.mul_add _ _ _

end SymplecticStafford.Filtered.ReesQuotientOracle
