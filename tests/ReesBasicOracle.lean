module

public import SymplecticStafford.Filtered.ReesBasic
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace SymplecticStafford.Filtered.ReesBasicOracle

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
  value := 3
  bounded := by simp [HasDegreeAtMost, trivialFiltration]

def y : ReesTerm (R := ℕ) trivialFiltration where
  degree := 4
  value := 5
  bounded := by simp [HasDegreeAtMost, trivialFiltration]

example : (ReesTerm.add x y).degree = 4 := by
  simp [x, y]

example : (ReesTerm.mul x y).value = 15 := by
  norm_num [x, y]

example : ∃ z : ReesTerm trivialFiltration, z.value = 12 := by
  exact ReesTerm.exists_value trivialFiltration 12

example : ReesTerm.reindex (n := 4) (ReesTerm.add x y) (by simp [x, y]) =
    ReesTerm.add (ReesTerm.reindex (n := 4) x (by simp [x]))
      (ReesTerm.reindex (n := 4) y (by simp [y])) := by
  exact ReesTerm.reindex_add x y (by simp [x, y]) (by simp [x]) (by simp [y])

example : ReesTerm.reindex (n := 6) (ReesTerm.mul x y) (by simp [x, y]) =
    ReesTerm.mul (ReesTerm.reindex (n := 2) x (by simp [x]))
      (ReesTerm.reindex (n := 4) y (by simp [y])) := by
  exact ReesTerm.reindex_mul (m := 2) (n := 4) x y (by simp [x]) (by simp [y])

example : ReesTerm.add (ReesTerm.add x y) x =
    ReesTerm.add x (ReesTerm.add y x) := by
  exact ReesTerm.add_assoc_term x y x

example : ReesTerm.mul (ReesTerm.mul x y) x =
    ReesTerm.mul x (ReesTerm.mul y x) := by
  exact ReesTerm.mul_assoc_term x y x

end SymplecticStafford.Filtered.ReesBasicOracle
