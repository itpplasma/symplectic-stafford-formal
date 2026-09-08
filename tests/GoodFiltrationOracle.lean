import SymplecticStafford.Filtered.GoodFiltration
import Mathlib.Tactic.NormNum

/- Independent behavioral oracle for the finite good-filtration construction. -/
namespace SymplecticStafford.Filtered.GoodFiltrationOracle

def allFiltration : FiltrationData ℕ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def gens : Fin 2 → ℕ := fun i => if i = 0 then 1 else 4

def bounds : Fin 2 → ℕ := fun _ => 2

theorem gens_span_top :
    Submodule.span ℕ (Set.range gens) = (⊤ : Submodule ℕ ℕ) := by
  apply top_unique
  intro x hx
  have hgen : (1 : ℕ) ∈ Submodule.span ℕ (Set.range gens) := by
    apply Submodule.subset_span
    exact ⟨0, by simp [gens]⟩
  have hsmul := Submodule.smul_mem
    (Submodule.span ℕ (Set.range gens)) x hgen
  simpa using hsmul

def filtration : ModuleFiltrationData allFiltration ℕ :=
  GoodFiltration.moduleFiltration allFiltration gens bounds gens_span_top

example : (4 : ℕ) ∈
    GoodFiltration.carrier allFiltration gens bounds 2 := by
  apply AddSubmonoid.subset_closure
  exact ⟨⟨1, by decide⟩, 0, 1, by simp [bounds], by simp [allFiltration], by
    simp [gens]⟩

example : (12 : ℕ) ∈ filtration.carrier 6 := by
  change (12 : ℕ) ∈ GoodFiltration.carrier allFiltration gens bounds 6
  apply AddSubmonoid.subset_closure
  exact ⟨⟨1, by decide⟩, 4, 3, by simp [bounds], by simp [allFiltration], by
    norm_num [gens]⟩

example : (3 : ℕ) ∈ filtration.carrier 6 := by
  have ha : (3 : ℕ) ∈ allFiltration.carrier 4 := by simp [allFiltration]
  have hx : (1 : ℕ) ∈
      GoodFiltration.carrier allFiltration gens bounds 2 := by
    exact GoodFiltration.generator_mem allFiltration gens bounds ⟨0, by decide⟩
  have h := GoodFiltration.smul_mem allFiltration gens bounds ha hx
  simpa [filtration, GoodFiltration.moduleFiltration, gens] using h

example : ∃ n : ℕ, (37 : ℕ) ∈ filtration.carrier n :=
  filtration.exhaustive 37

end SymplecticStafford.Filtered.GoodFiltrationOracle
