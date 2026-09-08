import SymplecticStafford.Filtered.NoetherianBoundary

namespace SymplecticStafford.Filtered

/- Independent consumer checks: the same explicit coordinate witnesses show
that the chain really grows, while the filtration remains exhaustive. -/
example (n : ℕ) : HasDegreeAtMost constantFiltration n (coordinate n) := by
  exact constantFiltration_degreeAtMost n (coordinate n)

example (n : ℕ) : coordinate n ∈ prefixIdeal (n + 1) := by
  exact coordinate_mem_succ n

example (n : ℕ) : coordinate n ∉ prefixIdeal n := by
  exact coordinate_not_mem n

example : ¬ IsNoetherianRing SequenceSemiring := by
  exact prefixChain_not_noetherian

end SymplecticStafford.Filtered
