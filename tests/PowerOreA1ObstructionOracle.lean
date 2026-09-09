import SymplecticStafford.Filtered.PowerOreA1Obstruction

/-!
Independent consumer for the fixed A₁ obstruction.  The oracle asks for the
actual Ore-clearing witness at every power and is refuted by the checked
normal-form theorem; it does not merely inspect declarations or source text.
-/
namespace SymplecticStaffordTest.PowerOreA1Obstruction

open SymplecticStafford.Filtered.PowerOreA1Obstruction

example : p * x = x * p + 1 := p_mul_x
example : x * H = (H - 1) * x := x_mul_H
example : ¬ ∃ (n : ℕ) (b : A1), x * H ^ n = H * b := no_right_power_clear

end SymplecticStaffordTest.PowerOreA1Obstruction

#print axioms SymplecticStafford.Filtered.PowerOreA1Obstruction.no_right_power_clear
