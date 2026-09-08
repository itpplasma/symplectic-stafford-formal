import SymplecticStafford.Statement

/-! A tiny independent consumer for the scaffold's ordered statement. -/

namespace SymplecticStaffordTest

example {R : Type} [Ring R] {d : R} (hd : IsUnit d) :
    ∃ F r s : R, (1 : R) = d * r + F * d * s :=
  SymplecticStafford.certificate_of_unit hd

#print axioms SymplecticStafford.certificate_of_unit

end SymplecticStaffordTest
