import SymplecticStafford.Source.WeylUniversalTransfer

/-! Independent consumer checks for the all-rank Weyl-equivalence transfer. -/

namespace SymplecticStafford.Source.WeylUniversalTransferOracle

universe u v

variable {k : Type u} [Field k] [CharZero k]
variable {U : Type v} [Ring U] [Algebra k U]

example {n : ℕ} (e : Stafford38.WeylAlg k n ≃ₐ[k] U) :
    SymplecticStafford.SameDivisorS1 (R := U) :=
  SymplecticStafford.Source.sameDivisor_of_weylAlg_algEquiv e

example {n : ℕ} (e : Stafford38.WeylAlg k n ≃ₐ[k] U)
    {d : U} (hd : d ≠ 0) :
    ∃ F R S : U, (1 : U) = d * R + (F * d) * S := by
  exact (SymplecticStafford.Source.sameDivisor_of_weylAlg_algEquiv e) hd

end SymplecticStafford.Source.WeylUniversalTransferOracle
