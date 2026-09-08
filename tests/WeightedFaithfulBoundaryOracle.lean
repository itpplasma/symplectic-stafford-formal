import SymplecticStafford.Filtered.WeightedFaithfulBoundary

namespace SymplecticStafford.Filtered

variable {ι K M : Type*} [Nonempty ι] [Fintype ι] [DecidableEq ι] [Semiring K]
variable [NoZeroDivisors K]
variable [AddCommMonoid M] [Module K M]

example (D : FaithfulWeightedDetector (ι := ι) (K := K) (M := M))
    {x : M} (hx : x ≠ 0) :
    ∃ i, D.triangular.action (D.encode x) i ≠ 0 := by
  exact D.detect_nonzero hx

example :
    WeakWeightedData.cancelling.action
      (fun _ : Fin 2 => (1 : ℤ)) = 0 := by
  exact WeakWeightedData.cancelling_action_zero

end SymplecticStafford.Filtered
