module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.FinCases
public import SymplecticStafford.Filtered.WeightedDetection

@[expose] public section

/-!
# Faithful weighted detection and its exact boundary

The weighted-top theorem is a finite statement.  To use it for an associated
graded module, one must separately provide a faithful finite-coordinate
encoding into the coefficient space.  This file packages exactly that bridge:
injectivity of the encoding plus the explicit integer-weighted triangular
system yields a nonzero detected output.  Integer weights make negative
degrees harmless; no shift, completion, or localization is used.

The final example records the complementary boundary.  If equal-weight
off-diagonal vanishing is omitted, a nonzero vector can be annihilated even
when all diagonal entries are nonzero.  Thus faithfulness and the triangular
hypotheses cannot be inferred merely from a finite list of graded coordinates.
-/

namespace SymplecticStafford.Filtered

universe u v

section Faithful

variable {ι : Type u} {K : Type v} {M : Type*}
variable [Nonempty ι] [Fintype ι] [DecidableEq ι] [Semiring K]
variable [NoZeroDivisors K]
variable [AddCommMonoid M] [Module K M]

/-- A finite weighted detector with faithfulness made explicit. -/
structure FaithfulWeightedDetector where
  encode : M →ₗ[K] (ι → K)
  encode_injective : Function.Injective encode
  triangular : WeightedTriangularData (ι := ι) (K := K)

namespace FaithfulWeightedDetector

variable (D : FaithfulWeightedDetector (ι := ι) (K := K) (M := M))

theorem encode_ne_zero {x : M} (hx : x ≠ 0) : D.encode x ≠ 0 := by
  intro hzero
  apply hx
  apply D.encode_injective
  calc
    D.encode x = 0 := hzero
    _ = D.encode 0 := (D.encode.map_zero).symm

theorem detect_nonzero {x : M} (hx : x ≠ 0) :
    ∃ i, D.triangular.action (D.encode x) i ≠ 0 := by
  have hvec : ∃ j, (D.encode x) j ≠ 0 := by
    by_contra h
    apply D.encode_ne_zero hx
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  exact D.triangular.action_ne_zero_of_nonzero hvec

end FaithfulWeightedDetector

end Faithful

section MissingTriangularity

variable {K : Type*} [Ring K]

/-- A weighted matrix without the equal-weight off-diagonal condition. -/
structure WeakWeightedData where
  coefficient : Fin 2 → Fin 2 → K

namespace WeakWeightedData

variable (T : WeakWeightedData (K := K))

def action (v : Fin 2 → K) (i : Fin 2) : K :=
  ∑ j, T.coefficient i j * v j

def cancelling : WeakWeightedData (K := ℤ) where
  coefficient := fun i j => if i = j then 1 else -1

theorem cancelling_action_zero :
    (cancelling.action (fun _ : Fin 2 => (1 : ℤ))) = 0 := by
  funext i
  fin_cases i <;> simp [action, cancelling, Fin.sum_univ_two]

theorem cancelling_diagonal_ne_zero :
    ∀ i : Fin 2, cancelling.coefficient i i ≠ (0 : ℤ) := by
  intro i
  simp [cancelling]

end WeakWeightedData

end MissingTriangularity

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FaithfulWeightedDetector.detect_nonzero
#print axioms SymplecticStafford.Filtered.WeakWeightedData.cancelling_action_zero
