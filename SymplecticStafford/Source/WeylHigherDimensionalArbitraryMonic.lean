import Stafford38.Weyl.EulerRemainder
import Stafford38.Weyl.IteratedEquivalence

/-!
# Original-ring division by an arbitrary outer monic polynomial

The newest momentum in a presented higher-rank Weyl algebra is an Ore
variable over the old coefficient stage.  The generic Ore right-division
theorem therefore applies to every monic coefficient-left polynomial, not
only to the pure power used by the positive-coordinate remainder theorem.

The wrappers below transport the division identity through the checked
`PresentedWeyl ≃ IteratedPairStage` equivalence.  In particular, the quotient
and remainder are explicitly elements of the original presented ring.  This
is only a division certificate: no assertion that the resulting remainder
vanishes, or that a two-generator right ideal is the whole ring, is made.
-/

namespace SymplecticStafford.Source

open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreRightQuotient
open Stafford38.OreCoordinateStage
open Stafford38.OreIteratedPairStage
open Stafford38.OrePairStage
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]

private theorem iteratedPairStage_nontrivial (n : ℕ) :
    Nontrivial (IteratedPairStage k n) := by
  induction n with
  | zero =>
      change Nontrivial k
      infer_instance
  | succ n ih =>
      letI : Nontrivial (IteratedPairStage k n) := ih
      change Nontrivial (PairStage (B := IteratedPairStage k n))
      exact normalOreNontrivial (coordinateDerivation)

local instance (n : ℕ) : Algebra k (IteratedPairStage k n) :=
  iteratedPairStageAlgebra k n

local instance (n : ℕ) :
    Algebra k (CoordinateStage (B := IteratedPairStage k n)) :=
  coordinateStageAlgebra

local instance (n : ℕ) :
    Algebra k (PairStage (B := IteratedPairStage k n)) :=
  pairStageAlgebra

/-- Evaluate an outer coefficient polynomial in the newest pair stage, then
transport it to the original presented Weyl algebra. -/
def presentedOuterPolynomialEval
    (n : ℕ) (H : Polynomial (CoordinateStage (B := IteratedPairStage k n))) :
    PresentedWeyl k (n + 1) :=
  iteratedToPresented k (n + 1)
    (normalForm (coordinateDerivation :
      OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n))) H)

@[simp] theorem presentedOuterPolynomialEval_map
    (n : ℕ) (H : Polynomial (CoordinateStage (B := IteratedPairStage k n))) :
    presentedToIterated k (n + 1) (presentedOuterPolynomialEval k n H) =
      normalForm (coordinateDerivation :
        OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n))) H := by
  letI : Nontrivial (IteratedPairStage k n) :=
    iteratedPairStage_nontrivial k n
  unfold presentedOuterPolynomialEval
  change ((presentedToIterated k (n + 1)).comp
      (iteratedToPresented k (n + 1))) (normalForm (coordinateDerivation :
        OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n))) H) = _
  rw [presentedToIterated_comp_iteratedToPresented]
  rfl

/-- Right division by an arbitrary monic polynomial in the newest outer
variable, with the quotient and remainder evaluated in the original ring. -/
theorem presented_outer_monic_right_division
    (n : ℕ)
    (H : Polynomial (CoordinateStage (B := IteratedPairStage k n)))
    (hH : H.Monic)
    (d : PresentedWeyl k (n + 1)) :
    ∃ q r : PresentedWeyl k (n + 1),
      d = presentedOuterPolynomialEval k n H * q + r ∧
        (r = 0 ∨ ∃ r₀ : Polynomial (CoordinateStage (B := IteratedPairStage k n)),
          r = iteratedToPresented k (n + 1) (normalForm (coordinateDerivation :
            OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n))) r₀) ∧
          r₀.natDegree < H.natDegree) := by
  letI : Nontrivial (IteratedPairStage k n) :=
    iteratedPairStage_nontrivial k n
  let D : OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateDerivation
  obtain ⟨p, hp⟩ := normalForm_surjective D
    (presentedToIterated k (n + 1) d)
  obtain ⟨q₀, r₀, hdiv, hrem⟩ :=
    right_division_exists D H p hH
  let q : PresentedWeyl k (n + 1) :=
    iteratedToPresented k (n + 1) (normalForm D q₀)
  let r : PresentedWeyl k (n + 1) :=
    iteratedToPresented k (n + 1) (normalForm D r₀)
  refine ⟨q, r, ?_, ?_⟩
  · have hdivN : presentedToIterated k (n + 1) d =
        normalForm D (rightMul D H q₀) +
          normalForm D r₀ := by
      rw [← hp, hdiv, normalForm_add]
    have hdiv' := congrArg (iteratedToPresented k (n + 1)) hdivN
    have hleft :
        iteratedToPresented k (n + 1)
            (presentedToIterated k (n + 1) d) = d := by
      exact DFunLike.congr_fun
        (iteratedToPresented_comp_presentedToIterated k (n + 1)) d
    have hsum := (iteratedToPresented k (n + 1)).map_add
      (normalForm D (rightMul D H q₀)) (normalForm D r₀)
    have hdiv'' :
        d = iteratedToPresented k (n + 1)
              (normalForm D (rightMul D H q₀)) +
            iteratedToPresented k (n + 1) (normalForm D r₀) := by
      calc
        d = iteratedToPresented k (n + 1)
              (presentedToIterated k (n + 1) d) := hleft.symm
        _ = iteratedToPresented k (n + 1)
              (normalForm D (rightMul D H q₀) + normalForm D r₀) := hdiv'
        _ = _ := hsum
    have hprod :
        iteratedToPresented k (n + 1)
            (normalForm D (rightMul D H q₀)) =
          iteratedToPresented k (n + 1) (normalForm D H) *
            iteratedToPresented k (n + 1) (normalForm D q₀) := by
      rw [normalForm_mul]
      exact (iteratedToPresented k (n + 1)).map_mul _ _
    rw [hprod] at hdiv''
    change d = presentedOuterPolynomialEval k n H * q + r
      at hdiv''
    change d = presentedOuterPolynomialEval k n H * q + r
    simpa [presentedOuterPolynomialEval, q, r] using hdiv''
  · rcases hrem with hzero | hsmall
    · have hrzero : normalForm D r₀ = 0 := by
        rw [hzero, normalForm_zero]
      apply Or.inl
      dsimp [r]
      rw [hzero, normalForm_zero]
      exact RingHom.map_zero (iteratedToPresented k (n + 1)).toRingHom
    · exact Or.inr ⟨r₀, rfl, hsmall⟩

/- The remainder branch above deliberately keeps the coefficient polynomial
  visible.  This equivalent formulation exposes the usual finite outer-PBW
  window directly and is convenient for callers that need its bound. -/
theorem presented_outer_monic_right_division_window
    (n : ℕ)
    (H : Polynomial (CoordinateStage (B := IteratedPairStage k n)))
    (hH : H.Monic)
    (d : PresentedWeyl k (n + 1)) :
    ∃ q₀ r₀ : Polynomial (CoordinateStage (B := IteratedPairStage k n)),
      presentedToIterated k (n + 1) d =
          normalForm (coordinateDerivation :
            OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)))
              (rightMul (coordinateDerivation :
                OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n))) H q₀) +
            normalForm (coordinateDerivation :
              OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n))) r₀ ∧
        (r₀ = 0 ∨ r₀.natDegree < H.natDegree) := by
  letI : Nontrivial (IteratedPairStage k n) :=
    iteratedPairStage_nontrivial k n
  let D : OreDivisionDerivation (CoordinateStage (B := IteratedPairStage k n)) :=
    coordinateDerivation
  obtain ⟨p, hp⟩ := normalForm_surjective D
    (presentedToIterated k (n + 1) d)
  obtain ⟨q₀, r₀, hdiv, hrem⟩ :=
    right_division_exists D H p hH
  refine ⟨q₀, r₀, ?_, hrem⟩
  rw [← hp, hdiv, normalForm_add]

#print axioms presentedOuterPolynomialEval
#print axioms presented_outer_monic_right_division
#print axioms presented_outer_monic_right_division_window

end
end SymplecticStafford.Source
