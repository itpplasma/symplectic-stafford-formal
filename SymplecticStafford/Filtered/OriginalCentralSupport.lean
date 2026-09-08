import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Support
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Tactic.NormNum
import SymplecticStafford.Semantics.SupportDimension

/-!
# Original-ring central characteristic support

This module supplies a genuine support object for an original-ring right
quotient without introducing a class-map existential. A right ideal is first
viewed as a submodule for the opposite action, so the quotient retains the
literal right-sided order in `U`. The center of `U` then acts on the quotient
and Mathlib's spectrum support gives an actual zero-detection theorem.

This is the strongest M01 bridge available before constructing the Rees
associated module over `Spec (gr U)`: it does not identify the center with the
associated graded ring, and it does not assert finite generation or a Krull
dimension theorem. Those are separate M02--M05 obligations.
-/

namespace SymplecticStafford.Filtered

universe u

open SymplecticStafford

section OriginalQuotient

variable {R : Type u} [Ring R]

/-- A right ideal is a submodule for the left action of `Rᵐᵒᵖ` on `R`.

The scalar action is `x * r`, so the displayed order is not reversed in the
underlying original ring. -/
def rightIdealOppSubmodule (I : RingRightIdeal (R := R)) :
    Submodule Rᵐᵒᵖ R where
  carrier := I.carrier
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro r x hx
    exact I.right_mul_mem hx r.unop

@[simp] theorem mem_rightIdealOppSubmodule_iff
    (I : RingRightIdeal (R := R)) (x : R) :
    x ∈ rightIdealOppSubmodule I ↔ x ∈ I := Iff.rfl

/-- The canonical additive quotient of the original ring by a right ideal. -/
abbrev OriginalRightQuotient (I : RingRightIdeal (R := R)) :=
  R ⧸ rightIdealOppSubmodule I

@[simp] theorem originalRightQuotient_mk_eq_zero_iff_mem
    (I : RingRightIdeal (R := R)) (x : R) :
    (Submodule.Quotient.mk x : OriginalRightQuotient I) = 0 ↔ x ∈ I := by
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem originalRightQuotient_subsingleton_iff
    (I : RingRightIdeal (R := R)) :
    Subsingleton (OriginalRightQuotient I) ↔ QuotientIsZero I := by
  constructor
  · intro h q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    have hxq : (Submodule.Quotient.mk x : OriginalRightQuotient I) = 0 :=
      Subsingleton.elim _ _
    have hmem : x ∈ I :=
      (originalRightQuotient_mk_eq_zero_iff_mem I x).mp hxq
    exact (rightQuotient_mk_eq_zero_iff_mem I x).mpr hmem
  · intro h
    exact ⟨fun q₁ q₂ => by
      obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective
        (p := rightIdealOppSubmodule I)) q₁
      obtain ⟨y, rfl⟩ := (Submodule.Quotient.mk_surjective
        (p := rightIdealOppSubmodule I)) q₂
      have hx : x ∈ I :=
        (rightQuotient_mk_eq_zero_iff_mem I x).mp
          (h (Quotient.mk (rightIdealSetoid I) x))
      have hy : y ∈ I :=
        (rightQuotient_mk_eq_zero_iff_mem I y).mp
          (h (Quotient.mk (rightIdealSetoid I) y))
      have hxm : (Submodule.Quotient.mk x : OriginalRightQuotient I) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hx
      have hym : (Submodule.Quotient.mk y : OriginalRightQuotient I) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hy
      exact hxm.trans hym.symm⟩

theorem originalRightQuotient_zero_iff_quotientIsZero
    (I : RingRightIdeal (R := R)) :
    (∀ q : OriginalRightQuotient I, q = 0) ↔ QuotientIsZero I := by
  constructor
  · intro h q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    have hxq : (Submodule.Quotient.mk x : OriginalRightQuotient I) = 0 := h _
    have hmem : x ∈ I :=
      (originalRightQuotient_mk_eq_zero_iff_mem I x).mp hxq
    exact (rightQuotient_mk_eq_zero_iff_mem I x).mpr hmem
  · intro h
    intro q
    obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective
      (p := rightIdealOppSubmodule I)) q
    have hmem : x ∈ I :=
      (rightQuotient_mk_eq_zero_iff_mem I x).mp
        (h (Quotient.mk (rightIdealSetoid I) x))
    exact (originalRightQuotient_mk_eq_zero_iff_mem I x).mpr hmem

end OriginalQuotient

section CentralSupport

variable {R : Type u} [Ring R]

/-- The actual spectrum support of an original right quotient, over the
commutative center of the original ring. -/
def OriginalCentralCharacteristicSupport (I : RingRightIdeal (R := R)) :
    Set (PrimeSpectrum (Subring.center R)) :=
  Module.support (Subring.center R) (OriginalRightQuotient I)

theorem originalCentralCharacteristicSupport_nonempty_iff
    (I : RingRightIdeal (R := R)) :
    (OriginalCentralCharacteristicSupport I).Nonempty ↔
      Nontrivial (OriginalRightQuotient I) := by
  exact Module.nonempty_support_iff

theorem originalCentralCharacteristicSupport_empty_iff_quotientIsZero
    (I : RingRightIdeal (R := R)) :
    OriginalCentralCharacteristicSupport I = ∅ ↔ QuotientIsZero I := by
  change Module.support (Subring.center R) (OriginalRightQuotient I) = ∅ ↔ _
  rw [Module.support_eq_empty_iff]
  exact originalRightQuotient_subsingleton_iff I

theorem originalCentralCharacteristicSupport_empty_iff_one_mem
    (I : RingRightIdeal (R := R)) :
    OriginalCentralCharacteristicSupport I = ∅ ↔ (1 : R) ∈ I := by
  rw [originalCentralCharacteristicSupport_empty_iff_quotientIsZero,
    quotientIsZero_iff_one_mem]

/-- Under the independently proved finite-generation hypothesis, the support
is the zero locus of its actual central annihilator. -/
theorem originalCentralCharacteristicSupport_eq_zeroLocus_annihilator
    (I : RingRightIdeal (R := R))
    [Module.Finite (Subring.center R) (OriginalRightQuotient I)] :
    OriginalCentralCharacteristicSupport I =
      PrimeSpectrum.zeroLocus
        (Module.annihilator (Subring.center R) (OriginalRightQuotient I) :
          Set (Subring.center R)) := by
  exact Module.support_eq_zeroLocus

end CentralSupport

section DimensionDefect

/-- The integer defect corresponding to a bottom-extended natural dimension:
`⊥` is the paper's `-1`, and a finite dimension `n` is cast to `Int`. -/
def supportDimensionDefect : SupportDimension → Int :=
  WithBot.recBotCoe (-1) (fun n : Nat => (n : Int))

@[simp] theorem supportDimensionDefect_bot :
    supportDimensionDefect (⊥ : SupportDimension) = -1 := rfl

@[simp] theorem supportDimensionDefect_coe (n : Nat) :
    supportDimensionDefect (n : SupportDimension) = (n : Int) := rfl

theorem supportDimensionDefect_eq_neg_one_iff
    (d : SupportDimension) :
    supportDimensionDefect d = -1 ↔ d = (⊥ : SupportDimension) := by
  induction d using WithBot.recBotCoe with
  | bot => simp
  | coe n =>
      change (n : Int) = -1 ↔ (n : SupportDimension) = (⊥ : SupportDimension)
      constructor
      · intro h
        have hn0 : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
        have hneg : (-1 : Int) < (n : Int) :=
          lt_of_lt_of_le (by norm_num) hn0
        exact False.elim ((ne_of_gt hneg) h)
      · intro h
        exact False.elim ((WithBot.coe_ne_bot :
          (n : SupportDimension) ≠ (⊥ : SupportDimension)) h)

theorem supportDimensionDefect_le_neg_one_iff
    (d : SupportDimension) :
    supportDimensionDefect d ≤ -1 ↔ d = (⊥ : SupportDimension) := by
  induction d using WithBot.recBotCoe with
  | bot => simp
  | coe n =>
      change (n : Int) ≤ -1 ↔ (n : SupportDimension) = (⊥ : SupportDimension)
      constructor
      · intro h
        have hn0 : (0 : Int) ≤ (n : Int) := Int.natCast_nonneg n
        have hneg : (-1 : Int) < (n : Int) :=
          lt_of_lt_of_le (by norm_num) hn0
        exact False.elim ((not_lt_of_ge h) hneg)
      · intro h
        exact False.elim ((WithBot.coe_ne_bot :
          (n : SupportDimension) ≠ (⊥ : SupportDimension)) h)

/-- A support/dimension datum whose integer defect is definitionally tied to
its `WithBot Nat` dimension, rather than supplied as an unrelated integer. -/
structure DimensionDefectWitness where
  dimension : SupportDimension
  defect : Int
  defect_eq_dimension : defect = supportDimensionDefect dimension

theorem DimensionDefectWitness.bot_iff_defect_le_neg_one
    (w : DimensionDefectWitness) :
    w.dimension = (⊥ : SupportDimension) ↔ w.defect ≤ -1 := by
  rw [w.defect_eq_dimension, supportDimensionDefect_le_neg_one_iff]

theorem DimensionDefectWitness.bot_of_defect_le_neg_one
    (w : DimensionDefectWitness) (h : w.defect ≤ -1) :
    w.dimension = (⊥ : SupportDimension) :=
  w.bot_iff_defect_le_neg_one.mpr h

end DimensionDefect

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.originalRightQuotient_mk_eq_zero_iff_mem
#print axioms SymplecticStafford.Filtered.originalCentralCharacteristicSupport_empty_iff_one_mem
#print axioms SymplecticStafford.Filtered.DimensionDefectWitness.bot_of_defect_le_neg_one
