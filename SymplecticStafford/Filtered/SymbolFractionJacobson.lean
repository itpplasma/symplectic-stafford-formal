module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Tactic
public import SymplecticStafford.Filtered.SymbolFractionFiltration

@[expose] public section

/-!
# The degree `-1` layer and the Jacobson radical of degree zero

For an actual selected right Ore localization with regular selected symbols,
the degree `-1` fractions have equal-degree geometric inverses: `1 - q` is a
unit in the degree-zero subring.  The final theorem records the corresponding
left-ideal statement using Mathlib's noncommutative Jacobson criterion.

No Rees-Noetherianity or length-transfer assertion is made here.
-/

namespace SymplecticStafford.Filtered

universe u

open SymplecticStafford
open SymbolDenominatorSubmonoid
open SymbolFractionInverse
open AlgebraicAnalysis.OreRightLocalization

namespace SymbolFractionJacobson

variable {R : Type u} [Ring R]

variable (C : SymbolFractionFiltration.Data R)

private theorem rightFraction_mul_denominator
    (a : R) (s : C.inverse.localization.denominators) :
    C.inverse.rightFraction a s * C.inverse.localization.numerator (s : R) =
      C.inverse.localization.numerator a := by
  letI : OreLocalization.OreSet
      (oppositeSubmonoid C.inverse.localization.denominators) :=
    C.inverse.localization.ore
  apply MulOpposite.unop_injective
  rw [show C.inverse.rightFraction a s = MulOpposite.op
      (OreLocalization.oreDiv (MulOpposite.op a)
        (⟨MulOpposite.op (s : R), s.property⟩ :
          oppositeSubmonoid C.inverse.localization.denominators)) by
        rfl]
  exact OreLocalization.mul_cancel
    (R := Rᵐᵒᵖ)
    (S := oppositeSubmonoid C.inverse.localization.denominators)
    (r := MulOpposite.op a)
    (s := (⟨MulOpposite.op (s : R), s.property⟩ :
      oppositeSubmonoid C.inverse.localization.denominators))
    (t := (1 : oppositeSubmonoid C.inverse.localization.denominators))

private theorem rightFraction_eq_of_clear
    {q : C.inverse.localization.Localization} {a : R}
    (s : C.inverse.localization.denominators)
    (hclear : q * C.inverse.localization.numerator (s : R) =
      C.inverse.localization.numerator a) :
    q = C.inverse.rightFraction a s := by
  apply (C.inverse.localization.denominator_unit s).mul_right_cancel
  calc
    q * C.inverse.localization.numerator (s : R) =
        C.inverse.localization.numerator a := hclear
    _ = C.inverse.rightFraction a s *
        C.inverse.localization.numerator (s : R) :=
      (rightFraction_mul_denominator C a s).symm

/-- The element `1 - q`, with its degree-zero membership made explicit. -/
def oneSubDegreeZero
    {q : C.inverse.localization.Localization}
    (hq : q ∈ C.fractionFiltration (-1)) :
    C.degreeZeroSubring := by
  have hq0 : q ∈ C.fractionFiltration 0 :=
    C.fractionFiltration_mono (by norm_num) hq
  have hone : (1 : C.inverse.localization.Localization) ∈
      C.fractionFiltration 0 := C.degreeZeroSubring.one_mem
  exact ⟨1 - q, (C.fractionFiltration 0).sub_mem hone hq0⟩

theorem isUnit_oneSubDegreeZero
    {q : C.inverse.localization.Localization}
    (hq : q ∈ C.fractionFiltration (-1)) :
    IsUnit (oneSubDegreeZero C hq) := by
  let hq_orig := hq
  change C.inverse.fractionDegreeAtMost (-1 : ℤ) q at hq
  rcases hq with hzero | ⟨a, s, da, ha, hclear, hdeg⟩
  · subst q
    have hu : oneSubDegreeZero C hq_orig =
        (1 : C.degreeZeroSubring) := by
      apply Subtype.ext
      simp [oneSubDegreeZero]
    rw [hu]
    exact isUnit_one
  · have hda : da < C.inverse.denominator_degree s := by
      by_contra hnot
      have hle : C.inverse.denominator_degree s ≤ da :=
        Nat.le_of_not_gt hnot
      have hle' : (Int.ofNat (C.inverse.denominator_degree s) : ℤ) ≤
          Int.ofNat da := by
        exact Int.ofNat_le.mpr hle
      have hnonneg : (0 : ℤ) ≤
          Int.ofNat da - Int.ofNat (C.inverse.denominator_degree s) :=
        sub_nonneg.mpr hle'
      omega
    rcases C.inverse.denominator_admissible s with ⟨hs, hSigma⟩
    rcases C.inverse.one_sub_rightFraction_mul_inverse hs hSigma ha hda with
      ⟨ss, tt, hss, htt, hleft, hright⟩
    have hclear_ss : q * C.inverse.localization.numerator (ss : R) =
        C.inverse.localization.numerator a := by
      simpa [hss] using hclear
    have hqfrac : q = C.inverse.rightFraction a ss :=
      rightFraction_eq_of_clear C ss hclear_ss
    have hmem0 := C.inverse.inverse_mem_degreeZeroFractionSet hs hSigma ha hda
    rcases hmem0 with ⟨ss0, tt0, hss0, htt0, hmem0⟩
    have hss_eq : ss0 = ss := by
      apply Subtype.ext
      exact hss0.trans hss.symm
    have htt_eq : tt0 = tt := by
      apply Subtype.ext
      exact htt0.trans htt.symm
    have hmem : C.inverse.rightFraction (ss : R) tt ∈
        C.fractionFiltration 0 := by
      change C.inverse.fractionDegreeAtMost 0
        (C.inverse.rightFraction (ss : R) tt)
      change C.inverse.fractionDegreeAtMost 0
        (C.inverse.rightFraction (ss0 : R) tt0) at hmem0
      simpa [hss_eq, htt_eq] using hmem0
    let v : C.degreeZeroSubring :=
      ⟨C.inverse.rightFraction (ss : R) tt, hmem⟩
    have hleft' : oneSubDegreeZero C hq_orig * v = 1 := by
      apply Subtype.ext
      change (1 - q) * C.inverse.rightFraction (ss : R) tt = 1
      simpa [hqfrac, oneSubDegreeZero] using hleft
    have hright' : v * oneSubDegreeZero C hq_orig = 1 := by
      apply Subtype.ext
      change C.inverse.rightFraction (ss : R) tt *
          (1 - q) = 1
      simpa [hqfrac, oneSubDegreeZero] using hright
    refine ⟨⟨oneSubDegreeZero C hq_orig, v, hleft', hright'⟩, rfl⟩

/-- The degree `-1` fractions form a left ideal in the degree-zero subring. -/
def degreeMinusOneIdeal : Ideal C.degreeZeroSubring where
  carrier := {q | (q : C.inverse.localization.Localization) ∈
    C.fractionFiltration (-1)}
  zero_mem' := by
    change (0 : C.inverse.localization.Localization) ∈
      C.fractionFiltration (-1)
    exact (C.fractionFiltration (-1)).zero_mem
  add_mem' := by
    intro q r hq hr
    change ((q + r : C.degreeZeroSubring) :
      C.inverse.localization.Localization) ∈ C.fractionFiltration (-1)
    change (q : C.inverse.localization.Localization) +
      (r : C.inverse.localization.Localization) ∈ C.fractionFiltration (-1)
    exact (C.fractionFiltration (-1)).add_mem hq hr
  smul_mem' := by
    intro b q hq
    change ((b • q : C.degreeZeroSubring) :
      C.inverse.localization.Localization) ∈ C.fractionFiltration (-1)
    change (b : C.inverse.localization.Localization) *
      (q : C.inverse.localization.Localization) ∈ C.fractionFiltration (-1)
    have hb : (b : C.inverse.localization.Localization) ∈
        C.fractionFiltration 0 := b.property
    simpa using C.fractionFiltration_mul_mem (z := 0) (w := -1) hb hq

theorem degreeMinusOneIdeal_le_jacobson :
    degreeMinusOneIdeal C ≤
      (⊥ : Ideal C.degreeZeroSubring).jacobson := by
  intro q hq
  rw [Ideal.mem_jacobson_iff]
  intro b
  have hbq : ((b * q : C.degreeZeroSubring) :
      C.inverse.localization.Localization) ∈ C.fractionFiltration (-1) := by
    change (b : C.inverse.localization.Localization) *
      (q : C.inverse.localization.Localization) ∈ C.fractionFiltration (-1)
    have hb : (b : C.inverse.localization.Localization) ∈
        C.fractionFiltration 0 := b.property
    exact (by simpa using
      C.fractionFiltration_mul_mem (z := 0) (w := -1) hb hq)
  have hneg : ((-(b * q : C.degreeZeroSubring)) :
      C.inverse.localization.Localization) ∈ C.fractionFiltration (-1) := by
    change -((b : C.inverse.localization.Localization) *
      (q : C.inverse.localization.Localization)) ∈
        C.fractionFiltration (-1)
    exact (C.fractionFiltration (-1)).neg_mem hbq
  have hu := isUnit_oneSubDegreeZero C hneg
  rcases hu with ⟨u, huval⟩
  let z : C.degreeZeroSubring := u.inv
  refine ⟨z, ?_⟩
  apply (Submodule.mem_bot C.degreeZeroSubring).2
  have hz : z * oneSubDegreeZero C hneg = 1 := by
    dsimp [z]
    change u.inv * oneSubDegreeZero C hneg = 1
    rw [← huval]
    exact u.inv_val
  have hz' := congrArg (fun x : C.degreeZeroSubring =>
    (x : C.inverse.localization.Localization)) hz
  change (z : C.inverse.localization.Localization) *
      (oneSubDegreeZero C hneg : C.inverse.localization.Localization) = 1 at hz'
  have hplus : (oneSubDegreeZero C hneg :
      C.inverse.localization.Localization) =
      1 + (b : C.inverse.localization.Localization) *
        (q : C.inverse.localization.Localization) := by
    simp [oneSubDegreeZero]
  rw [hplus] at hz'
  change (z : C.degreeZeroSubring) * b * q + z - 1 = 0
  apply Subtype.ext
  change (z : C.inverse.localization.Localization) *
      (b : C.inverse.localization.Localization) *
        (q : C.inverse.localization.Localization) +
      (z : C.inverse.localization.Localization) - 1 = 0
  calc
    (z : C.inverse.localization.Localization) *
          (b : C.inverse.localization.Localization) *
          (q : C.inverse.localization.Localization) +
        (z : C.inverse.localization.Localization) - 1 =
        (z : C.inverse.localization.Localization) *
          (1 + (b : C.inverse.localization.Localization) *
            (q : C.inverse.localization.Localization)) - 1 := by
              noncomm_ring
    _ = 0 := by rw [hz', sub_self]

end SymbolFractionJacobson

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.SymbolFractionJacobson.isUnit_oneSubDegreeZero
#print axioms
  SymplecticStafford.Filtered.SymbolFractionJacobson.degreeMinusOneIdeal_le_jacobson
