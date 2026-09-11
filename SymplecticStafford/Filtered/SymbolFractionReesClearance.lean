import Mathlib.Tactic
import SymplecticStafford.Filtered.SymbolFractionRees

namespace SymplecticStafford.Filtered.SymbolFractionRees

universe u

noncomputable section

open SymplecticStafford
open SymbolDenominatorSubmonoid
open SymbolFractionInverse
open SymbolFractionFiltration
open AlgebraicAnalysis.OreRightLocalization

variable {R : Type u} [Ring R]

namespace Clearance

variable (C : SymbolFractionFiltration.Data R)

private noncomputable def regularSymbol
    (s : C.inverse.localization.denominators) :
    RegularSymbolDegree.Data C.inverse.filtration
      (C.inverse.denominator_degree s) := by
  let ha := C.inverse.denominator_admissible s
  let hs := ha.choose
  let hSigma := ha.choose_spec
  exact
    { representative := (s : R)
      representative_mem := hs
      symbol_ne_zero :=
        associatedClass_ne_zero_of_mem_sigma C.inverse.filtration
          C.inverse.symbols hSigma
      left_regular := fun j y hy => C.left_regular s _ hs hSigma j y hy }

private theorem regular_cofactor_control
    (s : C.inverse.localization.denominators)
    {x : R} {n : ℕ} (hx : (s : R) * x ∈ C.inverse.filtration.carrier n) :
    (C.inverse.denominator_degree s ≤ n →
        x ∈ C.inverse.filtration.carrier
          (n - C.inverse.denominator_degree s)) ∧
      (n < C.inverse.denominator_degree s → x = 0) := by
  exact (regularSymbol C s).degree_controlled_mul hx

private theorem right_ore_common
    (a : R) (s : C.inverse.localization.denominators) :
    ∃ t : C.inverse.localization.denominators, ∃ c : R,
      a * (t : R) = (s : R) * c := by
  letI : OreLocalization.OreSet
      (oppositeSubmonoid C.inverse.localization.denominators) :=
    C.inverse.localization.ore
  let s' : oppositeSubmonoid C.inverse.localization.denominators :=
    ⟨MulOpposite.op (s : R), s.property⟩
  rcases OreLocalization.oreCondition (MulOpposite.op a) s' with
    ⟨c', t', ht⟩
  refine ⟨⟨(t' : Rᵐᵒᵖ).unop, t'.property⟩, (c' : Rᵐᵒᵖ).unop, ?_⟩
  exact congrArg MulOpposite.unop ht

private theorem denominator_degree_mul
    (s t : C.inverse.localization.denominators) :
    C.inverse.denominator_degree (s * t) =
      C.inverse.denominator_degree s + C.inverse.denominator_degree t := by
  have hs : (s : R) ∈ submonoid C.inverse.filtration C.inverse.symbols := by
    rw [← C.inverse.denominators_eq_submonoid]
    exact s.property
  have ht : (t : R) ∈ submonoid C.inverse.filtration C.inverse.symbols := by
    rw [← C.inverse.denominators_eq_submonoid]
    exact t.property
  simpa [SymbolFractionInverse.Data.denominator_degree] using
    (degree_mul C.inverse.filtration C.inverse.symbols hs ht)

private theorem finite_right_clear
    (q : ℤ → T C) (S : Finset ℤ)
    (hnz : ∀ z ∈ S, q z ≠ 0)
    (hq : ∀ z ∈ S, q z ∈ C.fractionFiltration z) :
    ∃ s : C.inverse.localization.denominators,
      ∀ z ∈ S, ∃ (a : R) (d : ℕ),
        a ∈ C.inverse.filtration.carrier d ∧
        q z * C.inverse.localization.numerator (s : R) =
          C.inverse.localization.numerator a ∧
        Int.ofNat d ≤ z + Int.ofNat (C.inverse.denominator_degree s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | @insert z S hz ih =>
      rcases ih (fun w hw => hnz w (by simp [hw]))
          (fun w hw => hq w (by simp [hw])) with ⟨s, hs⟩
      have hzmem : z ∈ insert z S := Finset.mem_insert_self z S
      have hzq := hq z hzmem
      change C.inverse.fractionDegreeAtMost z (q z) at hzq
      rcases hzq with hzero | ⟨a, t, d, ha, hclear, hdeg⟩
      · exact (hnz z hzmem hzero).elim
      · rcases right_ore_common C (s : R) t with ⟨u, c, hcommon⟩
        let common : C.inverse.localization.denominators := s * u
        let ds := C.inverse.denominator_degree s
        let du := C.inverse.denominator_degree u
        let dt := C.inverse.denominator_degree t
        have hsu : (s : R) * (u : R) ∈
            C.inverse.filtration.carrier (ds + du) :=
          C.inverse.filtration.mul_mem
            (C.inverse.denominator_admissible s).choose
            (C.inverse.denominator_admissible u).choose
        have htc : (t : R) * c ∈
            C.inverse.filtration.carrier (ds + du) := by
          rw [← hcommon]
          exact hsu
        have hcontrol := regular_cofactor_control C t htc
        have hdt : dt ≤ ds + du := by
          by_contra hnot
          have hc0 := hcontrol.2 (Nat.lt_of_not_ge hnot)
          have hbad : ((common : C.inverse.localization.denominators) : R) = 0 := by
            change (s : R) * (u : R) = 0
            rw [hcommon, hc0, mul_zero]
          have hmem : (0 : R) ∈ submonoid C.inverse.filtration C.inverse.symbols := by
            rw [← C.inverse.denominators_eq_submonoid]
            rw [← hbad]
            exact common.property
          exact zero_not_mem C.inverse.filtration C.inverse.symbols hmem
        have hc : c ∈ C.inverse.filtration.carrier (ds + du - dt) :=
          hcontrol.1 hdt
        refine ⟨common, ?_⟩
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwS
        · refine ⟨a * c, d + (ds + du - dt),
            C.inverse.filtration.mul_mem ha hc, ?_, ?_⟩
          · change q w * C.inverse.localization.numerator ((s : R) * (u : R)) = _
            calc
              q w * C.inverse.localization.numerator ((s : R) * (u : R)) =
                  q w * C.inverse.localization.numerator ((t : R) * c) := by
                    rw [hcommon]
              _ = (q w * C.inverse.localization.numerator (t : R)) *
                    C.inverse.localization.numerator c := by
                    rw [map_mul]
                    simp only [mul_assoc]
              _ = C.inverse.localization.numerator (a * c) := by
                    rw [hclear, map_mul]
          · have hsub : Int.ofNat (ds + du - dt) =
                Int.ofNat (ds + du) - Int.ofNat dt := Int.ofNat_sub hdt
            have hcommonDeg := denominator_degree_mul C s u
            dsimp [common, ds, du, dt] at *
            rw [hcommonDeg]
            omega
        · rcases hs w hwS with ⟨b, e, hb, hbclear, hbdeg⟩
          refine ⟨b * (u : R), e + du,
            C.inverse.filtration.mul_mem hb
              (C.inverse.denominator_admissible u).choose, ?_, ?_⟩
          · change q w * C.inverse.localization.numerator ((s : R) * (u : R)) = _
            rw [map_mul, ← mul_assoc, hbclear, map_mul]
          · have hcommonDeg := denominator_degree_mul C s u
            dsimp [common, ds, du] at *
            rw [hcommonDeg]
            omega

/-- A finite Laurent Rees element has one selected homogeneous denominator
which clears every nonzero coefficient on the right with its integer degree
bound preserved. -/
theorem support_right_clear (p : ReesRing C) :
    ∃ s : C.inverse.localization.denominators,
      ∀ z ∈ (p : LaurentPolynomial C).coeff.support,
        ∃ (a : R) (d : ℕ),
          a ∈ C.inverse.filtration.carrier d ∧
          (p : LaurentPolynomial C).coeff z *
              C.inverse.localization.numerator (s : R) =
            C.inverse.localization.numerator a ∧
          Int.ofNat d ≤ z +
            Int.ofNat (C.inverse.denominator_degree s) := by
  apply finite_right_clear C
  · intro z hz
    simpa [Finsupp.mem_support_iff] using hz
  · intro z _hz
    exact p.property z

end Clearance

end

end SymplecticStafford.Filtered.SymbolFractionRees

#print axioms
  SymplecticStafford.Filtered.SymbolFractionRees.Clearance.support_right_clear
