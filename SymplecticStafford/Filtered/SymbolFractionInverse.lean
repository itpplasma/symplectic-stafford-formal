import SymplecticStafford.Filtered.SymbolDenominatorSubmonoid
import SymplecticStafford.Filtered.FullSymbolRightLocalization

/-!
# Lower perturbations and a degree-zero fraction witness

This file records the small algebraic step available from the actual selected
symbol submonoid.  A selected representative at degree `n` cannot have a
selected representative at a lower degree: after monotone reindexing its
degree-`n` associated class would be zero.  Consequently subtraction by a
strictly lower filtered element preserves the selected degree.

The localization part uses an explicitly supplied right Ore localization whose
denominators are exactly the selected original-ring submonoid.  Fractions are
defined through the opposite-ring Ore quotient.  The displayed inverse of
`1 - a/s` is then the original-ring right fraction `s/(s-a)`.  Its membership
in the degree-zero fraction predicate is witnessed by numerator `s`,
denominator `s-a`, and the two equal selected degrees.

No closure property of the degree-zero predicate is asserted.
-/

namespace SymplecticStafford.Filtered

universe u

open SymplecticStafford

namespace SymbolDenominatorSubmonoid

variable {R : Type u} [Ring R]

/- Every admissible witness is the least selected degree for that original
   element.  A lower witness would make the selected class at `n` zero. -/
theorem degree_eq_of_admissible
    (F : AdditiveFilteredRingData R) (D : Data F)
    {a : R} {n : ℕ} (hna : Admissible F D a n) :
    degree F D (show a ∈ submonoid F D from ⟨n, hna⟩) = n := by
  have hmin : ∀ m < n, ¬ Admissible F D a m := by
    intro m hmn hma
    rcases hma with ⟨hm, hSigma⟩
    rcases hna with ⟨hn, hnSigma⟩
    have hpred : a ∈ AdditiveFilteredRingData.predecessor F n := by
      by_cases hn0 : n = 0
      · omega
      · rw [AdditiveFilteredRingData.predecessor, if_neg hn0]
        exact F.monotone (by omega) hm
    have hzero :=
      (AdditiveFilteredRingData.associatedClass_eq_zero_iff F n a hn).mpr hpred
    exact associatedClass_ne_zero_of_mem_sigma F D hnSigma hzero
  exact degree_eq_of_minimal F D hna hmin

/- The selected degree is preserved by a strictly lower perturbation. -/
theorem degree_sub_eq_of_selected_symbol
    (F : AdditiveFilteredRingData R) (D : Data F)
    {s u : R} {n da : ℕ}
    (hs : s ∈ F.carrier n)
    (hSigma : AdditiveFilteredRingData.associatedClass F n s hs ∈ D.Sigma n)
    (hu : u ∈ F.carrier da) (hda : da < n) :
    degree F D
        (show s - u ∈ submonoid F D from
          (sub_mem_of_selected_symbol F D hs hSigma
            (by
              by_cases hn0 : n = 0
              · omega
              · rw [AdditiveFilteredRingData.predecessor, if_neg hn0]
                exact F.monotone (by omega) hu))) = n := by
  let hpred : u ∈ AdditiveFilteredRingData.predecessor F n := by
    by_cases hn0 : n = 0
    · omega
    · rw [AdditiveFilteredRingData.predecessor, if_neg hn0]
      exact F.monotone (by omega) hu
  let hsu : s - u ∈ submonoid F D :=
    sub_mem_of_selected_symbol F D hs hSigma hpred
  have hsu_carrier : s - u ∈ F.carrier n := by
    exact (F.carrier n).sub_mem hs (F.predecessor_le n hpred)
  have hsu_class :
      AdditiveFilteredRingData.associatedClass F n (s - u) hsu_carrier ∈
        D.Sigma n := by
    rw [associatedClass_sub_eq_of_mem_predecessor F hs hpred]
    exact hSigma
  have hna : Admissible F D (s - u) n := ⟨hsu_carrier, hsu_class⟩
  exact degree_eq_of_admissible F D hna

end SymbolDenominatorSubmonoid

namespace SymbolFractionInverse

variable {R : Type u} [Ring R]

open SymbolDenominatorSubmonoid
open AlgebraicAnalysis.OreRightLocalization

/- A full-symbol right localization attached to the actual selected
   original-ring submonoid. -/
structure Data (R : Type u) [Ring R] where
  filtration : AdditiveFilteredRingData R
  symbols : SymbolDenominatorSubmonoid.Data filtration
  localization : FullSymbolRightLocalization.Data R
  denominators_eq_submonoid :
    localization.denominators =
      SymbolDenominatorSubmonoid.submonoid filtration symbols

namespace Data

variable (C : Data R)

private theorem mem_submonoid_of_denominator
    (s : C.localization.denominators) :
    (s : R) ∈ SymbolDenominatorSubmonoid.submonoid C.filtration C.symbols := by
  rw [← C.denominators_eq_submonoid]
  exact s.property

noncomputable def denominator_degree
    (s : C.localization.denominators) :
    ℕ :=
  SymbolDenominatorSubmonoid.degree C.filtration C.symbols
    (C.mem_submonoid_of_denominator s)

theorem denominator_admissible
    (s : C.localization.denominators) :
    SymbolDenominatorSubmonoid.Admissible C.filtration C.symbols
      (s : R) (C.denominator_degree s) :=
  by
    dsimp [denominator_degree]
    exact SymbolDenominatorSubmonoid.degree_spec C.filtration C.symbols
      (C.mem_submonoid_of_denominator s)

/- The right fraction `a/s`, implemented by the opposite-ring Ore quotient. -/
noncomputable def rightFraction
    (a : R) (s : C.localization.denominators) :
    C.localization.Localization := by
  letI : OreLocalization.OreSet
      (oppositeSubmonoid C.localization.denominators) := C.localization.ore
  exact MulOpposite.op
    (OreLocalization.oreDiv (MulOpposite.op a)
      (⟨MulOpposite.op (s : R), s.property⟩ :
        oppositeSubmonoid C.localization.denominators))

private theorem rightFraction_mul_denominator
    (a : R) (s : C.localization.denominators) :
    C.rightFraction a s * C.localization.numerator (s : R) =
      C.localization.numerator a := by
  letI : OreLocalization.OreSet
      (oppositeSubmonoid C.localization.denominators) := C.localization.ore
  apply MulOpposite.unop_injective
  rw [show C.rightFraction a s = MulOpposite.op
      (OreLocalization.oreDiv (MulOpposite.op a)
        (⟨MulOpposite.op (s : R), s.property⟩ :
          oppositeSubmonoid C.localization.denominators)) by
        rfl]
  exact OreLocalization.mul_cancel
    (R := Rᵐᵒᵖ)
    (S := oppositeSubmonoid C.localization.denominators)
    (r := MulOpposite.op a)
    (s := (⟨MulOpposite.op (s : R), s.property⟩ :
      oppositeSubmonoid C.localization.denominators))
    (t := (1 : oppositeSubmonoid C.localization.denominators))

private theorem cancel_right_denominator
    {x y : C.localization.Localization}
    (s : C.localization.denominators)
    (h : x * C.localization.numerator (s : R) =
      y * C.localization.numerator (s : R)) :
    x = y :=
  (C.localization.denominator_unit s).mul_right_cancel h

private theorem rightFraction_same_denominator_sub
    {a : R} (s : C.localization.denominators)
    (_hsa : (s : R) - a ∈
      SymbolDenominatorSubmonoid.submonoid C.filtration C.symbols) :
    C.rightFraction ((s : R) - a) s =
      1 - C.rightFraction a s := by
  apply cancel_right_denominator C s
  calc
    C.rightFraction ((s : R) - a) s * C.localization.numerator (s : R) =
        C.localization.numerator ((s : R) - a) :=
      rightFraction_mul_denominator C ((s : R) - a) s
    _ = C.localization.numerator (s : R) - C.localization.numerator a := by
      rw [map_sub]
    _ = (1 - C.rightFraction a s) * C.localization.numerator (s : R) := by
      rw [sub_mul, one_mul, rightFraction_mul_denominator]

/- The inverse numerator and denominator are equal-degree in the supplied
   selected filtration.  The proof keeps the actual denominator subtype. -/
theorem sub_mem_and_degree_eq
    {s a : R} {n da : ℕ}
    (hs : s ∈ C.filtration.carrier n)
    (hSigma : AdditiveFilteredRingData.associatedClass C.filtration n s hs ∈
      C.symbols.Sigma n)
    (ha : a ∈ C.filtration.carrier da) (hda : da < n) :
    ∃ ht : (s - a) ∈
        SymbolDenominatorSubmonoid.submonoid C.filtration C.symbols,
      SymbolDenominatorSubmonoid.degree C.filtration C.symbols ht = n := by
  let hpred : a ∈ AdditiveFilteredRingData.predecessor C.filtration n := by
    by_cases hn0 : n = 0
    · omega
    · rw [AdditiveFilteredRingData.predecessor, if_neg hn0]
      exact C.filtration.monotone (by omega) ha
  let ht : (s - a) ∈
      SymbolDenominatorSubmonoid.submonoid C.filtration C.symbols :=
    SymbolDenominatorSubmonoid.sub_mem_of_selected_symbol C.filtration
      C.symbols hs hSigma hpred
  have ht_carrier : s - a ∈ C.filtration.carrier n := by
    exact (C.filtration.carrier n).sub_mem hs
      (C.filtration.predecessor_le n hpred)
  have ht_class :
      AdditiveFilteredRingData.associatedClass C.filtration n (s - a)
          ht_carrier ∈ C.symbols.Sigma n := by
    rw [SymbolDenominatorSubmonoid.associatedClass_sub_eq_of_mem_predecessor
      C.filtration hs hpred]
    exact hSigma
  have hta : SymbolDenominatorSubmonoid.Admissible C.filtration C.symbols
      (s - a) n := ⟨ht_carrier, ht_class⟩
  refine ⟨ht, ?_⟩
  exact SymbolDenominatorSubmonoid.degree_eq_of_admissible
    C.filtration C.symbols hta

/- A degree bound for right-localized fractions.  The `q = 0` branch is kept
   explicit because the proposed set is only a predicate at this stage. -/
def fractionDegreeAtMost (z : ℤ)
    (q : C.localization.Localization) : Prop :=
  q = 0 ∨ ∃ (a : R) (s : C.localization.denominators) (da : ℕ),
    a ∈ C.filtration.carrier da ∧
    q * C.localization.numerator (s : R) = C.localization.numerator a ∧
    (Int.ofNat da - Int.ofNat (C.denominator_degree s)) ≤ z

def degreeZeroFractionSet : Set C.localization.Localization :=
  {q | C.fractionDegreeAtMost 0 q}

theorem inverse_mem_degreeZeroFractionSet
    {s a : R} {n da : ℕ}
    (hs : s ∈ C.filtration.carrier n)
    (hSigma : AdditiveFilteredRingData.associatedClass C.filtration n s hs ∈
      C.symbols.Sigma n)
    (ha : a ∈ C.filtration.carrier da) (hda : da < n) :
    ∃ (ss : C.localization.denominators)
      (tt : C.localization.denominators),
      (ss : R) = s ∧ (tt : R) = s - a ∧
      C.rightFraction (ss : R) tt ∈ C.degreeZeroFractionSet := by
  have hs_sub : s ∈
      SymbolDenominatorSubmonoid.submonoid C.filtration C.symbols :=
    ⟨n, ⟨hs, hSigma⟩⟩
  have hsub : (s - a) ∈
      SymbolDenominatorSubmonoid.submonoid C.filtration C.symbols := by
    rcases C.sub_mem_and_degree_eq hs hSigma ha hda with ⟨ht, _⟩
    exact ht
  let ss : C.localization.denominators :=
    ⟨s, by rw [C.denominators_eq_submonoid]; exact hs_sub⟩
  let tt : C.localization.denominators :=
    ⟨s - a, by rw [C.denominators_eq_submonoid]; exact hsub⟩
  have hss : (ss : R) = s := rfl
  have htt : (tt : R) = s - a := rfl
  have hdeg_t : C.denominator_degree tt = n := by
    rcases C.sub_mem_and_degree_eq hs hSigma ha hda with ⟨ht, htn⟩
    simpa [denominator_degree, tt] using htn
  refine ⟨ss, tt, hss, htt, ?_⟩
  change C.fractionDegreeAtMost 0 (C.rightFraction (ss : R) tt)
  refine Or.inr ⟨s, tt, n, hs, ?_, ?_⟩
  · simpa [hss] using rightFraction_mul_denominator C s tt
  · simp [hdeg_t]

/- The actual inverse identity.  It is stated separately from the set
   membership theorem so no closure or field structure is inferred. -/
theorem one_sub_rightFraction_mul_inverse
    {s a : R} {n da : ℕ}
    (hs : s ∈ C.filtration.carrier n)
    (hSigma : AdditiveFilteredRingData.associatedClass C.filtration n s hs ∈
      C.symbols.Sigma n)
    (ha : a ∈ C.filtration.carrier da) (hda : da < n) :
    ∃ (ss tt : C.localization.denominators),
      (ss : R) = s ∧ (tt : R) = s - a ∧
      (1 - C.rightFraction a ss) * C.rightFraction (ss : R) tt = 1 ∧
      C.rightFraction (ss : R) tt *
          (1 - C.rightFraction a ss) = 1 := by
  have hs_sub : s ∈
      SymbolDenominatorSubmonoid.submonoid C.filtration C.symbols :=
    ⟨n, ⟨hs, hSigma⟩⟩
  have hsub : (s - a) ∈
      SymbolDenominatorSubmonoid.submonoid C.filtration C.symbols := by
    rcases C.sub_mem_and_degree_eq hs hSigma ha hda with ⟨ht, _⟩
    exact ht
  let ss : C.localization.denominators :=
    ⟨s, by rw [C.denominators_eq_submonoid]; exact hs_sub⟩
  let tt : C.localization.denominators :=
    ⟨s - a, by rw [C.denominators_eq_submonoid]; exact hsub⟩
  have hss : (ss : R) = s := rfl
  have htt : (tt : R) = s - a := rfl
  have hleft :
      (1 - C.rightFraction a ss) * C.rightFraction (ss : R) tt = 1 := by
    apply cancel_right_denominator C tt
    calc
      ((1 - C.rightFraction a ss) * C.rightFraction (ss : R) tt) *
          C.localization.numerator (tt : R) =
          (1 - C.rightFraction a ss) *
            (C.rightFraction (ss : R) tt *
              C.localization.numerator (tt : R)) := by
                simp only [mul_assoc]
      _ = (1 - C.rightFraction a ss) *
            C.localization.numerator (ss : R) := by
              rw [rightFraction_mul_denominator]
      _ = C.localization.numerator (ss : R) -
            C.localization.numerator a := by
              rw [sub_mul, one_mul, rightFraction_mul_denominator]
      _ = C.localization.numerator ((ss : R) - a) := by
              rw [map_sub]
      _ = (1 : C.localization.Localization) *
            C.localization.numerator (tt : R) := by
              rw [hss, htt]
              simp
  have hright :
      C.rightFraction (ss : R) tt *
          (1 - C.rightFraction a ss) = 1 := by
    apply cancel_right_denominator C ss
    calc
      (C.rightFraction (ss : R) tt *
          (1 - C.rightFraction a ss)) *
            C.localization.numerator (ss : R) =
          C.rightFraction (ss : R) tt *
            ((1 - C.rightFraction a ss) *
              C.localization.numerator (ss : R)) := by
                simp only [mul_assoc]
      _ = C.rightFraction (ss : R) tt *
            (C.localization.numerator (ss : R) -
              C.localization.numerator a) := by
              rw [sub_mul, one_mul, rightFraction_mul_denominator]
      _ = C.rightFraction (ss : R) tt *
            C.localization.numerator (tt : R) := by
              rw [← map_sub, hss, htt]
      _ = C.localization.numerator (ss : R) :=
            rightFraction_mul_denominator C (ss : R) tt
      _ = (1 : C.localization.Localization) *
            C.localization.numerator (ss : R) := by simp
  exact ⟨ss, tt, hss, htt, hleft, hright⟩

end Data

end SymbolFractionInverse

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.SymbolDenominatorSubmonoid.degree_eq_of_admissible
#print axioms
  SymplecticStafford.Filtered.SymbolDenominatorSubmonoid.degree_sub_eq_of_selected_symbol
#print axioms
  SymplecticStafford.Filtered.SymbolFractionInverse.Data.inverse_mem_degreeZeroFractionSet
#print axioms
  SymplecticStafford.Filtered.SymbolFractionInverse.Data.one_sub_rightFraction_mul_inverse
