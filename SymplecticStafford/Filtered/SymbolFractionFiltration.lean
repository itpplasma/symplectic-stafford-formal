module

public import Mathlib.Tactic
public import SymplecticStafford.Filtered.SymbolFractionInverse
public import SymplecticStafford.Filtered.RegularSymbolDegree

@[expose] public section

/-!
# The degree-controlled filtration on a selected right localization

The fraction predicate from `SymbolFractionInverse` becomes an actual
integer-indexed filtration once the selected associated symbols are assumed
left regular on every associated layer.  The only localization input used
below is the supplied right Ore localization itself.  In particular, the
additive and multiplicative closure proofs construct their own Ore
cofactors and control their degrees with `RegularSymbolDegree`.
-/

namespace SymplecticStafford.Filtered

universe u

open SymplecticStafford
open SymbolDenominatorSubmonoid
open SymbolFractionInverse
open AlgebraicAnalysis.OreRightLocalization

namespace SymbolFractionFiltration

variable {R : Type u} [Ring R]

structure Data (R : Type u) [Ring R] where
  inverse : SymbolFractionInverse.Data R
  /-- Left regularity of every selected denominator symbol on every actual
      associated layer.  The filtration witness is deliberately explicit,
      so no choice of representatives is hidden in this hypothesis. -/
  left_regular :
    ∀ (s : inverse.localization.denominators) (n : ℕ)
      (hs : (s : R) ∈ inverse.filtration.carrier n)
      (_hSigma : AdditiveFilteredRingData.associatedClass
        inverse.filtration n (s : R) hs ∈ inverse.symbols.Sigma n)
      (j : ℕ) (y : AdditiveFilteredRingData.associatedLayer
        inverse.filtration j),
      AdditiveFilteredRingData.associatedLayerMul inverse.filtration n j
          (AdditiveFilteredRingData.associatedClass
            inverse.filtration n (s : R) hs) y = 0 →
        y = 0

namespace Data

variable (C : Data R)

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
      left_regular := by
        intro j y hy
        exact C.left_regular s _ hs hSigma j y hy }

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
  refine ⟨⟨(t' : Rᵐᵒᵖ).unop, t'.property⟩,
    (c' : Rᵐᵒᵖ).unop, ?_⟩
  have hu := congrArg MulOpposite.unop ht
  change a * (t' : Rᵐᵒᵖ).unop = (s : R) *
    (c' : Rᵐᵒᵖ).unop at hu
  exact hu

private theorem denominator_degree_mul
    (s t : C.inverse.localization.denominators) :
    C.inverse.denominator_degree (s * t) =
      C.inverse.denominator_degree s + C.inverse.denominator_degree t := by
  have hs : (s : R) ∈
      SymbolDenominatorSubmonoid.submonoid C.inverse.filtration
        C.inverse.symbols := by
    rw [← C.inverse.denominators_eq_submonoid]
    exact s.property
  have ht : (t : R) ∈
      SymbolDenominatorSubmonoid.submonoid C.inverse.filtration
        C.inverse.symbols := by
    rw [← C.inverse.denominators_eq_submonoid]
    exact t.property
  simpa [SymbolFractionInverse.Data.denominator_degree] using
    (SymbolDenominatorSubmonoid.degree_mul C.inverse.filtration
      C.inverse.symbols hs ht)

private theorem regular_cofactor_control
    (s : C.inverse.localization.denominators)
    {x : R} {n : ℕ} (hx : (s : R) * x ∈ C.inverse.filtration.carrier n) :
    (C.inverse.denominator_degree s ≤ n →
        x ∈ C.inverse.filtration.carrier
          (n - C.inverse.denominator_degree s)) ∧
      (n < C.inverse.denominator_degree s → x = 0) := by
  change (regularSymbol C s).representative * x ∈
    C.inverse.filtration.carrier n at hx
  exact (regularSymbol C s).degree_controlled_mul hx

private theorem cancel_denominator
    {x y : C.inverse.localization.Localization}
    (s : C.inverse.localization.denominators)
    (h : x * C.inverse.localization.numerator (s : R) =
      y * C.inverse.localization.numerator (s : R)) :
    x = y :=
  (C.inverse.localization.denominator_unit s).mul_right_cancel h

private theorem fractionDegreeAtMost_nonzero_rep
    {z : ℤ} {q : C.inverse.localization.Localization}
    (hq : q ≠ 0)
    (h : C.inverse.fractionDegreeAtMost z q) :
    ∃ (a : R) (s : C.inverse.localization.denominators) (da : ℕ),
      a ∈ C.inverse.filtration.carrier da ∧
      q * C.inverse.localization.numerator (s : R) =
        C.inverse.localization.numerator a ∧
      (Int.ofNat da -
        Int.ofNat (C.inverse.denominator_degree s)) ≤ z := by
  rcases h with hzero | h
  · exact (hq hzero).elim
  · exact h

theorem fractionDegreeAtMost_neg
    {z : ℤ} {q : C.inverse.localization.Localization}
    (hq : C.inverse.fractionDegreeAtMost z q) :
    C.inverse.fractionDegreeAtMost z (-q) := by
  rcases hq with rfl | ⟨a, s, da, ha, hq, hdeg⟩
  · exact Or.inl (by simp)
  · refine Or.inr ⟨-a, s, da, C.inverse.filtration.carrier da |>.neg_mem ha,
      ?_, hdeg⟩
    calc
      (-q) * C.inverse.localization.numerator (s : R) =
          -(q * C.inverse.localization.numerator (s : R)) := neg_mul q _
      _ = -C.inverse.localization.numerator a := by rw [hq]
      _ = C.inverse.localization.numerator (-a) := by rw [map_neg]

private theorem fractionDegreeAtMost_mono
    {z w : ℤ} (hzw : z ≤ w) {q : C.inverse.localization.Localization}
    (hq : C.inverse.fractionDegreeAtMost z q) :
    C.inverse.fractionDegreeAtMost w q := by
  rcases hq with hzero | ⟨a, s, da, ha, hrep, hdeg⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨a, s, da, ha, hrep, hdeg.trans hzw⟩

theorem fractionDegreeAtMost_add
    {z₁ z₂ : ℤ} {q₁ q₂ : C.inverse.localization.Localization}
    (h₁ : C.inverse.fractionDegreeAtMost z₁ q₁)
    (h₂ : C.inverse.fractionDegreeAtMost z₂ q₂) :
    C.inverse.fractionDegreeAtMost (max z₁ z₂) (q₁ + q₂) := by
  by_cases hq₁ : q₁ = 0
  · subst q₁
    simpa [zero_add] using
      (fractionDegreeAtMost_mono C (le_max_right z₁ z₂) h₂)
  by_cases hq₂ : q₂ = 0
  · subst q₂
    simpa [add_zero] using
      (fractionDegreeAtMost_mono C (le_max_left z₁ z₂) h₁)
  rcases fractionDegreeAtMost_nonzero_rep C hq₁ h₁ with
    ⟨a, s₁, da, ha, h₁s, hda⟩
  rcases fractionDegreeAtMost_nonzero_rep C hq₂ h₂ with
    ⟨b, s₂, db, hb, h₂s, hdb⟩
  rcases right_ore_common C (s₁ : R) s₂ with ⟨t, c, hst⟩
  let common : C.inverse.localization.denominators := s₁ * t
  have hcommon_value : (common : R) = (s₂ : R) * c := by
    change (s₁ : R) * (t : R) = (s₂ : R) * c
    exact hst
  have htmem := (C.inverse.denominator_admissible t).choose
  let dt := C.inverse.denominator_degree t
  have hstmem : (s₂ : R) * c ∈
      C.inverse.filtration.carrier
        (C.inverse.denominator_degree s₁ + dt) := by
    rw [← hcommon_value]
    exact C.inverse.filtration.mul_mem
      (C.inverse.denominator_admissible s₁).choose htmem
  have hcontrol := regular_cofactor_control C s₂ hstmem
  have hcindex :
      C.inverse.denominator_degree s₂ ≤
        C.inverse.denominator_degree s₁ + dt := by
    by_contra hnot
    have hc0 := hcontrol.2 (Nat.lt_of_not_ge hnot)
    have hzero : q₂ = 0 := by
      apply cancel_denominator C common
      calc
        q₂ * C.inverse.localization.numerator (common : R) =
            q₂ * C.inverse.localization.numerator ((s₂ : R) * c) := by
              rw [hcommon_value]
        _ = (q₂ * C.inverse.localization.numerator (s₂ : R)) *
            C.inverse.localization.numerator c := by
              rw [map_mul]
              simp only [mul_assoc]
        _ = C.inverse.localization.numerator b *
            C.inverse.localization.numerator c := by rw [h₂s]
        _ = C.inverse.localization.numerator (b * c) := by rw [map_mul]
        _ = 0 := by rw [hc0, mul_zero, map_zero]
      simp
    exact hq₂ hzero
  have hcmem : c ∈ C.inverse.filtration.carrier
      (C.inverse.denominator_degree s₁ + dt -
        C.inverse.denominator_degree s₂) := hcontrol.1 hcindex
  have hamem : a * (t : R) ∈ C.inverse.filtration.carrier
      (da + dt) := C.inverse.filtration.mul_mem ha htmem
  have hbcmem : b * c ∈ C.inverse.filtration.carrier
      (db + (C.inverse.denominator_degree s₁ + dt -
        C.inverse.denominator_degree s₂)) :=
    C.inverse.filtration.mul_mem hb hcmem
  let dsum := max (da + dt)
    (db + (C.inverse.denominator_degree s₁ + dt -
      C.inverse.denominator_degree s₂))
  have haddmem : a * (t : R) + b * c ∈
      C.inverse.filtration.carrier dsum :=
    C.inverse.filtration.add_mem hamem hbcmem
  have hqcommon₁ : q₁ * C.inverse.localization.numerator (common : R) =
      C.inverse.localization.numerator (a * (t : R)) := by
    change q₁ * C.inverse.localization.numerator ((s₁ : R) * (t : R)) = _
    rw [map_mul, ← mul_assoc, h₁s, map_mul]
  have hqcommon₂ : q₂ * C.inverse.localization.numerator (common : R) =
      C.inverse.localization.numerator (b * c) := by
    rw [hcommon_value, map_mul, ← mul_assoc, h₂s, map_mul]
  have hsum : (q₁ + q₂) * C.inverse.localization.numerator (common : R) =
      C.inverse.localization.numerator (a * (t : R) + b * c) := by
    rw [add_mul, hqcommon₁, hqcommon₂, map_add]
  refine Or.inr ⟨a * (t : R) + b * c, common, dsum, haddmem, hsum, ?_⟩
  have hcommon_degree : C.inverse.denominator_degree common =
      C.inverse.denominator_degree s₁ + dt := by
    simpa [common] using denominator_degree_mul C s₁ t
  dsimp [dsum, dt] at *
  rw [hcommon_degree]
  omega

theorem fractionDegreeAtMost_mul
    {z₁ z₂ : ℤ} {q₁ q₂ : C.inverse.localization.Localization}
    (h₁ : C.inverse.fractionDegreeAtMost z₁ q₁)
    (h₂ : C.inverse.fractionDegreeAtMost z₂ q₂) :
    C.inverse.fractionDegreeAtMost (z₁ + z₂) (q₁ * q₂) := by
  by_cases hq₁ : q₁ = 0
  · subst q₁
    exact Or.inl (by simp)
  by_cases hq₂ : q₂ = 0
  · subst q₂
    exact Or.inl (by simp)
  rcases fractionDegreeAtMost_nonzero_rep C hq₁ h₁ with
    ⟨a, s₁, da, ha, h₁s, hda⟩
  rcases fractionDegreeAtMost_nonzero_rep C hq₂ h₂ with
    ⟨b, s₂, db, hb, h₂s, hdb⟩
  rcases right_ore_common C b s₁ with ⟨t, c, hbt⟩
  let common : C.inverse.localization.denominators := s₂ * t
  have htmem := (C.inverse.denominator_admissible t).choose
  let dt := C.inverse.denominator_degree t
  have hbtmem : (s₁ : R) * c ∈
      C.inverse.filtration.carrier (db + dt) := by
    rw [← hbt]
    exact C.inverse.filtration.mul_mem hb htmem
  have hcontrol := regular_cofactor_control C s₁ hbtmem
  have hqcommon : (q₁ * q₂) *
      C.inverse.localization.numerator (common : R) =
      C.inverse.localization.numerator (a * c) := by
    change (q₁ * q₂) * C.inverse.localization.numerator
      ((s₂ : R) * (t : R)) = _
    calc
      (q₁ * q₂) * C.inverse.localization.numerator
          ((s₂ : R) * (t : R)) =
          q₁ * (q₂ * C.inverse.localization.numerator (s₂ : R)) *
            C.inverse.localization.numerator (t : R) := by
              rw [map_mul]
              simp only [mul_assoc]
      _ = q₁ * C.inverse.localization.numerator b *
            C.inverse.localization.numerator (t : R) := by rw [h₂s]
      _ = q₁ * C.inverse.localization.numerator (b * (t : R)) := by
            rw [map_mul]
            simp only [mul_assoc]
      _ = q₁ * C.inverse.localization.numerator ((s₁ : R) * c) := by
            rw [hbt]
      _ = (q₁ * C.inverse.localization.numerator (s₁ : R)) *
            C.inverse.localization.numerator c := by
            rw [map_mul]
            simp only [mul_assoc]
      _ = C.inverse.localization.numerator (a * c) := by
            rw [h₁s, map_mul]
  by_cases hcindex : C.inverse.denominator_degree s₁ ≤ db + dt
  · have hcmem : c ∈ C.inverse.filtration.carrier
        (db + dt - C.inverse.denominator_degree s₁) :=
      hcontrol.1 hcindex
    have hacmem : a * c ∈ C.inverse.filtration.carrier
        (da + (db + dt - C.inverse.denominator_degree s₁)) :=
      C.inverse.filtration.mul_mem ha hcmem
    refine Or.inr ⟨a * c, common,
      da + (db + dt - C.inverse.denominator_degree s₁), hacmem,
      hqcommon, ?_⟩
    dsimp [dt] at *
    have hdenmul := denominator_degree_mul C s₂ t
    have hcast_sub :
        Int.ofNat (db + C.inverse.denominator_degree t -
          C.inverse.denominator_degree s₁) =
          Int.ofNat (db + C.inverse.denominator_degree t) -
            Int.ofNat (C.inverse.denominator_degree s₁) := by
      exact Int.ofNat_sub hcindex
    have hcast_num :
        Int.ofNat (da + (db + C.inverse.denominator_degree t -
          C.inverse.denominator_degree s₁)) =
          Int.ofNat da + Int.ofNat (db + C.inverse.denominator_degree t -
            C.inverse.denominator_degree s₁) :=
      Int.natCast_add da _
    have hcast_den :
        Int.ofNat (C.inverse.denominator_degree s₂ +
          C.inverse.denominator_degree t) =
          Int.ofNat (C.inverse.denominator_degree s₂) +
            Int.ofNat (C.inverse.denominator_degree t) :=
      Int.natCast_add _ _
    have hcast_db :
        Int.ofNat (db + C.inverse.denominator_degree t) =
          Int.ofNat db + Int.ofNat (C.inverse.denominator_degree t) :=
      Int.natCast_add _ _
    calc
      Int.ofNat (da + (db + C.inverse.denominator_degree t -
          C.inverse.denominator_degree s₁)) -
          Int.ofNat (C.inverse.denominator_degree (s₂ * t)) =
        (Int.ofNat da - Int.ofNat (C.inverse.denominator_degree s₁)) +
          (Int.ofNat db - Int.ofNat (C.inverse.denominator_degree s₂)) := by
            rw [hcast_num, hdenmul, hcast_den, hcast_sub, hcast_db]
            ring
      _ ≤ z₁ + z₂ := add_le_add hda hdb
  · have hc0 := hcontrol.2 (Nat.lt_of_not_ge hcindex)
    have hqzero : q₁ * q₂ = 0 := by
      apply cancel_denominator C common
      simpa [hc0] using hqcommon
    exact Or.inl hqzero

def fractionFiltration : ℤ → AddSubgroup
    C.inverse.localization.Localization
  | z =>
    { carrier := {q | C.inverse.fractionDegreeAtMost z q}
      zero_mem' := Or.inl rfl
      add_mem' := by
        intro q r hq hr
        simpa using C.fractionDegreeAtMost_add hq hr
      neg_mem' := by
        intro q hq
        exact C.fractionDegreeAtMost_neg hq }

theorem fractionFiltration_mem
    {z : ℤ} {q : C.inverse.localization.Localization} :
    q ∈ C.fractionFiltration z ↔
      C.inverse.fractionDegreeAtMost z q := Iff.rfl

theorem fractionFiltration_mono {z w : ℤ} (hzw : z ≤ w) :
    C.fractionFiltration z ≤ C.fractionFiltration w := by
  intro q hq
  rcases hq with hq
  rcases hq with hzero | ⟨a, s, da, ha, hrep, hdeg⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨a, s, da, ha, hrep, hdeg.trans hzw⟩

theorem fractionFiltration_mul_mem
    {z w : ℤ} {q r : C.inverse.localization.Localization}
    (hq : q ∈ C.fractionFiltration z) (hr : r ∈ C.fractionFiltration w) :
    q * r ∈ C.fractionFiltration (z + w) := by
  exact C.fractionDegreeAtMost_mul hq hr

theorem fractionFiltration_exhaustive
    (q : C.inverse.localization.Localization) :
    ∃ z : ℤ, q ∈ C.fractionFiltration z := by
  by_cases hq : q = 0
  · exact ⟨0, Or.inl hq⟩
  · rcases C.inverse.localization.right_clear q with
      ⟨a, s, _hs, _hu, hqclear⟩
    rcases C.inverse.filtration.exhaustive a with ⟨da, ha⟩
    refine ⟨Int.ofNat da -
      Int.ofNat (C.inverse.denominator_degree ⟨s, _hs⟩), ?_⟩
    exact Or.inr ⟨a, ⟨s, _hs⟩, da, ha, hqclear, le_rfl⟩

def degreeZeroSubring : Subring C.inverse.localization.Localization where
  carrier := C.fractionFiltration 0
  zero_mem' := (C.fractionFiltration 0).zero_mem
  add_mem' := (C.fractionFiltration 0).add_mem
  neg_mem' := (C.fractionFiltration 0).neg_mem
  one_mem' := by
    refine Or.inr ⟨1, (1 : C.inverse.localization.denominators), 0,
      C.inverse.filtration.one_mem, ?_, ?_⟩
    · simp
    · have hnonneg : (0 : ℤ) ≤
          Int.ofNat (C.inverse.denominator_degree
            (1 : C.inverse.localization.denominators)) :=
        Int.natCast_nonneg _
      exact sub_nonpos.mpr hnonneg
  mul_mem' := by
    intro q r hq hr
    simpa using C.fractionFiltration_mul_mem hq hr

end Data

end SymbolFractionFiltration

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.SymbolFractionFiltration.Data.fractionDegreeAtMost_add
#print axioms
  SymplecticStafford.Filtered.SymbolFractionFiltration.Data.fractionDegreeAtMost_mul
#print axioms
  SymplecticStafford.Filtered.SymbolFractionFiltration.Data.degreeZeroSubring
