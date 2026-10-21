module

public import Mathlib.Tactic
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.RingTheory.OreLocalization.Ring
public import AlgebraicAnalysis.Ore.RightLocalization
public import SymplecticStafford.Filtered.SymbolFractionReesClearance
public import SymplecticStafford.Filtered.SymbolFractionReesMap

@[expose] public section

/-!
# Finite comparison with the selected Laurent Rees ring

The finite right-clearance theorem gives a source coefficient for each
nonzero Laurent coefficient after multiplication by one selected
denominator.  The degree inequality in that theorem is exactly what is
needed to move every such coefficient to a nonnegative source degree.  This
file packages the resulting finite sum as an element of the original Rees
ring and records the resulting factorisation by the homogeneous denominator.

The selected source denominator range is then given an actual opposite Ore
structure.  Its canonical right Ore localization is compared with the
target by Mathlib's universal property.  No Noetherianity claim is made.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

open SymplecticStafford
open SymbolDenominatorSubmonoid
open SymbolFractionInverse
open SymbolFractionFiltration
open SymbolFractionRees
open Multiplicative
open AlgebraicAnalysis.OreRightLocalization

namespace SymbolFractionReesLocalization

variable {R : Type u} [Ring R]

private theorem shift_nonneg
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators)
    (a : ℤ → R) (d : ℤ → ℕ)
    (S : Finset ℤ)
    (hdeg : ∀ z, z ∈ S → Int.ofNat (d z) ≤
      z + Int.ofNat (C.inverse.denominator_degree s))
    {z : ℤ} (hz : z ∈ S) :
    0 ≤ z + Int.ofNat (C.inverse.denominator_degree s) := by
  have hbound := hdeg z hz
  have hnonneg : (0 : ℤ) ≤ Int.ofNat (d z) := Int.natCast_nonneg _
  omega

private theorem shift_mem
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators)
    (a : ℤ → R) (d : ℤ → ℕ)
    (S : Finset ℤ)
    (ha : ∀ z, z ∈ S → a z ∈ C.inverse.filtration.carrier (d z))
    (hdeg : ∀ z, z ∈ S → Int.ofNat (d z) ≤
      z + Int.ofNat (C.inverse.denominator_degree s))
    {z : ℤ} (hz : z ∈ S) :
    a z ∈ (SymbolFractionReesMap.SourceFiltration C).carrier
      (Int.toNat (z + Int.ofNat (C.inverse.denominator_degree s))) := by
  have hnonneg := shift_nonneg C s a d S hdeg hz
  have hnat : d z ≤ Int.toNat (z + Int.ofNat
      (C.inverse.denominator_degree s)) := by
    rw [Int.le_toNat hnonneg]
    exact hdeg z hz
  change a z ∈ C.inverse.filtration.carrier
    (Int.toNat (z + Int.ofNat (C.inverse.denominator_degree s)))
  exact C.inverse.filtration.monotone hnat (ha z hz)

private theorem mul_single_right
    (C : SymbolFractionFiltration.Data R)
    (q : SymbolFractionRees.LaurentPolynomial C) (e : ℤ) (b : T C) :
    q * AddMonoidAlgebra.single e b =
      ∑ z ∈ q.coeff.support,
        AddMonoidAlgebra.single (z + e) (q.coeff z * b) := by
  calc
    q * AddMonoidAlgebra.single e b =
        (∑ z ∈ q.coeff.support, AddMonoidAlgebra.single z (q.coeff z)) *
          AddMonoidAlgebra.single e b := by
            congr 1
            exact (AddMonoidAlgebra.sum_coeff_single q).symm
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [AddMonoidAlgebra.single_mul_single]

/-- Every Laurent Rees element becomes the image of an original nonnegative
Rees element after multiplication by one selected homogeneous denominator. -/
theorem exists_source_multiple
    (C : SymbolFractionFiltration.Data R)
    (p : SymbolFractionRees.ReesRing C) :
    ∃ (r : SymbolFractionReesMap.SourceReesRing C)
      (s : C.inverse.localization.denominators),
      SymbolFractionReesMap.map C r =
        p * SymbolFractionRees.homogeneousDenominator C s := by
  classical
  let S : Finset ℤ :=
    (p : SymbolFractionRees.LaurentPolynomial C).coeff.support
  obtain ⟨s, hs⟩ := SymbolFractionRees.Clearance.support_right_clear C p
  choose a d ha hclear hdeg using hs
  let e : ℕ := C.inverse.denominator_degree s
  let a' : S → R := fun z => a z.1 (by simpa [S] using z.2)
  let d' : S → ℕ := fun z => d z.1 (by simpa [S] using z.2)
  have ha' (z : S) : a' z ∈ C.inverse.filtration.carrier (d' z) :=
    ha z.1 (by simpa [S] using z.2)
  have hdeg' (z : S) : Int.ofNat (d' z) ≤ z.1 + Int.ofNat e := by
    simpa [a', d', S, e] using hdeg z.1 (by simpa [S] using z.2)
  have hshift_nonneg : ∀ (z : ℤ) (hz : z ∈ S), 0 ≤ z + Int.ofNat e := by
    intro z hz
    exact le_trans (Int.ofNat_nonneg (d' ⟨z, hz⟩)) (hdeg' ⟨z, hz⟩)
  have hshift_mem : ∀ (z : ℤ) (hz : z ∈ S),
      a' ⟨z, hz⟩ ∈ (SymbolFractionReesMap.SourceFiltration C).carrier
        (Int.toNat (z + Int.ofNat e)) := by
    intro z hz
    change a' ⟨z, hz⟩ ∈ C.inverse.filtration.carrier _
    apply C.inverse.filtration.monotone _ (ha' ⟨z, hz⟩)
    rw [Int.le_toNat (hshift_nonneg z hz)]
    exact hdeg' ⟨z, hz⟩
  let r : SymbolFractionReesMap.SourceReesRing C :=
    ∑ z ∈ S.attach,
      ReesRing.monomial (SymbolFractionReesMap.SourceFiltration C)
        (Int.toNat (z.1 + Int.ofNat e)) (a' z)
        (hshift_mem z.1 z.2)
  have hmap_shift :
      ((SymbolFractionReesMap.map C r : SymbolFractionRees.ReesRing C) :
          SymbolFractionRees.LaurentPolynomial C) =
        ∑ z ∈ S.attach,
          AddMonoidAlgebra.single (z.1 + Int.ofNat e)
            (C.inverse.localization.numerator (a' z)) := by
    dsimp [r]
    rw [map_sum]
    change (SymbolFractionRees.ReesRing C).subtype
      (∑ z ∈ S.attach,
        SymbolFractionReesMap.map C
          (ReesRing.monomial (SymbolFractionReesMap.SourceFiltration C)
            (Int.toNat (z.1 + Int.ofNat e)) (a' z)
            (hshift_mem z.1 z.2))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [congrArg (SymbolFractionRees.ReesRing C).subtype
      (SymbolFractionReesMap.map_homogeneous C
        (Int.toNat (z.1 + Int.ofNat e)) (a' z)
        (hshift_mem z.1 z.2))]
    change AddMonoidAlgebra.single
      (Int.ofNat (Int.toNat (z.1 + Int.ofNat e)))
      (C.inverse.localization.numerator (a' z)) = _
    congr 1
    exact Int.toNat_of_nonneg (hshift_nonneg z.1 z.2)
  have hproduct :
      ((p : SymbolFractionRees.ReesRing C) :
          SymbolFractionRees.LaurentPolynomial C) *
          (SymbolFractionRees.homogeneousDenominator C s :
            SymbolFractionRees.LaurentPolynomial C) =
        ∑ z ∈ S,
          AddMonoidAlgebra.single (z + Int.ofNat e)
            ((p : SymbolFractionRees.LaurentPolynomial C).coeff z *
              C.inverse.localization.numerator (s : R)) := by
    change (p : SymbolFractionRees.LaurentPolynomial C) *
      AddMonoidAlgebra.single (Int.ofNat e)
        (C.inverse.localization.numerator (s : R)) = _
    simpa [S] using
      (mul_single_right C (p : SymbolFractionRees.LaurentPolynomial C)
        (Int.ofNat e) (C.inverse.localization.numerator (s : R)))
  have hshift :
      SymbolFractionReesMap.map C r =
        p * SymbolFractionRees.homogeneousDenominator C s := by
    apply Subtype.ext
    change ((SymbolFractionReesMap.map C r : SymbolFractionRees.ReesRing C) :
        SymbolFractionRees.LaurentPolynomial C) =
      ((p * SymbolFractionRees.homogeneousDenominator C s :
        SymbolFractionRees.ReesRing C) :
          SymbolFractionRees.LaurentPolynomial C)
    rw [hmap_shift]
    calc
      (∑ z ∈ S.attach,
          AddMonoidAlgebra.single (z.1 + Int.ofNat e)
            (C.inverse.localization.numerator (a' z))) =
          ∑ z ∈ S.attach,
            AddMonoidAlgebra.single (z.1 + Int.ofNat e)
              ((p : SymbolFractionRees.LaurentPolynomial C).coeff z.1 *
                C.inverse.localization.numerator (s : R)) := by
        apply Finset.sum_congr rfl
        intro z hz
        congr 1
        exact (hclear z.1 (by simpa [S] using z.2)).symm
      _ = ∑ z ∈ S,
          AddMonoidAlgebra.single (z + Int.ofNat e)
            ((p : SymbolFractionRees.LaurentPolynomial C).coeff z *
              C.inverse.localization.numerator (s : R)) := by
        exact Finset.sum_attach S (fun z =>
          AddMonoidAlgebra.single (z + Int.ofNat e)
            ((p : SymbolFractionRees.LaurentPolynomial C).coeff z *
              C.inverse.localization.numerator (s : R)))
      _ = ((p : SymbolFractionRees.ReesRing C) :
          SymbolFractionRees.LaurentPolynomial C) *
          (SymbolFractionRees.homogeneousDenominator C s :
            SymbolFractionRees.LaurentPolynomial C) := hproduct.symm
      _ = (((p * SymbolFractionRees.homogeneousDenominator C s) :
          SymbolFractionRees.ReesRing C) :
            SymbolFractionRees.LaurentPolynomial C) := rfl
  exact ⟨r, s, hshift⟩

/-- Multiplying the source multiple by the unit inverse gives a right
fraction representation inside the Laurent Rees subring. -/
theorem exists_source_factorization
    (C : SymbolFractionFiltration.Data R)
    (p : SymbolFractionRees.ReesRing C) :
    ∃ (r : SymbolFractionReesMap.SourceReesRing C)
      (s : C.inverse.localization.denominators),
      p = SymbolFractionReesMap.map C r *
        ((IsUnit.unit
          (SymbolFractionRees.homogeneousDenominator_isUnit C s)).inv :
            SymbolFractionRees.ReesRing C) := by
  obtain ⟨r, s, hshift⟩ := exists_source_multiple C p
  let u : Units (SymbolFractionRees.ReesRing C) :=
    IsUnit.unit (SymbolFractionRees.homogeneousDenominator_isUnit C s)
  have hu : (u : SymbolFractionRees.ReesRing C) =
      SymbolFractionRees.homogeneousDenominator C s := by
    exact IsUnit.unit_spec
      (SymbolFractionRees.homogeneousDenominator_isUnit C s)
  have huinv :
      SymbolFractionRees.homogeneousDenominator C s *
          (u.inv : SymbolFractionRees.ReesRing C) = 1 := by
    rw [← hu]
    exact Units.mul_inv u
  refine ⟨r, s, ?_⟩
  change p = SymbolFractionReesMap.map C r * (u.inv : SymbolFractionRees.ReesRing C)
  calc
    p = p * 1 := (mul_one p).symm
    _ = p * (SymbolFractionRees.homogeneousDenominator C s *
        (u.inv : SymbolFractionRees.ReesRing C)) := by rw [huinv]
    _ = (p * SymbolFractionRees.homogeneousDenominator C s) *
        (u.inv : SymbolFractionRees.ReesRing C) := by rw [mul_assoc]
    _ = SymbolFractionReesMap.map C r *
        (u.inv : SymbolFractionRees.ReesRing C) := by simpa using congrArg (fun x => x * (u.inv : SymbolFractionRees.ReesRing C)) hshift.symm

/- The source denominator submonoid is the range of the selected source
   homogeneous-denominator monoid map.  Its opposite is the denominator set
   used by Mathlib's left Ore localization. -/
noncomputable def sourceDenominators
    (C : SymbolFractionFiltration.Data R) :
    Submonoid (SymbolFractionReesMap.SourceReesRing C) :=
  (⊤ : Submonoid C.inverse.localization.denominators).map
    (SymbolFractionReesMap.sourceHomogeneousDenominatorMonoidHom C)

abbrev sourceOppositeDenominators
    (C : SymbolFractionFiltration.Data R) :=
  oppositeSubmonoid (sourceDenominators C)

private theorem source_opp_unit
    (C : SymbolFractionFiltration.Data R)
    (q : sourceOppositeDenominators C) :
    IsUnit (SymbolFractionReesMap.map C
      ((q : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop)) := by
  have hq : ((q : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) ∈
      sourceDenominators C :=
    q.property
  rcases hq with ⟨s, _hs_top, hs⟩
  have hs' : ((q : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) =
      SymbolFractionReesMap.sourceHomogeneousDenominator C s := hs.symm
  rw [hs', SymbolFractionReesMap.map_sourceHomogeneousDenominator]
  exact SymbolFractionRees.homogeneousDenominator_isUnit C s

private theorem source_right_ore
    (C : SymbolFractionFiltration.Data R)
    (a : SymbolFractionReesMap.SourceReesRing C)
    (s : sourceDenominators C) :
    ∃ t : sourceDenominators C, ∃ c :
      SymbolFractionReesMap.SourceReesRing C,
      a * (t : SymbolFractionReesMap.SourceReesRing C) =
        (s : SymbolFractionReesMap.SourceReesRing C) * c := by
  have hs : (s : SymbolFractionReesMap.SourceReesRing C) ∈
      sourceDenominators C :=
    s.property
  rcases hs with ⟨s0, _hs0_top, hs0⟩
  have hmaps : SymbolFractionReesMap.map C (s :
      SymbolFractionReesMap.SourceReesRing C) =
      SymbolFractionRees.homogeneousDenominator C s0 := by
    calc
      SymbolFractionReesMap.map C (s :
          SymbolFractionReesMap.SourceReesRing C) =
          SymbolFractionReesMap.map C
            (SymbolFractionReesMap.sourceHomogeneousDenominator C s0) :=
        congrArg (SymbolFractionReesMap.map C) hs0.symm
      _ = SymbolFractionRees.homogeneousDenominator C s0 :=
        SymbolFractionReesMap.map_sourceHomogeneousDenominator C s0
  let us : Units (SymbolFractionRees.ReesRing C) :=
    IsUnit.unit (SymbolFractionRees.homogeneousDenominator_isUnit C s0)
  have hus : (us : SymbolFractionRees.ReesRing C) =
      SymbolFractionRees.homogeneousDenominator C s0 := by
    exact IsUnit.unit_spec
      (SymbolFractionRees.homogeneousDenominator_isUnit C s0)
  let q : SymbolFractionRees.ReesRing C :=
    (us.inv : SymbolFractionRees.ReesRing C) *
      SymbolFractionReesMap.map C a
  obtain ⟨c, t, hfac⟩ := exists_source_factorization C q
  let ut : Units (SymbolFractionRees.ReesRing C) :=
    IsUnit.unit (SymbolFractionRees.homogeneousDenominator_isUnit C t)
  have hut : (ut : SymbolFractionRees.ReesRing C) =
      SymbolFractionRees.homogeneousDenominator C t := by
    exact IsUnit.unit_spec
      (SymbolFractionRees.homogeneousDenominator_isUnit C t)
  have hutinv : (ut.inv : SymbolFractionRees.ReesRing C) *
      SymbolFractionRees.homogeneousDenominator C t = 1 := by
    rw [← hut]
    exact Units.inv_mul ut
  have hclear : q * SymbolFractionRees.homogeneousDenominator C t =
      SymbolFractionReesMap.map C c := by
    calc
      q * SymbolFractionRees.homogeneousDenominator C t =
          (SymbolFractionReesMap.map C c *
            (ut.inv : SymbolFractionRees.ReesRing C)) *
            SymbolFractionRees.homogeneousDenominator C t := by
              rw [hfac]
      _ = SymbolFractionReesMap.map C c *
          ((ut.inv : SymbolFractionRees.ReesRing C) *
            SymbolFractionRees.homogeneousDenominator C t) := by
              rw [mul_assoc]
      _ = SymbolFractionReesMap.map C c * 1 :=
        congrArg (fun x => SymbolFractionReesMap.map C c * x) hutinv
      _ = SymbolFractionReesMap.map C c :=
        mul_one (SymbolFractionReesMap.map C c :
          SymbolFractionRees.ReesRing C)
  have hleft : SymbolFractionReesMap.map C (s :
      SymbolFractionReesMap.SourceReesRing C) * q =
      SymbolFractionReesMap.map C a := by
    change SymbolFractionReesMap.map C (s : SymbolFractionReesMap.SourceReesRing C) *
      ((us.inv : SymbolFractionRees.ReesRing C) * SymbolFractionReesMap.map C a) = _
    have husinv : (us : SymbolFractionRees.ReesRing C) *
        (us.inv : SymbolFractionRees.ReesRing C) = 1 := Units.mul_inv us
    calc
      SymbolFractionReesMap.map C (s :
          SymbolFractionReesMap.SourceReesRing C) *
          ((us.inv : SymbolFractionRees.ReesRing C) *
            SymbolFractionReesMap.map C a) =
          ((us : SymbolFractionRees.ReesRing C) * us.inv) *
            SymbolFractionReesMap.map C a := by rw [hmaps, ← hus, mul_assoc]
      _ = SymbolFractionReesMap.map C a := by
        rw [husinv]
        exact one_mul (SymbolFractionReesMap.map C a :
          SymbolFractionRees.ReesRing C)
  have htarget : SymbolFractionReesMap.map C a *
      SymbolFractionReesMap.map C
        (SymbolFractionReesMap.sourceHomogeneousDenominator C t) =
      SymbolFractionReesMap.map C (s :
        SymbolFractionReesMap.SourceReesRing C) *
        SymbolFractionReesMap.map C c := by
    calc
      SymbolFractionReesMap.map C a *
          SymbolFractionReesMap.map C
            (SymbolFractionReesMap.sourceHomogeneousDenominator C t) =
          (SymbolFractionReesMap.map C (s :
            SymbolFractionReesMap.SourceReesRing C) * q) *
            SymbolFractionReesMap.map C
              (SymbolFractionReesMap.sourceHomogeneousDenominator C t) := by
                rw [hleft]
      _ = SymbolFractionReesMap.map C (s :
          SymbolFractionReesMap.SourceReesRing C) *
          (q * SymbolFractionReesMap.map C
            (SymbolFractionReesMap.sourceHomogeneousDenominator C t)) := by
              rw [mul_assoc]
      _ = SymbolFractionReesMap.map C (s :
          SymbolFractionReesMap.SourceReesRing C) *
          (q * SymbolFractionRees.homogeneousDenominator C t) := by
              rw [SymbolFractionReesMap.map_sourceHomogeneousDenominator]
      _ = SymbolFractionReesMap.map C (s :
          SymbolFractionReesMap.SourceReesRing C) *
          SymbolFractionReesMap.map C c := by rw [hclear]
  have hsource : a *
      SymbolFractionReesMap.sourceHomogeneousDenominator C t =
      (s : SymbolFractionReesMap.SourceReesRing C) * c := by
    apply SymbolFractionReesMap.map_injective C
    simpa only [map_mul] using htarget
  refine ⟨⟨SymbolFractionReesMap.sourceHomogeneousDenominator C t,
      ⟨t, trivial, rfl⟩⟩, c, hsource⟩

/- The actual Ore witness is obtained by applying the preceding right Ore
   equation and reversing products in the opposite ring. -/
noncomputable def sourceOreSet
    (C : SymbolFractionFiltration.Data R) :
    OreLocalization.OreSet (sourceOppositeDenominators C) := by
  classical
  let hright : ∀ (r : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ)
      (q : sourceOppositeDenominators C),
      ∃ (n : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ)
        (d : sourceOppositeDenominators C),
        d * r = n * q := by
    intro r q
    let s : sourceDenominators C :=
      ⟨((q : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop), q.property⟩
    rcases source_right_ore C ((r :
      (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) s with
      ⟨t, c, h⟩
    refine ⟨MulOpposite.op c,
      ⟨MulOpposite.op (t : SymbolFractionReesMap.SourceReesRing C),
        t.property⟩, ?_⟩
    have hq : (⟨MulOpposite.op (s : SymbolFractionReesMap.SourceReesRing C),
        s.property⟩ : sourceOppositeDenominators C) = q := by
      apply Subtype.ext
      rfl
    rw [← hq]
    simpa only [MulOpposite.op_mul, MulOpposite.op_unop] using
      congrArg MulOpposite.op h
  choose n d hnd using hright
  refine
    { ore_right_cancel := ?_
      oreNum := n
      oreDenom := d
      ore_eq := hnd }
  intro r₁ r₂ q h
  let hu := source_opp_unit C q
  have hunop :
      ((q : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) *
          ((r₁ : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) =
        ((q : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) *
          ((r₂ : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) := by
    simpa only [MulOpposite.unop_mul] using
      congrArg MulOpposite.unop h
  have hmap := congrArg (SymbolFractionReesMap.map C) hunop
  have hmap' : SymbolFractionReesMap.map C
      ((r₁ : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) =
      SymbolFractionReesMap.map C
        ((r₂ : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) := by
    apply hu.mul_left_cancel
    simpa only [map_mul] using hmap
  have hr_unop :
      ((r₁ : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) =
        ((r₂ : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) :=
    SymbolFractionReesMap.map_injective C hmap'
  have hr : r₁ = r₂ := congrArg MulOpposite.op hr_unop
  exact ⟨1, by simp [hr]⟩

abbrev sourceLocalization
    (C : SymbolFractionFiltration.Data R) :=
  @RightOreLocalization (SymbolFractionReesMap.SourceReesRing C)
    (inferInstance : Ring (SymbolFractionReesMap.SourceReesRing C))
    (sourceDenominators C) (sourceOreSet C)

noncomputable def sourceNumerator
    (C : SymbolFractionFiltration.Data R) :
    SymbolFractionReesMap.SourceReesRing C →+*
      sourceLocalization C :=
  @rightNumeratorRingHom (SymbolFractionReesMap.SourceReesRing C)
    (inferInstance : Ring (SymbolFractionReesMap.SourceReesRing C))
    (sourceDenominators C) (sourceOreSet C)

private theorem source_opp_regular
    (C : SymbolFractionFiltration.Data R) :
    sourceOppositeDenominators C ≤ nonZeroDivisorsLeft
      (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ := by
  intro q hq y hy
  let q' : sourceOppositeDenominators C := ⟨q, hq⟩
  have hu := source_opp_unit C q'
  have hunop :
      ((y : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) *
          ((q : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) = 0 := by
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_zero] using
      congrArg MulOpposite.unop hy
  have hmap := congrArg (SymbolFractionReesMap.map C) hunop
  have hmap' : SymbolFractionReesMap.map C
      ((y : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop) = 0 := by
    apply hu.mul_right_cancel
    simpa only [map_mul, map_zero, zero_mul] using hmap
  exact MulOpposite.unop_injective
    (SymbolFractionReesMap.map_injective C (by simpa using hmap'))

theorem sourceNumerator_injective (C : SymbolFractionFiltration.Data R) :
    Function.Injective (sourceNumerator C) := by
  intro a b hab
  apply MulOpposite.op_injective
  apply @OreLocalization.numeratorHom_inj
    ((SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ) _
    (sourceOppositeDenominators C) (sourceOreSet C)
    (source_opp_regular C)
  exact congrArg MulOpposite.unop hab

theorem sourceNumerator_isUnit
    (C : SymbolFractionFiltration.Data R)
    (s : sourceDenominators C) :
    IsUnit (sourceNumerator C s) := by
  letI : OreLocalization.OreSet (sourceOppositeDenominators C) :=
    sourceOreSet C
  exact isUnit_op.mpr (OreLocalization.numerator_isUnit
    (R := (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ)
    (S := sourceOppositeDenominators C)
    (⟨MulOpposite.op (s : SymbolFractionReesMap.SourceReesRing C),
      s.property⟩ : sourceOppositeDenominators C))

/- The canonical source fraction is the opposite of Mathlib's Ore quotient.
   It is useful below because its denominator is visibly the same selected
   source denominator as the one occurring in the right-clearance API. -/
noncomputable def sourceFraction
    (C : SymbolFractionFiltration.Data R)
    (a : SymbolFractionReesMap.SourceReesRing C)
    (s : sourceDenominators C) : sourceLocalization C := by
  letI : OreLocalization.OreSet (sourceOppositeDenominators C) :=
    sourceOreSet C
  exact MulOpposite.op
    (OreLocalization.oreDiv (MulOpposite.op a)
      (⟨MulOpposite.op (s : SymbolFractionReesMap.SourceReesRing C),
        s.property⟩ : sourceOppositeDenominators C))

private theorem sourceFraction_mul_numerator
    (C : SymbolFractionFiltration.Data R)
    (a : SymbolFractionReesMap.SourceReesRing C)
    (s : sourceDenominators C) :
    sourceFraction C a s * sourceNumerator C s =
      sourceNumerator C a := by
  letI : OreLocalization.OreSet (sourceOppositeDenominators C) :=
    sourceOreSet C
  apply MulOpposite.unop_injective
  rw [show sourceFraction C a s = MulOpposite.op
      (OreLocalization.oreDiv (MulOpposite.op a)
        (⟨MulOpposite.op (s : SymbolFractionReesMap.SourceReesRing C),
          s.property⟩ : sourceOppositeDenominators C)) by
        rfl]
  exact OreLocalization.mul_cancel
    (R := (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ)
    (S := sourceOppositeDenominators C)
    (r := MulOpposite.op a)
    (s := (⟨MulOpposite.op (s : SymbolFractionReesMap.SourceReesRing C),
      s.property⟩ : sourceOppositeDenominators C))
    (t := (1 : sourceOppositeDenominators C))

/- The quotient itself has the usual fraction normal form.  This induction
   is over the actual Ore localization, so no representation callback is
   hidden in the comparison. -/
theorem sourceFraction_normal_form
    (C : SymbolFractionFiltration.Data R)
    (x : sourceLocalization C) :
    ∃ (a : SymbolFractionReesMap.SourceReesRing C)
      (s : sourceDenominators C),
      x = sourceFraction C a s := by
  letI : OreLocalization.OreSet (sourceOppositeDenominators C) :=
    sourceOreSet C
  generalize hx : (x : sourceLocalization C).unop = y
  induction y using @OreLocalization.ind
      ((SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ) _
      (sourceOppositeDenominators C) (sourceOreSet C)
      ((SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ) _ with
  | _ a s =>
      refine ⟨a.unop,
        ⟨s.val.unop, s.property⟩, ?_⟩
      apply MulOpposite.unop_injective
      simpa [sourceFraction] using hx

abbrev sourceOppositeMap
    (C : SymbolFractionFiltration.Data R) :
    (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ →+*
      (SymbolFractionRees.ReesRing C)ᵐᵒᵖ :=
  (SymbolFractionReesMap.map C).op

private theorem source_opp_unit_op
    (C : SymbolFractionFiltration.Data R)
    (q : sourceOppositeDenominators C) :
    IsUnit (sourceOppositeMap C q) := by
  change IsUnit (MulOpposite.op
    (SymbolFractionReesMap.map C
      ((q : (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ).unop)))
  exact (source_opp_unit C q).op

/- A choice of target unit for each source denominator is made coherent by
   the fact that `IsUnit.unit_spec` identifies its value with the mapped
   denominator. -/
noncomputable def sourceOppositeUnits
  (C : SymbolFractionFiltration.Data R) :
    sourceOppositeDenominators C →*
      Units ((SymbolFractionRees.ReesRing C)ᵐᵒᵖ) where
  toFun q := IsUnit.unit (source_opp_unit_op C q)
  map_one' := by
    apply Units.ext
    change (IsUnit.unit (source_opp_unit_op C (1 :
      sourceOppositeDenominators C)) :
        (SymbolFractionRees.ReesRing C)ᵐᵒᵖ) = 1
    rw [IsUnit.unit_spec]
    exact (sourceOppositeMap C).map_one
  map_mul' q₁ q₂ := by
    apply Units.ext
    change (IsUnit.unit (source_opp_unit_op C (q₁ * q₂)) :
        (SymbolFractionRees.ReesRing C)ᵐᵒᵖ) =
      (IsUnit.unit (source_opp_unit_op C q₁) :
        (SymbolFractionRees.ReesRing C)ᵐᵒᵖ) *
        (IsUnit.unit (source_opp_unit_op C q₂) :
          (SymbolFractionRees.ReesRing C)ᵐᵒᵖ)
    rw [IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec]
    exact (sourceOppositeMap C).map_mul _ _

private theorem sourceOppositeUnits_spec
    (C : SymbolFractionFiltration.Data R)
    (q : sourceOppositeDenominators C) :
    sourceOppositeMap C q = (sourceOppositeUnits C q :
      (SymbolFractionRees.ReesRing C)ᵐᵒᵖ) := by
  change _ = (IsUnit.unit (source_opp_unit_op C q) :
    (SymbolFractionRees.ReesRing C)ᵐᵒᵖ)
  rw [IsUnit.unit_spec]

/- The universal property now gives the canonical map from the source
   right localization to the target Laurent Rees subring. -/
noncomputable def sourceLocalizationMap
    (C : SymbolFractionFiltration.Data R) :
    sourceLocalization C →+* SymbolFractionRees.ReesRing C := by
  letI : OreLocalization.OreSet (sourceOppositeDenominators C) :=
    sourceOreSet C
  let f : (sourceLocalization C)ᵐᵒᵖ →+*
      (SymbolFractionRees.ReesRing C)ᵐᵒᵖ :=
    (OreLocalization.universalHom
        (R := (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ)
        (S := sourceOppositeDenominators C)
        (T := (SymbolFractionRees.ReesRing C)ᵐᵒᵖ)
        (sourceOppositeMap C)
        (sourceOppositeUnits C) (sourceOppositeUnits_spec C)).comp
      (RingEquiv.opOp (OreLocalization (sourceOppositeDenominators C)
        (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ)).symm.toRingHom
  exact RingHom.unop f

theorem sourceLocalizationMap_commutes
    (C : SymbolFractionFiltration.Data R)
    (a : SymbolFractionReesMap.SourceReesRing C) :
    sourceLocalizationMap C (sourceNumerator C a) =
      SymbolFractionReesMap.map C a := by
  letI : OreLocalization.OreSet (sourceOppositeDenominators C) :=
    sourceOreSet C
  rw [sourceLocalizationMap, sourceNumerator]
  change MulOpposite.unop
      (OreLocalization.universalHom (sourceOppositeMap C)
      (sourceOppositeUnits C) (sourceOppositeUnits_spec C)
        (OreLocalization.numeratorRingHom (MulOpposite.op a))) =
    SymbolFractionReesMap.map C a
  have h := OreLocalization.universalHom_commutes
    (R := (SymbolFractionReesMap.SourceReesRing C)ᵐᵒᵖ)
    (S := sourceOppositeDenominators C)
    (T := (SymbolFractionRees.ReesRing C)ᵐᵒᵖ)
    (r := MulOpposite.op a)
    (sourceOppositeMap C) (sourceOppositeUnits C)
      (sourceOppositeUnits_spec C)
  exact congrArg MulOpposite.unop h

theorem sourceLocalizationMap_fraction_clear
    (C : SymbolFractionFiltration.Data R)
    (a : SymbolFractionReesMap.SourceReesRing C)
    (s : sourceDenominators C) :
    sourceLocalizationMap C (sourceFraction C a s) *
        SymbolFractionReesMap.map C (s :
          SymbolFractionReesMap.SourceReesRing C) =
      SymbolFractionReesMap.map C a := by
  have h := congrArg (sourceLocalizationMap C)
    (sourceFraction_mul_numerator C a s)
  rw [map_mul, sourceLocalizationMap_commutes,
    sourceLocalizationMap_commutes] at h
  exact h

private theorem source_right_clear
    (C : SymbolFractionFiltration.Data R)
    (x : sourceLocalization C) :
    ∃ (a : SymbolFractionReesMap.SourceReesRing C)
      (s : sourceDenominators C),
      IsUnit (sourceNumerator C s) ∧
        x * sourceNumerator C s = sourceNumerator C a := by
  rcases sourceFraction_normal_form C x with ⟨a, s, rfl⟩
  exact ⟨a, s, sourceNumerator_isUnit C s,
    sourceFraction_mul_numerator C a s⟩

theorem sourceLocalizationMap_injective
    (C : SymbolFractionFiltration.Data R) :
    Function.Injective (sourceLocalizationMap C) := by
  intro x y hxy
  have hz : sourceLocalizationMap C (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨a, s, hus, hclear⟩ := source_right_clear C (x - y)
  have hmapclear := congrArg (sourceLocalizationMap C) hclear
  have hmapa : SymbolFractionReesMap.map C a = 0 := by
    rw [map_mul, hz, zero_mul,
      sourceLocalizationMap_commutes] at hmapclear
    exact hmapclear.symm
  have ha : a = 0 := SymbolFractionReesMap.map_injective C hmapa
  have hzero : x - y = 0 := by
    apply hus.mul_right_cancel
    simpa [ha] using hclear
  exact sub_eq_zero.mp hzero

theorem sourceLocalizationMap_surjective
    (C : SymbolFractionFiltration.Data R) :
    Function.Surjective (sourceLocalizationMap C) := by
  intro p
  obtain ⟨r, s, hfac⟩ := exists_source_factorization C p
  let sd : sourceDenominators C :=
    ⟨SymbolFractionReesMap.sourceHomogeneousDenominator C s,
      ⟨s, trivial, rfl⟩⟩
  have hmapsd : SymbolFractionReesMap.map C (sd :
      SymbolFractionReesMap.SourceReesRing C) =
      SymbolFractionRees.homogeneousDenominator C s := by
    change SymbolFractionReesMap.map C
      (SymbolFractionReesMap.sourceHomogeneousDenominator C s) = _
    exact SymbolFractionReesMap.map_sourceHomogeneousDenominator C s
  let u : Units (SymbolFractionRees.ReesRing C) :=
    IsUnit.unit (SymbolFractionRees.homogeneousDenominator_isUnit C s)
  have hu : (u : SymbolFractionRees.ReesRing C) =
      SymbolFractionRees.homogeneousDenominator C s :=
    IsUnit.unit_spec
      (SymbolFractionRees.homogeneousDenominator_isUnit C s)
  have huinv : (u.inv : SymbolFractionRees.ReesRing C) *
      SymbolFractionRees.homogeneousDenominator C s = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  have hfac_clear : p * SymbolFractionRees.homogeneousDenominator C s =
      SymbolFractionReesMap.map C r := by
    calc
      p * SymbolFractionRees.homogeneousDenominator C s =
          (SymbolFractionReesMap.map C r *
            (u.inv : SymbolFractionRees.ReesRing C)) *
            SymbolFractionRees.homogeneousDenominator C s := by
              rw [hfac]
      _ = SymbolFractionReesMap.map C r *
          ((u.inv : SymbolFractionRees.ReesRing C) *
            SymbolFractionRees.homogeneousDenominator C s) := by
              rw [mul_assoc]
      _ = SymbolFractionReesMap.map C r * 1 :=
        congrArg (fun x => SymbolFractionReesMap.map C r * x) huinv
      _ = SymbolFractionReesMap.map C r :=
        mul_one (SymbolFractionReesMap.map C r :
          SymbolFractionRees.ReesRing C)
  refine ⟨sourceFraction C r sd, ?_⟩
  apply (SymbolFractionRees.homogeneousDenominator_isUnit C s).mul_right_cancel
  calc
    sourceLocalizationMap C (sourceFraction C r sd) *
          SymbolFractionRees.homogeneousDenominator C s =
        sourceLocalizationMap C (sourceFraction C r sd) *
          SymbolFractionReesMap.map C (sd :
            SymbolFractionReesMap.SourceReesRing C) := by rw [hmapsd]
    _ = SymbolFractionReesMap.map C r :=
      sourceLocalizationMap_fraction_clear C r sd
    _ = p * SymbolFractionRees.homogeneousDenominator C s :=
      hfac_clear.symm

theorem sourceLocalizationMap_bijective
    (C : SymbolFractionFiltration.Data R) :
    Function.Bijective (sourceLocalizationMap C) :=
  ⟨sourceLocalizationMap_injective C,
    sourceLocalizationMap_surjective C⟩

end SymbolFractionReesLocalization

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.SymbolFractionReesLocalization.exists_source_multiple
#print axioms
  SymplecticStafford.Filtered.SymbolFractionReesLocalization.exists_source_factorization
