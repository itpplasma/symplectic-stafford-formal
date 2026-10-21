module

public import Mathlib.Tactic
public import SymplecticStafford.Filtered.ReesRing
public import SymplecticStafford.Filtered.SymbolFractionRees

@[expose] public section

/-!
# The original Rees ring maps into the Laurent fraction Rees ring

For an actual symbol-fraction datum, the original nonnegative Rees ring maps
to the integer-indexed Laurent Rees ring by applying the localization
numerator to each coefficient and sending degree `n` to degree `n`.  The
ambient map is built from Mathlib's noncommutative monoid-algebra lift; its
coefficient and degree factors commute because the latter has coefficient
`1`, so no commutativity of the localization is used.

The restriction is proved from the actual fraction predicate.  This file does
not assume a universal property for either Rees object and makes no
Noetherianity or localization-comparison claim.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

set_option maxRecDepth 2000

open SymplecticStafford
open SymbolDenominatorSubmonoid
open SymbolFractionInverse
open SymbolFractionFiltration
open SymbolFractionRees
open Multiplicative

namespace SymbolFractionReesMap

variable {R : Type u} [Ring R]

abbrev SourceFiltration (C : SymbolFractionFiltration.Data R) :
    NegFiltrationData R := C.inverse.filtration.toNegFiltrationData

abbrev SourceReesRing (C : SymbolFractionFiltration.Data R) :=
  ReesRing (SourceFiltration C)

/- The degree of a product of selected denominators is obtained from the
   actual selected-symbol degree theorem.  This is kept local because the
   corresponding helper in the filtration implementation is private. -/
private theorem denominator_degree_mul
    (C : SymbolFractionFiltration.Data R)
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

private theorem denominator_degree_one
    (C : SymbolFractionFiltration.Data R) :
    C.inverse.denominator_degree
      (1 : C.inverse.localization.denominators) = 0 := by
  let hmem : (1 : R) ∈
      SymbolDenominatorSubmonoid.submonoid C.inverse.filtration
        C.inverse.symbols :=
    (SymbolDenominatorSubmonoid.submonoid C.inverse.filtration
      C.inverse.symbols).one_mem
  have hzero : SymbolDenominatorSubmonoid.Admissible
      C.inverse.filtration C.inverse.symbols (1 : R) 0 :=
    ⟨C.inverse.filtration.one_mem, C.inverse.symbols.one_mem⟩
  have hdeg : SymbolDenominatorSubmonoid.degree
      C.inverse.filtration C.inverse.symbols hmem = 0 := by
    apply SymbolDenominatorSubmonoid.degree_eq_of_minimal
      C.inverse.filtration C.inverse.symbols hzero
    intro n hn
    omega
  dsimp [SymbolFractionInverse.Data.denominator_degree]
  simpa [hmem, C.inverse.denominators_eq_submonoid] using hdeg

private def coefficientMap (C : SymbolFractionFiltration.Data R) :
    R →+* SymbolFractionRees.LaurentPolynomial C where
  toFun a := AddMonoidAlgebra.single (0 : ℤ)
    (C.inverse.localization.numerator a)
  map_one' := by simp
  map_mul' := by
    intro a b
    simp [AddMonoidAlgebra.single_mul_single]
  map_zero' := by simp
  map_add' := by
    intro a b
    simp

private def degreeMap (C : SymbolFractionFiltration.Data R) :
    Multiplicative ℕ →* SymbolFractionRees.LaurentPolynomial C where
  toFun n := AddMonoidAlgebra.single
    (Int.ofNat (Multiplicative.toAdd n)) 1
  map_one' := by simp
  map_mul' := by
    intro m n
    rw [AddMonoidAlgebra.single_mul_single]
    congr 1
    simp [Int.natCast_add]

/-- The ambient coefficient-and-degree map before restricting to bounded
    elements.  The `hcomm` proof uses only multiplication by coefficient `1`
    and commutativity of the integer degree index. -/
def ambientMap (C : SymbolFractionFiltration.Data R) :
    ReesPolynomial R →+* SymbolFractionRees.LaurentPolynomial C :=
  SkewMonoidAlgebra.liftNCRingHom (coefficientMap C) (degreeMap C) (by
    intro a n
    change AddMonoidAlgebra.single (0 : ℤ)
        (C.inverse.localization.numerator a) *
        AddMonoidAlgebra.single
          (Int.ofNat (Multiplicative.toAdd n)) 1 =
      AddMonoidAlgebra.single
          (Int.ofNat (Multiplicative.toAdd n)) 1 *
        AddMonoidAlgebra.single (0 : ℤ)
          (C.inverse.localization.numerator a)
    rw [AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.single_mul_single]
    simp [add_comm])

private theorem numerator_mem_nat_degree
    (C : SymbolFractionFiltration.Data R)
    {n : ℕ} {a : R} (ha : a ∈ C.inverse.filtration.carrier n) :
    C.inverse.localization.numerator a ∈
      C.fractionFiltration (Int.ofNat n) := by
  change C.inverse.fractionDegreeAtMost (Int.ofNat n)
    (C.inverse.localization.numerator a)
  refine Or.inr ⟨a, (1 : C.inverse.localization.denominators), n, ha,
    ?_, ?_⟩
  · simp
  · have hdeg : (0 : ℤ) ≤ Int.ofNat
        (C.inverse.denominator_degree
          (1 : C.inverse.localization.denominators)) :=
      Int.natCast_nonneg _
    omega

private theorem single_bounded_nat
    (C : SymbolFractionFiltration.Data R)
    {n : ℕ} {a : R} (ha : a ∈ C.inverse.filtration.carrier n) :
    SymbolFractionRees.Bounded C
      (AddMonoidAlgebra.single (Int.ofNat n)
        (C.inverse.localization.numerator a)) := by
  intro z
  rw [AddMonoidAlgebra.coeff_single_apply]
  by_cases h : Int.ofNat n = z
  · subst z
    simpa using numerator_mem_nat_degree C ha
  · rw [if_neg h]
    exact (C.fractionFiltration z).zero_mem

private theorem ambientMap_monomial
    (C : SymbolFractionFiltration.Data R) (n : ℕ) (a : R) :
    ambientMap C (SkewPolynomial.monomial n a) =
      AddMonoidAlgebra.single (Int.ofNat n)
        (C.inverse.localization.numerator a) := by
  simp [ambientMap, SkewMonoidAlgebra.liftNCRingHom,
    SkewMonoidAlgebra.liftNC, coefficientMap, degreeMap,
    SkewPolynomial.monomial_def]

private theorem ambientMap_bounded
    (C : SymbolFractionFiltration.Data R)
    (p : ReesPolynomial R)
    (hp : ReesBounded (SourceFiltration C).toFiltrationData p) :
    SymbolFractionRees.Bounded C (ambientMap C p) := by
  revert hp
  induction p using SkewPolynomial.induction with
  | h0 =>
      intro _hq
      simpa [ambientMap] using SymbolFractionRees.bounded_zero C
  | ha n a q _hns _ha0 ih =>
      intro hsum
      have ha_mem : a ∈ C.inverse.filtration.carrier n := by
        have hcoeff := hsum n
        rw [SkewPolynomial.coeff_add, SkewPolynomial.coeff_monomial,
          if_pos rfl, SkewPolynomial.notMem_support_iff.mp _hns,
          add_zero] at hcoeff
        exact hcoeff
      have hq_mem :
          ReesBounded (SourceFiltration C).toFiltrationData q := by
        intro m
        by_cases hnm : n = m
        · subst m
          simpa [SkewPolynomial.notMem_support_iff.mp _hns] using
            (SourceFiltration C).toFiltrationData.monotone
              (Nat.zero_le n) (SourceFiltration C).toFiltrationData.zero_mem
        · have hcoeff := hsum m
          rw [SkewPolynomial.coeff_add, SkewPolynomial.coeff_monomial,
            if_neg hnm, zero_add] at hcoeff
          exact hcoeff
      rw [(ambientMap C).map_add, ambientMap_monomial]
      have hq_bounded : SymbolFractionRees.Bounded C
          (ambientMap C q) := ih hq_mem
      exact SymbolFractionRees.bounded_add C
        (single_bounded_nat C ha_mem) hq_bounded

/- The ambient map remembers every source coefficient at its corresponding
   nonnegative integer degree.  This is the coefficient-level injectivity
   bridge; no localization universal property is used. -/
private theorem ambientMap_coeff_nat
    (C : SymbolFractionFiltration.Data R)
    (p : ReesPolynomial R) (n : ℕ) :
    (ambientMap C p).coeff (Int.ofNat n) =
      C.inverse.localization.numerator (p.coeff n) := by
  induction p using SkewPolynomial.induction with
  | h0 =>
      simp [ambientMap]
  | ha k a q _hns _ha0 ih =>
      rw [(ambientMap C).map_add, ambientMap_monomial,
        AddMonoidAlgebra.coeff_add, SkewPolynomial.coeff_add,
        SkewPolynomial.coeff_monomial]
      rw [show
        ((AddMonoidAlgebra.single (Int.ofNat k)
              (C.inverse.localization.numerator a)).coeff +
            (ambientMap C q).coeff) (Int.ofNat n) =
          (AddMonoidAlgebra.single (Int.ofNat k)
              (C.inverse.localization.numerator a)).coeff (Int.ofNat n) +
            (ambientMap C q).coeff (Int.ofNat n) from rfl,
        AddMonoidAlgebra.coeff_single_apply]
      by_cases hkn : k = n
      · subst n
        simp [map_add]
        exact ih
      · simp [hkn, map_add]
        exact ih

theorem ambientMap_injective
    (C : SymbolFractionFiltration.Data R) :
    Function.Injective (ambientMap C) := by
  intro p q hpq
  apply SkewPolynomial.ext
  intro n
  apply C.inverse.localization.numerator_injective
  rw [← ambientMap_coeff_nat C p n, ← ambientMap_coeff_nat C q n]
  exact congrArg (fun x : SymbolFractionRees.LaurentPolynomial C =>
    x.coeff (Int.ofNat n)) hpq

/-- The actual ring homomorphism from the original bounded Rees ring to the
    integer-indexed Laurent Rees ring. -/
def map (C : SymbolFractionFiltration.Data R) :
    SourceReesRing C →+* SymbolFractionRees.ReesRing C where
  toFun p :=
    ⟨ambientMap C (p : ReesPolynomial R),
      ambientMap_bounded C (p : ReesPolynomial R) p.property⟩
  map_zero' := by
    apply Subtype.ext
    exact (ambientMap C).map_zero
  map_one' := by
    apply Subtype.ext
    exact (ambientMap C).map_one
  map_add' p q := by
    apply Subtype.ext
    exact (ambientMap C).map_add (p : ReesPolynomial R) (q : ReesPolynomial R)
  map_mul' p q := by
    apply Subtype.ext
    exact (ambientMap C).map_mul (p : ReesPolynomial R) (q : ReesPolynomial R)

theorem map_injective
    (C : SymbolFractionFiltration.Data R) :
    Function.Injective (map C) := by
  intro p q hpq
  apply Subtype.ext
  apply ambientMap_injective C
  exact congrArg (fun x : SymbolFractionRees.ReesRing C =>
    (x : SymbolFractionRees.LaurentPolynomial C)) hpq

theorem map_homogeneous
    (C : SymbolFractionFiltration.Data R) (n : ℕ) (a : R)
    (ha : a ∈ C.inverse.filtration.carrier n) :
    map C (ReesRing.monomial (SourceFiltration C) n a ha) =
      SymbolFractionRees.homogeneous C (Int.ofNat n)
        (C.inverse.localization.numerator a)
        (numerator_mem_nat_degree C ha) := by
  apply Subtype.ext
  exact ambientMap_monomial C n a

/- The selected denominator itself is placed in the source Rees ring at the
   exact degree supplied by its selected associated class. -/
noncomputable def sourceHomogeneousDenominator
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) : SourceReesRing C :=
  ReesRing.monomial (SourceFiltration C)
    (C.inverse.denominator_degree s) (s : R)
    (C.inverse.denominator_admissible s).choose

theorem sourceHomogeneousDenominator_coeff
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) :
    ((sourceHomogeneousDenominator C s : SourceReesRing C) :
      ReesPolynomial R).coeff (C.inverse.denominator_degree s) =
      (s : R) := by
  change (SkewPolynomial.monomial
      (C.inverse.denominator_degree s) (s : R)).coeff
        (C.inverse.denominator_degree s) = (s : R)
  rw [SkewPolynomial.coeff_monomial]
  simp

private theorem sourceHomogeneousDenominator_mul
    (C : SymbolFractionFiltration.Data R)
    (s t : C.inverse.localization.denominators) :
    sourceHomogeneousDenominator C s * sourceHomogeneousDenominator C t =
      sourceHomogeneousDenominator C (s * t) := by
  apply Subtype.ext
  change
    SkewMonoidAlgebra.single
        (Multiplicative.ofAdd (C.inverse.denominator_degree s)) (s : R) *
      SkewMonoidAlgebra.single
        (Multiplicative.ofAdd (C.inverse.denominator_degree t)) (t : R) =
    SkewMonoidAlgebra.single
      (Multiplicative.ofAdd (C.inverse.denominator_degree (s * t)))
      ((s * t : C.inverse.localization.denominators) : R)
  rw [SkewMonoidAlgebra.single_mul_single]
  change SkewMonoidAlgebra.single _ ((s : R) * (t : R)) = _
  simp [denominator_degree_mul C s t]

private theorem sourceHomogeneousDenominator_one
    (C : SymbolFractionFiltration.Data R) :
    sourceHomogeneousDenominator C
        (1 : C.inverse.localization.denominators) = 1 := by
  apply Subtype.ext
  change SkewPolynomial.monomial
      (C.inverse.denominator_degree
        (1 : C.inverse.localization.denominators)) (1 : R) = 1
  rw [denominator_degree_one C]
  exact SkewPolynomial.C_1

/- The selected source terms form a genuine monoid map.  Its multiplicativity
   uses the actual selected-degree theorem above, rather than a closure
   callback for the desired image. -/
noncomputable def sourceHomogeneousDenominatorMonoidHom
    (C : SymbolFractionFiltration.Data R) :
    C.inverse.localization.denominators →* SourceReesRing C where
  toFun := sourceHomogeneousDenominator C
  map_one' := sourceHomogeneousDenominator_one C
  map_mul' := fun s t => (sourceHomogeneousDenominator_mul C s t).symm

theorem map_sourceHomogeneousDenominator
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) :
    map C (sourceHomogeneousDenominator C s) =
      SymbolFractionRees.homogeneousDenominator C s := by
  unfold sourceHomogeneousDenominator
  rw [map_homogeneous]
  rfl

/- Composing with the actual source map packages the same selected terms in
   the Laurent fraction Rees ring. -/
noncomputable def homogeneousDenominatorMonoidHom
    (C : SymbolFractionFiltration.Data R) :
    C.inverse.localization.denominators →*
      SymbolFractionRees.ReesRing C :=
  (map C).toMonoidHom.comp (sourceHomogeneousDenominatorMonoidHom C)

@[simp] theorem homogeneousDenominatorMonoidHom_apply
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) :
    homogeneousDenominatorMonoidHom C s =
      SymbolFractionRees.homogeneousDenominator C s := by
  exact map_sourceHomogeneousDenominator C s

theorem map_homogeneous_coeff
    (C : SymbolFractionFiltration.Data R) (n : ℕ) (a : R)
    (ha : a ∈ C.inverse.filtration.carrier n) :
    ((map C (ReesRing.monomial (SourceFiltration C) n a ha) :
        SymbolFractionRees.ReesRing C) :
      SymbolFractionRees.LaurentPolynomial C).coeff (Int.ofNat n) =
      C.inverse.localization.numerator a := by
  rw [map_homogeneous]
  change (AddMonoidAlgebra.single (Int.ofNat n)
      (C.inverse.localization.numerator a)).coeff (Int.ofNat n) =
    C.inverse.localization.numerator a
  exact Finsupp.single_eq_same

end SymbolFractionReesMap

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.SymbolFractionReesMap.map
#print axioms SymplecticStafford.Filtered.SymbolFractionReesMap.map_injective
#print axioms SymplecticStafford.Filtered.SymbolFractionReesMap.ambientMap_injective
#print axioms SymplecticStafford.Filtered.SymbolFractionReesMap.map_homogeneous
#print axioms
  SymplecticStafford.Filtered.SymbolFractionReesMap.sourceHomogeneousDenominator_coeff
#print axioms
  SymplecticStafford.Filtered.SymbolFractionReesMap.map_sourceHomogeneousDenominator
#print axioms
  SymplecticStafford.Filtered.SymbolFractionReesMap.homogeneousDenominatorMonoidHom_apply
#print axioms SymplecticStafford.Filtered.SymbolFractionReesMap.map_homogeneous_coeff
