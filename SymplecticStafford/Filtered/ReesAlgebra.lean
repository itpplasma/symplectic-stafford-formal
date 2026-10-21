module

public import Mathlib.Algebra.SkewPolynomial.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Data.Finset.Fold
public import SymplecticStafford.Filtered.ReesBasic
public import SymplecticStafford.Filtered.ReesQuotient

@[expose] public section

/-!
# An algebraic Rees-like subobject

This file packages the bounded homogeneous terms as a genuine subobject of a
skew-polynomial ambient algebra.  The scoped action is the trivial action of
the degree monoid, so multiplication is ordinary convolution with the
coefficient order inherited from `R`.  The filtration axioms prove closure of
the coefficient predicate under addition and multiplication.

The construction is deliberately finite and algebraic.  It does not assert
Noetherianity, an Ore condition, a full symbol localization, or a faithful
associated-graded theorem.  The value map and its image inclusion are the
only quotient/graded interfaces supplied here.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

variable {R : Type u} [Semiring R]

open Multiplicative SkewMonoidAlgebra
open scoped BigOperators

/- The degree monoid acts trivially on coefficients.  This is scoped so that
  a client with a genuinely skew coefficient action can choose another
  construction without an instance conflict. -/
instance trivialDegreeSMul : SMul (Multiplicative ℕ) R :=
  ⟨fun _ a => a⟩

instance trivialDegreeAction : MulSemiringAction (Multiplicative ℕ) R where
  one_smul := by intro a; rfl
  mul_smul := by intro _ _ a; rfl
  smul_zero := by intro _; rfl
  smul_add := by intro _ _ _; rfl
  smul_one := by intro _; rfl
  smul_mul := by intro _ _ _; rfl

abbrev ReesPolynomial (R : Type u) [AddCommMonoid R] := SkewPolynomial R

/-- A polynomial whose coefficient in degree `n` lies in `F_n`. -/
def ReesBounded (F : FiltrationData R) (p : ReesPolynomial R) : Prop :=
  ∀ n : ℕ, p.coeff n ∈ F.carrier n

theorem ReesBounded.zero (F : FiltrationData R) :
    ReesBounded F (0 : ReesPolynomial R) := by
  intro n
  exact F.monotone (Nat.zero_le n) F.zero_mem

theorem ReesBounded.one (F : FiltrationData R) :
    ReesBounded F (1 : ReesPolynomial R) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [ReesBounded] using F.one_mem
  · have hz : (0 : R) ∈ F.carrier n := F.monotone (Nat.zero_le n) F.zero_mem
    change SkewMonoidAlgebra.coeff
      (1 : SkewMonoidAlgebra R (Multiplicative ℕ))
      (Multiplicative.ofAdd n) ∈ F.carrier n
    rw [SkewMonoidAlgebra.one_def]
    simp [hn, hz]

theorem ReesBounded.add {F : FiltrationData R} {p q : ReesPolynomial R}
    (hp : ReesBounded F p) (hq : ReesBounded F q) :
    ReesBounded F (p + q) := by
  intro n
  rw [SkewPolynomial.coeff_add]
  simpa using F.add_mem (hp n) (hq n)

private theorem finset_sum_mem {α : Type*} {F : FiltrationData R}
    {n : ℕ} {s : Finset α} {g : α → R}
    (hg : ∀ a ∈ s, g a ∈ F.carrier n) :
    (∑ a ∈ s, g a) ∈ F.carrier n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact F.monotone (Nat.zero_le n) F.zero_mem
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      simpa using F.add_mem (hg a (by simp)) (ih (by
        intro b hb
        exact hg b (by simp [hb])))

theorem ReesBounded.mul {F : FiltrationData R} {p q : ReesPolynomial R}
    (hp : ReesBounded F p) (hq : ReesBounded F q) :
    ReesBounded F (p * q) := by
  intro n
  change (SkewMonoidAlgebra.coeff (p * q) (Multiplicative.ofAdd n)) ∈ F.carrier n
  rw [SkewMonoidAlgebra.coeff_mul]
  apply finset_sum_mem
  intro a₁ ha₁
  apply finset_sum_mem
  intro a₂ ha₂
  by_cases hdeg : a₁ * a₂ = Multiplicative.ofAdd n
  · simp only [hdeg, if_pos]
    change p.coeff a₁.toAdd * q.coeff a₂.toAdd ∈ F.carrier n
    have hsum : a₁.toAdd + a₂.toAdd = n := by
      exact congrArg Multiplicative.toAdd hdeg
    rw [← hsum]
    exact F.mul_mem (hp a₁.toAdd) (hq a₂.toAdd)
  · have hz : (0 : R) ∈ F.carrier n := F.monotone (Nat.zero_le n) F.zero_mem
    simpa [hdeg] using hz

/- The coefficient predicate is itself closed under the convolution algebra's
   addition and multiplication.  This is the actual Rees-like subobject; no
   quotienting or localization is involved in its definition. -/
def reesSubsemiring (F : FiltrationData R) :
    Subsemiring (ReesPolynomial R) where
  carrier := {p | ReesBounded F p}
  zero_mem' := ReesBounded.zero F
  one_mem' := ReesBounded.one F
  add_mem' := ReesBounded.add
  mul_mem' := ReesBounded.mul

abbrev ReesAlgebra (F : FiltrationData R) := reesSubsemiring F

/-- The inclusion of bounded Rees polynomials into the ambient convolution
algebra. -/
def ReesAlgebra.inclusion (F : FiltrationData R) :
    ReesAlgebra F →+* ReesPolynomial R := (reesSubsemiring F).subtype

theorem ReesAlgebra.coe_bounded (F : FiltrationData R) (p : ReesAlgebra F) :
    ReesBounded F (p : ReesPolynomial R) :=
  p.property

theorem ReesAlgebra.inclusion_injective (F : FiltrationData R) :
    Function.Injective (ReesAlgebra.inclusion F) := by
  intro p q h
  exact Subtype.ext h

/-- The coefficient in each degree is a graded map into the underlying
filtration piece.  The membership theorem below is its filtration bound. -/
def ReesAlgebra.degreeCoefficient (F : FiltrationData R) (n : ℕ) :
    ReesAlgebra F →+ R where
  toFun p := (p : ReesPolynomial R).coeff n
  map_zero' := by simp
  map_add' p q := by simp [SkewPolynomial.coeff_add]

theorem ReesAlgebra.degreeCoefficient_mem
    (F : FiltrationData R) (n : ℕ) (p : ReesAlgebra F) :
    ReesAlgebra.degreeCoefficient F n p ∈ F.carrier n :=
  p.property n

theorem ReesAlgebra.degreeCoefficient_apply
    (F : FiltrationData R) (n : ℕ) (p : ReesAlgebra F) :
    ReesAlgebra.degreeCoefficient F n p =
      (p : ReesPolynomial R).coeff n := rfl

theorem ReesAlgebra.degreeCoefficient_add
    (F : FiltrationData R) (n : ℕ) (p q : ReesAlgebra F) :
    ReesAlgebra.degreeCoefficient F n (p + q) =
      ReesAlgebra.degreeCoefficient F n p +
        ReesAlgebra.degreeCoefficient F n q := by
  exact (ReesAlgebra.degreeCoefficient F n).map_add p q

/- The quotient map for bounded homogeneous terms is included explicitly so
   reindexing can be consumed without choosing a degree representative. -/
def quotientMap (F : FiltrationData R) :
    ReesTerm F → ReesQuotient F := ReesQuotient.mk

theorem quotientMap_value (F : FiltrationData R) (x : ReesTerm F) :
    ReesQuotient.value (quotientMap F x) = x.value :=
  ReesQuotient.value_mk x

theorem quotientMap_reindex (F : FiltrationData R) (x : ReesTerm F)
    {n : ℕ} (h : x.degree ≤ n) :
    quotientMap F (ReesTerm.reindex x h) = quotientMap F x :=
  ReesQuotient.reindex_mk x h

theorem monomial_bounded (F : FiltrationData R) (n : ℕ) (a : R)
    (ha : a ∈ F.carrier n) : ReesBounded F (SkewPolynomial.monomial n a) := by
  intro m
  rw [SkewPolynomial.coeff_monomial]
  by_cases hnm : n = m
  · simpa [hnm] using ha
  · have hz : (0 : R) ∈ F.carrier m := F.monotone (Nat.zero_le m) F.zero_mem
    simpa [hnm] using hz

def ReesAlgebra.monomial (F : FiltrationData R) (n : ℕ) (a : R)
    (ha : a ∈ F.carrier n) : ReesAlgebra F :=
  ⟨SkewPolynomial.monomial n a, monomial_bounded F n a ha⟩

theorem ReesAlgebra.coe_monomial (F : FiltrationData R) (n : ℕ) (a : R)
    (ha : a ∈ F.carrier n) :
    ((ReesAlgebra.monomial F n a ha : ReesAlgebra F) : ReesPolynomial R) =
      SkewPolynomial.monomial n a := rfl

end

end SymplecticStafford.Filtered
