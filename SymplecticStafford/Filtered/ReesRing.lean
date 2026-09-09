import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.SkewPolynomial.Basic
import SymplecticStafford.Filtered.ReesAlgebra

/-!
# The algebraic Rees ring for a ring filtration

`ReesAlgebra` is a useful semiring checkpoint, but its carrier does not yet
record additive inverses.  For a ring filtration the same coefficient bounds
are closed under negation, so the bounded skew polynomials form an actual
`Subring`.  This is the algebraic Rees object used by the subsequent
Noetherian and localization arguments; no completion or principal-open
replacement is involved.

The construction is deliberately parameterised by the concrete filtration
data.  It proves exactly what follows from those data (closure, inclusion and
finite-support coefficient extraction), while leaving the genuinely separate
leading-term Noetherian and Ore certificates explicit.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

variable {R : Type u} [Ring R]

open Multiplicative SkewMonoidAlgebra

/- The old `FiltrationData` is intentionally semiring-general.  This small
   ring refinement supplies the additive-inverse closure needed for an
   actual Rees ring. -/
structure NegFiltrationData (R : Type u) [Ring R]
    extends FiltrationData R where
  neg_mem : ∀ {n : ℕ} {a : R}, a ∈ carrier n → -a ∈ carrier n

abbrev NegReesBounded (F : NegFiltrationData R) (p : ReesPolynomial R) : Prop :=
  ReesBounded F.toFiltrationData p

/- `ReesAlgebra` installs the trivial degree action, which is the central
   indeterminate used by this algebraic Rees presentation. -/

theorem NegReesBounded.neg {F : NegFiltrationData R} {p : ReesPolynomial R}
    (hp : NegReesBounded F p) : NegReesBounded F (-p) := by
  intro n
  rw [SkewPolynomial.coeff_neg]
  exact F.neg_mem (hp n)

theorem NegReesBounded.sub {F : NegFiltrationData R} {p q : ReesPolynomial R}
    (hp : NegReesBounded F p) (hq : NegReesBounded F q) :
    NegReesBounded F (p - q) := by
  simpa only [sub_eq_add_neg] using ReesBounded.add hp (NegReesBounded.neg hq)

/-- The genuine algebraic Rees ring attached to `F`. -/
def reesSubring (F : NegFiltrationData R) : Subring (ReesPolynomial R) where
  carrier := {p | NegReesBounded F p}
  zero_mem' := ReesBounded.zero F.toFiltrationData
  one_mem' := ReesBounded.one F.toFiltrationData
  add_mem' := ReesBounded.add
  neg_mem' := NegReesBounded.neg
  mul_mem' := ReesBounded.mul

abbrev ReesRing (F : NegFiltrationData R) := reesSubring F

def ReesRing.inclusion (F : NegFiltrationData R) :
    ReesRing F →+* ReesPolynomial R := (reesSubring F).subtype

theorem ReesRing.coe_bounded (F : NegFiltrationData R) (p : ReesRing F) :
    NegReesBounded F (p : ReesPolynomial R) := p.property

theorem ReesRing.inclusion_injective (F : NegFiltrationData R) :
    Function.Injective (ReesRing.inclusion F) := by
  intro p q h
  exact Subtype.ext h

theorem ReesRing.coe_sub (F : NegFiltrationData R) (p q : ReesRing F) :
    ((p - q : ReesRing F) : ReesPolynomial R) = (p : ReesPolynomial R) - q := rfl

theorem ReesRing.coe_neg (F : NegFiltrationData R) (p : ReesRing F) :
    ((-p : ReesRing F) : ReesPolynomial R) = -(p : ReesPolynomial R) := rfl

/-! A finite polynomial has a finite list of bounded coefficient witnesses.
This is the concrete coefficient-level bridge needed before a graded
leading-term argument can be applied. -/
theorem ReesRing.coefficient_mem (F : NegFiltrationData R) (p : ReesRing F)
    (n : ℕ) : (p : ReesPolynomial R).coeff n ∈ F.carrier n := p.property n

def ReesRing.monomial (F : NegFiltrationData R) (n : ℕ) (a : R)
    (ha : a ∈ F.carrier n) : ReesRing F :=
  ⟨SkewPolynomial.monomial n a, by
    intro m
    rw [SkewPolynomial.coeff_monomial]
    by_cases hnm : n = m
    · simpa [hnm] using ha
    · simpa [hnm] using (F.monotone (Nat.zero_le m) F.zero_mem)⟩

theorem ReesRing.coe_monomial (F : NegFiltrationData R) (n : ℕ) (a : R)
    (ha : a ∈ F.carrier n) :
    ((ReesRing.monomial F n a ha : ReesRing F) : ReesPolynomial R) =
      SkewPolynomial.monomial n a := rfl

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.NegReesBounded.neg
#print axioms SymplecticStafford.Filtered.ReesRing.inclusion_injective
#print axioms SymplecticStafford.Filtered.ReesRing.coefficient_mem
