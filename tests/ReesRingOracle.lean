import Mathlib.Tactic.NormNum
import SymplecticStafford.Filtered.ReesRing

/- Independent behavioral checks for the actual ring-valued Rees object.  The
   all-degree filtration on `ℤ` makes the ring closure executable while still
   exercising addition, negation, multiplication and coefficient extraction. -/
namespace SymplecticStaffordTest.ReesRing

open SymplecticStafford.Filtered

def allFiltration : NegFiltrationData ℤ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; simp
  exhaustive := by intro a; exact ⟨0, by simp⟩
  neg_mem := by simp

def F : NegFiltrationData ℤ := allFiltration

example (p : ReesRing F) :
    NegReesBounded F (p : ReesPolynomial ℤ) :=
  p.property

example (p q : ReesRing F) :
    ((p - q : ReesRing F) : ReesPolynomial ℤ) =
      (p : ReesPolynomial ℤ) - q :=
  ReesRing.coe_sub F p q

example : Function.Injective (ReesRing.inclusion F) :=
  ReesRing.inclusion_injective F

example (n : ℕ) (a : ℤ) :
    ((ReesRing.monomial F n a (by
      change a ∈ Set.univ
      exact Set.mem_univ a) : ReesRing F) : ReesPolynomial ℤ).coeff n ∈
      F.carrier n := by
  exact ReesRing.coefficient_mem F
    (ReesRing.monomial F n a (by
      change a ∈ Set.univ
      exact Set.mem_univ a)) n

example (n : ℕ) (a : ℤ) :
    (ReesRing.monomial F n a (by
      change a ∈ Set.univ
      exact Set.mem_univ a) : ReesPolynomial ℤ) =
      SkewPolynomial.monomial n a := by
  exact ReesRing.coe_monomial F n a (by
    change a ∈ Set.univ
    exact Set.mem_univ a)

end SymplecticStaffordTest.ReesRing
