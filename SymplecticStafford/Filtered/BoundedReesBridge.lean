import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import SymplecticStafford.Filtered.ReesRing

/-!
# The bounded homogeneous Rees bridge

`ReesRing F` is a bounded-polynomial subring, not yet an associated graded
ring.  This file records the exact coefficient-level identification that is
available from that definition: every element is a finite sum of bounded
homogeneous terms, and every finite family of bounded coefficients has a
unique polynomial lift.  The latter uniqueness is coefficientwise, so no
completion, specialization, or commutative associated-graded hypothesis is
being smuggled in.

The final theorem gives a useful M02 consumer.  If every ideal has finitely
many generators whose ideal span contains every bounded homogeneous term,
then the bounded Rees ring is Noetherian.  This is a genuine criterion for
the actual `ReesRing F`; it does not claim that the filtration axioms supply
the finite homogeneous generation hypothesis.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

variable {R : Type u} [Ring R]

open Multiplicative SkewMonoidAlgebra
open scoped BigOperators

namespace ReesRing

variable (F : NegFiltrationData R)

/- A bounded lift of one homogeneous coefficient. -/
def homogeneousLift (n : ℕ) (a : R) (ha : a ∈ F.carrier n) : ReesRing F :=
  ReesRing.monomial F n a ha

@[simp] theorem coe_homogeneousLift (n : ℕ) (a : R)
    (ha : a ∈ F.carrier n) :
    ((homogeneousLift F n a ha : ReesRing F) : ReesPolynomial R) =
      SkewPolynomial.monomial n a :=
  ReesRing.coe_monomial F n a ha

@[simp] theorem homogeneousLift_coeff_eq (n : ℕ) (a : R)
    (ha : a ∈ F.carrier n) :
    ((homogeneousLift F n a ha : ReesRing F) : ReesPolynomial R).coeff n = a := by
  change (SkewPolynomial.monomial n a).coeff n = a
  rw [SkewPolynomial.coeff_monomial]
  simp

theorem homogeneousLift_coeff_ne (n m : ℕ) (a : R)
    (ha : a ∈ F.carrier n) (hmn : m ≠ n) :
    ((homogeneousLift F n a ha : ReesRing F) : ReesPolynomial R).coeff m = 0 := by
  change (SkewPolynomial.monomial n a).coeff m = 0
  rw [SkewPolynomial.coeff_monomial]
  rw [if_neg (Ne.symm hmn)]

/- Coefficients are a complete invariant of bounded Rees elements because the
   ambient skew-polynomial representation has coefficient extensionality. -/
theorem ext_of_coeff_eq {p q : ReesRing F}
    (h : ∀ n : ℕ,
      ((p : ReesPolynomial R).coeff n) = ((q : ReesPolynomial R).coeff n)) :
    p = q := by
  apply Subtype.ext
  exact SkewPolynomial.ext h

/- The support-indexed homogeneous decomposition of an arbitrary bounded
   Rees element.  The proof is carried out in the ambient polynomial ring;
   the subtype terms are then recovered by injectivity of the inclusion. -/
def supportDecomposition (p : ReesRing F) : ReesRing F :=
  ∑ n ∈ (p : ReesPolynomial R).support,
    homogeneousLift F n ((p : ReesPolynomial R).coeff n) (p.property n)

theorem coe_supportDecomposition (p : ReesRing F) :
    ((supportDecomposition F p : ReesRing F) : ReesPolynomial R) =
      (p : ReesPolynomial R) := by
  unfold supportDecomposition
  change (ReesRing.inclusion F) (∑ n ∈ (p : ReesPolynomial R).support,
      homogeneousLift F n ((p : ReesPolynomial R).coeff n) (p.property n)) =
    (p : ReesPolynomial R)
  rw [_root_.map_sum]
  change (∑ n ∈ (p : ReesPolynomial R).support,
      SkewPolynomial.monomial n ((p : ReesPolynomial R).coeff n)) =
    (p : ReesPolynomial R)
  rw [← SkewPolynomial.sum_def (p : ReesPolynomial R)
    (fun n a => SkewPolynomial.monomial n a)]
  exact SkewPolynomial.sum_monomial (p : ReesPolynomial R)

theorem supportDecomposition_eq (p : ReesRing F) :
    supportDecomposition F p = p := by
  apply ReesRing.inclusion_injective F
  exact coe_supportDecomposition F p

/- A finite list of coefficients can be lifted at once.  Terms outside the
   selected finite set are absent from the resulting sum. -/
def finiteHomogeneousLift (s : Finset ℕ) (a : ℕ → R)
    (ha : ∀ n : ℕ, a n ∈ F.carrier n) : ReesRing F :=
  ∑ n ∈ s, homogeneousLift F n (a n) (ha n)

theorem coe_finiteHomogeneousLift (s : Finset ℕ) (a : ℕ → R)
    (ha : ∀ n : ℕ, a n ∈ F.carrier n) :
    ((finiteHomogeneousLift F s a ha : ReesRing F) : ReesPolynomial R) =
      ∑ n ∈ s, SkewPolynomial.monomial n (a n) := by
  unfold finiteHomogeneousLift
  change (ReesRing.inclusion F) (∑ n ∈ s,
      homogeneousLift F n (a n) (ha n)) = _
  rw [_root_.map_sum]
  change (∑ n ∈ s, SkewPolynomial.monomial n (a n)) = _
  rfl

/- Every bounded Rees element is recovered by the finite lift of its own
   coefficient function and support. -/
theorem finiteHomogeneousLift_support (p : ReesRing F) :
    finiteHomogeneousLift F (p : ReesPolynomial R).support
      (fun n => (p : ReesPolynomial R).coeff n) (fun n => p.property n) = p := by
  apply ReesRing.inclusion_injective F
  unfold finiteHomogeneousLift
  change (ReesRing.inclusion F) (∑ n ∈ (p : ReesPolynomial R).support,
      homogeneousLift F n ((p : ReesPolynomial R).coeff n) (p.property n)) =
    (p : ReesPolynomial R)
  rw [_root_.map_sum]
  change (∑ n ∈ (p : ReesPolynomial R).support,
      SkewPolynomial.monomial n ((p : ReesPolynomial R).coeff n)) =
    (p : ReesPolynomial R)
  rw [← SkewPolynomial.sum_def (p : ReesPolynomial R)
    (fun n a => SkewPolynomial.monomial n a)]
  exact SkewPolynomial.sum_monomial (p : ReesPolynomial R)

/- If the homogeneous components of an element of an ideal lie in a fixed
   ideal span, its finite support decomposition puts the whole element there.
   This is the precise bridge from homogeneous finite generation to ideal
   finite generation. -/
theorem mem_ideal_span_of_homogeneous_mem
    (I : Ideal (ReesRing F)) (s : Finset (ReesRing F))
    (hhom : ∀ p : ReesRing F, p ∈ I →
      ∀ n : ℕ, homogeneousLift F n ((p : ReesPolynomial R).coeff n)
        (p.property n) ∈ Ideal.span (s : Set (ReesRing F)))
    (p : ReesRing F) (hp : p ∈ I) :
    p ∈ Ideal.span (s : Set (ReesRing F)) := by
  rw [← supportDecomposition_eq F p]
  have hsum : ∀ t : Finset ℕ,
      (∑ n ∈ t, homogeneousLift F n ((p : ReesPolynomial R).coeff n)
        (p.property n)) ∈ Ideal.span (s : Set (ReesRing F)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, Submodule.zero_mem]
    | @insert n t hnt ih =>
        rw [Finset.sum_insert hnt]
        apply (Ideal.span (s : Set (ReesRing F))).add_mem
        · exact hhom p hp n
        · exact ih
  exact hsum (p : ReesPolynomial R).support

theorem ideal_eq_span_of_homogeneous_mem
    (I : Ideal (ReesRing F)) (s : Finset (ReesRing F))
    (hs : ∀ x ∈ s, x ∈ I)
    (hhom : ∀ p : ReesRing F, p ∈ I →
      ∀ n : ℕ, homogeneousLift F n ((p : ReesPolynomial R).coeff n)
        (p.property n) ∈ Ideal.span (s : Set (ReesRing F))) :
    I = Ideal.span (s : Set (ReesRing F)) := by
  apply le_antisymm
  · intro p hp
    exact mem_ideal_span_of_homogeneous_mem F I s hhom p hp
  · exact Ideal.span_le.2 (fun x hx => hs x hx)

end ReesRing

/- The finite homogeneous-generation criterion is the useful Noetherian
   consequence.  Its premise quantifies over actual ideals of the actual
   bounded Rees ring, so it is not a proposition-valued replacement for a
   filtered/associated-graded theorem. -/
theorem isNoetherianRing_of_finite_homogeneous_ideal_generators
    (F : NegFiltrationData R)
    (hgen : ∀ I : Ideal (ReesRing F), ∃ s : Finset (ReesRing F),
      (∀ x ∈ s, x ∈ I) ∧
      (∀ p : ReesRing F, p ∈ I → ∀ n : ℕ,
        ReesRing.homogeneousLift F n ((p : ReesPolynomial R).coeff n)
          (p.property n) ∈ Ideal.span (s : Set (ReesRing F)))) :
    IsNoetherianRing (ReesRing F) := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  obtain ⟨s, hs, hhom⟩ := hgen I
  rw [ReesRing.ideal_eq_span_of_homogeneous_mem F I s hs hhom]
  exact Submodule.fg_span s.finite_toSet

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.ReesRing.coe_supportDecomposition
#print axioms SymplecticStafford.Filtered.ReesRing.coe_finiteHomogeneousLift
#print axioms SymplecticStafford.Filtered.ReesRing.ext_of_coeff_eq
#print axioms SymplecticStafford.Filtered.ReesRing.finiteHomogeneousLift_support
#print axioms SymplecticStafford.Filtered.ReesRing.ideal_eq_span_of_homogeneous_mem
#print axioms SymplecticStafford.Filtered.isNoetherianRing_of_finite_homogeneous_ideal_generators
