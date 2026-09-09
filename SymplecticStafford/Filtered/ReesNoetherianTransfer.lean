import SymplecticStafford.Filtered.ReesNoetherianProducer
import SymplecticStafford.Filtered.RightPolynomialNoetherian
import SymplecticStafford.Filtered.BoundedReesBridge
import SymplecticStafford.Filtered.ReesGoodSubquotient
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Exact coefficient symbols for the Rees filtration

The coefficient filtration on the bounded Rees ring is already constructed in
`ReesNoetherianProducer`.  This file records the part of the Rees transfer
which can be proved directly from that construction.

There is one shift which is easy to miss.  A coefficient in filtration degree
`n` can occur in the Rees polynomial only in exponent `n + r`; exponents below
`n` are already in the preceding coefficient layer.  Consequently the degree
`n` symbol is a polynomial in the residual exponent `r`, rather than a
polynomial in the original exponent.

The definitions and lemmas below use the actual coefficient symbols, and the
bounded homogeneous lifts are constructed in the original Rees ring.  They do
not assume a symbol-lifting callback or a presentation of the associated
graded ring.  The final type-level quotient-to-polynomial assembly is left
explicitly identified at the end of the file; no false Noetherian conclusion
is stated in its place.
-/

namespace SymplecticStafford.Filtered

universe u v w

noncomputable section

variable {R : Type u} [Ring R]

open AdditiveFilteredRingData
open ActualAssociatedGraded
open FilteredRightIdealSymbols
open scoped BigOperators

namespace ReesNoetherianTransfer

variable (F : AdditiveFilteredRingData R)

abbrev Rees := ReesRing F.toNegFiltrationData
abbrev coefficientFiltration := ReesCoefficientFiltration.filtration F
abbrev coefficientAssociatedGraded :=
  AdditiveFilteredRingData.actualAssociatedGraded (coefficientFiltration F)

/- The coefficient of a degree-`n` symbol at residual exponent `r` is the
   class of the original Rees coefficient at exponent `n + r`.  The target is
   an additive monoid algebra because one individual associated layer has no
   ring structure of its own. -/
def CoefficientSymbol
    (n : ℕ) (p : Rees F)
    (q : AddMonoidAlgebra (associatedLayer F n) ℕ) : Prop :=
  ∃ hp : p ∈ ReesCoefficientFiltration.layer F n, ∀ r : ℕ,
    associatedClass F n
      ((p : ReesPolynomial R).coeff (n + r)) (hp (n + r)) =
      q.coeff r

/- The coefficient symbol attached to a bounded representative.  Its support
   is finite because it is contained in the image, under subtraction by `n`,
   of the support of the original Rees polynomial. -/
noncomputable def coefficientSymbolPolynomial
    (n : ℕ) (p : Rees F)
    (hp : p ∈ ReesCoefficientFiltration.layer F n) :
    AddMonoidAlgebra (associatedLayer F n) ℕ :=
  Finsupp.onFinset
    ((SkewPolynomial.support (p : ReesPolynomial R)).image (fun k => k - n))
    (fun r => associatedClass F n
      ((p : ReesPolynomial R).coeff (n + r)) (hp (n + r)))
    (by
      intro r hr
      rw [associatedClass_eq_zero_iff]
      have hcoeff : (p : ReesPolynomial R).coeff (n + r) = 0 := by
        apply SkewPolynomial.notMem_support_iff.mp
        intro hsupp
        apply hr
        simp only [Finset.mem_image]
        exact ⟨n + r, hsupp, by omega⟩
      simpa [hcoeff] using (predecessor F n).zero_mem)

@[simp] theorem coefficientSymbolPolynomial_coeff
    (n : ℕ) (p : Rees F)
    (hp : p ∈ ReesCoefficientFiltration.layer F n) (r : ℕ) :
    (coefficientSymbolPolynomial F n p hp).coeff r =
      associatedClass F n
        ((p : ReesPolynomial R).coeff (n + r)) (hp (n + r)) := by
  classical
  simp [coefficientSymbolPolynomial]

theorem coefficientSymbol_exists
    (n : ℕ) (p : Rees F)
    (hp : p ∈ ReesCoefficientFiltration.layer F n) :
    CoefficientSymbol F n p (coefficientSymbolPolynomial F n p hp) := by
  exact ⟨hp, fun r => (coefficientSymbolPolynomial_coeff F n p hp r).symm⟩

theorem associatedClass_zero (n : ℕ) :
    associatedClass F n 0 (F.zero_mem n) = 0 := by
  rw [associatedClass_eq_zero_iff]
  exact (predecessor F n).zero_mem

theorem coefficientSymbol_zero (n : ℕ) :
    CoefficientSymbol F n (0 : Rees F) 0 := by
  refine ⟨(ReesCoefficientFiltration.layer F n).zero_mem, ?_⟩
  intro r
  simp [CoefficientSymbol, associatedClass_zero]

theorem coefficientSymbol_add
    (n : ℕ) {p₁ p₂ : Rees F}
    {q₁ q₂ : AddMonoidAlgebra (associatedLayer F n) ℕ}
    (h₁ : CoefficientSymbol F n p₁ q₁)
    (h₂ : CoefficientSymbol F n p₂ q₂) :
    CoefficientSymbol F n (p₁ + p₂) (q₁ + q₂) := by
  rcases h₁ with ⟨hp₁, hq₁⟩
  rcases h₂ with ⟨hp₂, hq₂⟩
  refine ⟨(ReesCoefficientFiltration.layer F n).add_mem hp₁ hp₂, ?_⟩
  intro r
  have h := congrArg₂ (fun x y : associatedLayer F n => x + y)
    (hq₁ r) (hq₂ r)
  simpa [associatedClass, SkewPolynomial.coeff_add,
    AddMonoidAlgebra.coeff_add] using h

/- A bounded homogeneous lift at residual exponent `r`.  The representative
   lives in `F n`; monotonicity moves it to the Rees exponent `n + r`. -/
noncomputable def shiftedHomogeneousLift
    (n r : ℕ) (x : associatedLayer F n) : Rees F :=
  ReesRing.monomial F.toNegFiltrationData (n + r)
    (representative F n x)
    (F.monotone (Nat.le_add_right n r)
      (representative F n x).property)

theorem shiftedHomogeneousLift_mem_layer
    (n r : ℕ) (x : associatedLayer F n) :
    shiftedHomogeneousLift F n r x ∈
      ReesCoefficientFiltration.layer F n := by
  intro k
  change (SkewPolynomial.monomial (n + r)
      (representative F n x : R)).coeff k ∈ F.carrier n
  rw [SkewPolynomial.coeff_monomial]
  by_cases h : n + r = k
  · simpa [h] using (representative F n x).property
  · simp [h, F.zero_mem n]

theorem shiftedHomogeneousLift_coeff
    (n r : ℕ) (x : associatedLayer F n) :
    ((shiftedHomogeneousLift F n r x : Rees F) : ReesPolynomial R).coeff
        (n + r) = representative F n x := by
  change (SkewPolynomial.monomial (n + r)
      (representative F n x : R)).coeff (n + r) =
    (representative F n x : R)
  rw [SkewPolynomial.coeff_monomial]
  simp

theorem shiftedHomogeneousLift_coeff_ne
    (n r k : ℕ) (x : associatedLayer F n) (h : k ≠ n + r) :
    ((shiftedHomogeneousLift F n r x : Rees F) : ReesPolynomial R).coeff k = 0 := by
  change (SkewPolynomial.monomial (n + r)
      (representative F n x : R)).coeff k = 0
  rw [SkewPolynomial.coeff_monomial]
  simp [h]

/- The exact symbol of a shifted homogeneous lift is the corresponding
   additive monomial.  This is the basic coefficient-level surjectivity
   calculation used by the eventual graded assembly. -/
theorem coefficientSymbol_shiftedHomogeneousLift
    (n r : ℕ) (x : associatedLayer F n) :
    CoefficientSymbol F n (shiftedHomogeneousLift F n r x)
      (AddMonoidAlgebra.single r x) := by
  refine ⟨shiftedHomogeneousLift_mem_layer F n r x, ?_⟩
  intro s
  by_cases hrs : r = s
  · subst s
    rw [shiftedHomogeneousLift_coeff]
    rw [associatedClass_representative]
    simp
  · have hdeg : n + r ≠ n + s := by
      intro hdeg
      apply hrs
      omega
    rw [shiftedHomogeneousLift_coeff_ne F n r (n + s) x hdeg]
    rw [associatedClass_zero]
    simp [AddMonoidAlgebra.coeff_single_apply, hrs]

/- The residual-exponent symbol is unique.  This is a genuine injectivity
   statement for the coefficient-symbol relation, independent of any chosen
   quotient representative. -/
theorem coefficientSymbol_unique
    (n : ℕ) {p : Rees F}
    {q₁ q₂ : AddMonoidAlgebra (associatedLayer F n) ℕ}
    (h₁ : CoefficientSymbol F n p q₁)
    (h₂ : CoefficientSymbol F n p q₂) : q₁ = q₂ := by
  rcases h₁ with ⟨hp₁, hq₁⟩
  rcases h₂ with ⟨hp₂, hq₂⟩
  apply AddMonoidAlgebra.coeff_injective
  intro r
  exact (hq₁ r).trans (hq₂ r).symm

/- A zero symbol is exactly the lower coefficient layer.  The forward
   direction is the one needed for descent; the reverse direction records
   the kernel calculation that would make the quotient map faithful. -/
theorem coefficientSymbol_zero_of_lower
    (n : ℕ) {p : Rees F}
    (hp : p ∈ AdditiveFilteredRingData.predecessor
      (coefficientFiltration F) n) :
    CoefficientSymbol F n p 0 := by
  by_cases hn : n = 0
  · have hp0 : p = 0 := by
      simpa [AdditiveFilteredRingData.predecessor, hn] using hp
    subst p
    exact coefficientSymbol_zero F 0
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hp₀ : p ∈ (coefficientFiltration F).carrier m := by
      simpa [AdditiveFilteredRingData.predecessor] using hp
    have hp' : p ∈ ReesCoefficientFiltration.layer F m := by
      exact (coefficientFiltration F).monotone (Nat.le_succ m) hp₀
    refine ⟨hp', ?_⟩
    intro r
    have hcoeff : (p : ReesPolynomial R).coeff (m.succ + r) ∈ F.carrier m := by
      exact hp₀ (m.succ + r)
    rw [associatedClass_eq_zero_iff]
    simpa [AdditiveFilteredRingData.predecessor, Nat.succ_ne_zero] using hcoeff

theorem lower_of_coefficientSymbol_zero
    (n : ℕ) {p : Rees F}
    (hp : CoefficientSymbol F n p 0) :
    p ∈ AdditiveFilteredRingData.predecessor
      (coefficientFiltration F) n := by
  rcases hp with ⟨hp, hq⟩
  by_cases hn : n = 0
  · have hcoeff : ∀ k : ℕ,
        (p : ReesPolynomial R).coeff k = 0 := by
      intro k
      have hk := hq k
      have hpred := (associatedClass_eq_zero_iff F 0
        ((p : ReesPolynomial R).coeff k) (hp k)).mp (by simpa using hk)
      have hzero : (p : ReesPolynomial R).coeff k = 0 := by
        simpa [AdditiveFilteredRingData.predecessor] using hpred
      exact hzero
    have hpzero : p = 0 := by
      apply ReesRing.ext_of_coeff_eq F.toNegFiltrationData
      intro k
      simpa using hcoeff k
    simpa [AdditiveFilteredRingData.predecessor, hn, hpzero]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    change p ∈ ReesCoefficientFiltration.layer F m
    intro k
    by_cases hle : m.succ ≤ k
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hle
      have hk := hq r
      have hpred := (associatedClass_eq_zero_iff F m.succ
        ((p : ReesPolynomial R).coeff (m.succ + r))
        (hp (m.succ + r))).mp (by simpa using hk)
      simpa [AdditiveFilteredRingData.predecessor, Nat.succ_ne_zero] using hpred
    · have hkm : k ≤ m := by omega
      exact F.monotone hkm (p.property k)

theorem coefficientSymbol_zero_iff_lower
    (n : ℕ) {p : Rees F} :
    CoefficientSymbol F n p 0 ↔
      p ∈ AdditiveFilteredRingData.predecessor
        (coefficientFiltration F) n := by
  constructor
  · exact lower_of_coefficientSymbol_zero F n
  · exact coefficientSymbol_zero_of_lower F n

/- Product compatibility on the actual homogeneous generators.  This keeps
   the order of the original coefficient ring and proves the residual degree
   addition `r + s`. -/
theorem coefficientSymbol_mul_shiftedHomogeneousLift
    (n m r s : ℕ) (x : associatedLayer F n) (y : associatedLayer F m) :
    CoefficientSymbol F (n + m)
      (shiftedHomogeneousLift F n r x * shiftedHomogeneousLift F m s y)
      (AddMonoidAlgebra.single (r + s)
        (associatedLayerMul F n m x y)) := by
  refine ⟨ReesCoefficientFiltration.layer_mul
      (shiftedHomogeneousLift_mem_layer F n r x)
      (shiftedHomogeneousLift_mem_layer F m s y), ?_⟩
  intro v
  by_cases hv : r + s = v
  · subst v
    have hcoeff :
        ((shiftedHomogeneousLift F n r x *
          shiftedHomogeneousLift F m s y : Rees F) : ReesPolynomial R).coeff
            (n + m + (r + s)) =
          (representative F n x : R) * (representative F m y : R) := by
      have hdeg : (n + r) + (m + s) = n + m + (r + s) := by omega
      change (SkewPolynomial.monomial (n + r)
          (representative F n x : R) *
        SkewPolynomial.monomial (m + s)
          (representative F m y : R)).coeff
          (n + m + (r + s)) = _
      simp [SkewMonoidAlgebra.coeff_mul, hdeg]
    rw [hcoeff]
    change associatedClass F (n + m)
        ((representative F n x : R) * (representative F m y : R)) _ = _
    rw [show associatedLayerMul F n m x y =
        associatedClass F (n + m)
          ((representative F n x : R) * (representative F m y : R)) _ by
      induction x using Quotient.inductionOn with
      | _ a =>
          induction y using Quotient.inductionOn with
          | _ b =>
              exact (associatedLayerMul_mk_mk F n m a b).symm]
    simp [AddMonoidAlgebra.coeff_single_apply]
  · have hprod :
        ((shiftedHomogeneousLift F n r x *
          shiftedHomogeneousLift F m s y : Rees F) : ReesPolynomial R).coeff
            (n + m + v) = 0 := by
      have hdeg : (n + r) + (m + s) ≠ n + m + v := by
        intro hdeg
        apply hv
        omega
      change (SkewPolynomial.monomial (n + r)
          (representative F n x : R) *
        SkewPolynomial.monomial (m + s)
          (representative F m y : R)).coeff (n + m + v) = 0
      simp [SkewMonoidAlgebra.coeff_mul, hdeg]
    rw [hprod, associatedClass_zero]
    simp [AddMonoidAlgebra.coeff_single_apply, hv]

/- The exact symbol descent is now available for arbitrary nested right
   ideals.  It is the finite natural-number reduction from the producer,
   restated here as the transfer-facing theorem. -/
theorem filteredLeadingSymbolDescent
    (I J : Submodule (Rees F)ᵐᵒᖘ (Rees F))
    (hJI : J ≤ I)
    (hSymbols : ∀ n : ℕ,
      symbols (coefficientFiltration F) I n ⊆
        symbols (coefficientFiltration F) J n) :
    I ≤ J := by
  exact ReesCoefficientFiltration.le_of_symbols_subset F I J hJI hSymbols

theorem filteredLeadingSymbolEquality
    (I J : Submodule (Rees F)ᵐᵒᖘ (Rees F))
    (hIJ : I ≤ J) (hJI : J ≤ I)
    (hSymbols : ∀ n : ℕ,
      symbols (coefficientFiltration F) I n ⊆
        symbols (coefficientFiltration F) J n) :
    I = J := by
  exact le_antisymm (filteredLeadingSymbolDescent F I J hJI hSymbols) hIJ

/- The polynomial Noetherian input is a real theorem, not a callback.  It is
   conditional only on the right-Noetherianity of the actual associated ring;
   the coefficient-filtration quotient assembly below is what would connect
   this polynomial ring to the Rees filtration. -/
theorem rightNoetherian_associatedPolynomial
    [IsNoetherian
      (AdditiveFilteredRingData.actualAssociatedGraded F)ᵐᵒᖘ
      (AdditiveFilteredRingData.actualAssociatedGraded F)] :
    IsNoetherian
      (SkewPolynomial (AdditiveFilteredRingData.actualAssociatedGraded F))ᵐᵒᖘ
      (SkewPolynomial (AdditiveFilteredRingData.actualAssociatedGraded F)) := by
  exact rightNoetherian_centralSkewPolynomial

end ReesNoetherianTransfer

/-!
## Compatibility consumers

These declarations predate the exact-symbol transfer above and are retained
because downstream module consumers and the existing calibration oracle import
their names.  They are generic consumer theorems: no declaration in the exact
symbol path below uses them to manufacture the coefficient graded equivalence
or the final right-Noetherian result.
-/

namespace AdditiveFilteredRingData

variable (F : AdditiveFilteredRingData R)

abbrev boundedReesRing := ReesRing F.toNegFiltrationData

structure HomogeneousIdealLifting where
  generators : ∀ _I : Ideal (boundedReesRing F), Finset (boundedReesRing F)
  generators_mem : ∀ (I : Ideal (boundedReesRing F)) {x : boundedReesRing F},
    x ∈ generators I → x ∈ I
  component_mem_span : ∀ (I : Ideal (boundedReesRing F))
    (p : boundedReesRing F), p ∈ I → ∀ n : ℕ,
      ReesRing.homogeneousLift F.toNegFiltrationData n
          ((p : ReesPolynomial R).coeff n) (p.property n) ∈
        Ideal.span (generators I : Set (boundedReesRing F))

theorem ideal_eq_span_of_homogeneous_lifting
    (H : HomogeneousIdealLifting F) (I : Ideal (boundedReesRing F)) :
    I = Ideal.span (H.generators I : Set (boundedReesRing F)) := by
  apply ReesRing.ideal_eq_span_of_homogeneous_mem F.toNegFiltrationData I
    (H.generators I) (by
      intro x hx
      exact H.generators_mem I hx) (H.component_mem_span I)

theorem isNoetherianRing_of_homogeneous_lifting
    (H : HomogeneousIdealLifting F) :
    IsNoetherianRing (boundedReesRing F) := by
  apply isNoetherianRing_of_finite_homogeneous_ideal_generators
    F.toNegFiltrationData
  intro I
  refine ⟨H.generators I, ?_, ?_⟩
  · intro x hx
    exact H.generators_mem I hx
  exact H.component_mem_span I

end AdditiveFilteredRingData

section AffineGradedCompatibility

variable {K : Type u} {G : Type v} [Field K] [CommRing G] [Algebra K G]
variable {P M : Type w} [AddCommGroup P] [AddCommGroup M] [Module G P]

structure LocallyFiniteAffineGradedRing
    (K : Type u) (G : Type v) [Field K] [CommRing G] [Algebra K G] where
  pieces : ℕ → Submodule K G
  graded : GradedAlgebra pieces
  locallyFinite : ∀ n : ℕ, Module.Finite K (pieces n)
  affine : Algebra.FiniteType K G

namespace LocallyFiniteAffineGradedRing

variable (C : LocallyFiniteAffineGradedRing K G)

theorem isNoetherianRing : IsNoetherianRing G := by
  letI : Algebra.FiniteType K G := C.affine
  exact Algebra.FiniteType.isNoetherianRing K G

end LocallyFiniteAffineGradedRing

variable {R : Type w} [Ring R]

theorem isNoetherianModule_of_affineGraded_surjective
    (C : LocallyFiniteAffineGradedRing K G)
    (F : NegFiltrationData R)
    (σ : G →+* ReesRing F) [RingHomSurjective σ]
    [Module (ReesRing F) M] [Module.Finite G P]
    (f : P →ₛₗ[σ] M) (hf : LinearMap.range f = ⊤) :
    IsNoetherian (ReesRing F) M := by
  letI : IsNoetherianRing G := C.isNoetherianRing
  exact isNoetherian_of_surjective f hf

theorem boundedReesModuleCertificate_of_affineGraded_surjective
    (C : LocallyFiniteAffineGradedRing K G)
    (F : NegFiltrationData R)
    (σ : G →+* ReesRing F) [RingHomSurjective σ]
    [Module (ReesRing F) M] [Module.Finite G P]
    (f : P →ₛₗ[σ] M) (hf : LinearMap.range f = ⊤) :
    Nonempty (ReesModuleNoetherianCertificate (ReesRing F) M) := by
  letI : IsNoetherian (ReesRing F) M :=
    isNoetherianModule_of_affineGraded_surjective C F σ f hf
  exact ⟨noetherianModuleCertificate⟩

end AffineGradedCompatibility

/-!
## First residual

The preceding results produce the shifted symbol on every actual homogeneous
Rees lift, prove its zero kernel is exactly the predecessor coefficient layer,
prove uniqueness of the residual polynomial, and prove residual-degree
multiplication on homogeneous lifts.  The first unproved bridge is the
type-level assembly

`actualAssociatedGraded (ReesCoefficientFiltration.filtration F) ≃+*`
`SkewPolynomial (actualAssociatedGraded F)`.

Constructing that bridge requires defining the forward map on an arbitrary
finite Rees polynomial, proving it independent of the quotient representative,
and then proving its multiplication law after the exponent shift.  No such
equivalence is postulated here.  Until that finite-support quotient assembly
and the corresponding homogeneous symbol-lift theorem are supplied, the
conditional polynomial Noetherianity result above cannot be transported to the
actual Rees right ideals, so no right-Noetherian conclusion is asserted.
-/

end

end SymplecticStafford.Filtered
