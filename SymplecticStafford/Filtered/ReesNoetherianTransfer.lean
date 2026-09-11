import SymplecticStafford.Filtered.ReesNoetherianProducer
import SymplecticStafford.Filtered.RightPolynomialNoetherian
import SymplecticStafford.Filtered.BoundedReesBridge
import SymplecticStafford.Filtered.ReesGoodSubquotient
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.ToDirectSum
import Mathlib.LinearAlgebra.Quotient.Basic

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
open scoped DirectSum

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
    (q : ℕ →₀ associatedLayer F n) : Prop :=
  ∃ hp : p ∈ ReesCoefficientFiltration.layer F n, ∀ r : ℕ,
    associatedClass F n
      ((p : ReesPolynomial R).coeff (n + r)) (hp (n + r)) =
      q r

/- The coefficient symbol attached to a bounded representative.  Its support
   is finite because it is contained in the image, under subtraction by `n`,
   of the support of the original Rees polynomial. -/
noncomputable def coefficientSymbolPolynomial
    (n : ℕ) (p : Rees F)
    (hp : p ∈ ReesCoefficientFiltration.layer F n) :
    ℕ →₀ associatedLayer F n :=
  Finsupp.onFinset
    ((SkewPolynomial.support (p : ReesPolynomial R)).image (fun k => k - n))
    (fun r => associatedClass F n
      ((p : ReesPolynomial R).coeff (n + r)) (hp (n + r)))
    (by
      intro r hr
      simp only [Finset.mem_image]
      refine ⟨n + r, ?_, by omega⟩
      by_contra hcoeff
      apply hr
      have hz : (p : ReesPolynomial R).coeff (n + r) = 0 :=
        SkewPolynomial.notMem_support_iff.mp hcoeff
      rw [associatedClass_eq_zero_iff]
      rw [hz]
      exact (predecessor F n).zero_mem)

@[simp] theorem coefficientSymbolPolynomial_coeff
    (n : ℕ) (p : Rees F)
    (hp : p ∈ ReesCoefficientFiltration.layer F n) (r : ℕ) :
    coefficientSymbolPolynomial F n p hp r =
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
    {q₁ q₂ : ℕ →₀ associatedLayer F n}
    (h₁ : CoefficientSymbol F n p₁ q₁)
    (h₂ : CoefficientSymbol F n p₂ q₂) :
    CoefficientSymbol F n (p₁ + p₂) (q₁ + q₂) := by
  rcases h₁ with ⟨hp₁, hq₁⟩
  rcases h₂ with ⟨hp₂, hq₂⟩
  let hpadd := (ReesCoefficientFiltration.layer F n).add_mem hp₁ hp₂
  refine ⟨hpadd, ?_⟩
  intro r
  calc
    associatedClass F n
        (((p₁ + p₂ : Rees F) : ReesPolynomial R).coeff (n + r))
          (hpadd (n + r)) =
      associatedClass F n
        ((p₁ : ReesPolynomial R).coeff (n + r) +
          (p₂ : ReesPolynomial R).coeff (n + r))
          ((F.carrier n).add_mem (hp₁ (n + r)) (hp₂ (n + r))) := by
            change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
            congr 1
            exact Subtype.ext (SkewPolynomial.coeff_add
              (p₁ : ReesPolynomial R) (p₂ : ReesPolynomial R) (n + r))
    _ = associatedClass F n ((p₁ : ReesPolynomial R).coeff (n + r)) (hp₁ (n + r)) +
        associatedClass F n ((p₂ : ReesPolynomial R).coeff (n + r)) (hp₂ (n + r)) := by
          exact Submodule.Quotient.mk_add
            (x := ⟨(p₁ : ReesPolynomial R).coeff (n + r), hp₁ (n + r)⟩)
            (y := ⟨(p₂ : ReesPolynomial R).coeff (n + r), hp₂ (n + r)⟩)
            (layerSubmodule F n)
    _ = q₁ r + q₂ r := congrArg₂ (· + ·) (hq₁ r) (hq₂ r)

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
  simp [h.symm]

/- The exact symbol of a shifted homogeneous lift is the corresponding
   additive monomial.  This is the basic coefficient-level surjectivity
   calculation used by the eventual graded assembly. -/
theorem coefficientSymbol_shiftedHomogeneousLift
    (n r : ℕ) (x : associatedLayer F n) :
    CoefficientSymbol F n (shiftedHomogeneousLift F n r x)
      (Finsupp.single r x) := by
  refine ⟨shiftedHomogeneousLift_mem_layer F n r x, ?_⟩
  intro s
  by_cases hrs : r = s
  · subst s
    simp only [shiftedHomogeneousLift_coeff]
    change associatedClass F n (representative F n x) _ =
      Finsupp.single r x r
    simpa using associatedClass_representative F n x
  · have hdeg : n + r ≠ n + s := by
      intro hdeg
      apply hrs
      omega
    simp only [shiftedHomogeneousLift_coeff_ne F n r (n + s) x hdeg.symm]
    change associatedClass F n 0 _ = Finsupp.single r x s
    simp [associatedClass_zero, Finsupp.single_apply, hrs]

/- The residual-exponent symbol is unique.  This is a genuine injectivity
   statement for the coefficient-symbol relation, independent of any chosen
   quotient representative. -/
theorem coefficientSymbol_unique
    (n : ℕ) {p : Rees F}
    {q₁ q₂ : ℕ →₀ associatedLayer F n}
    (h₁ : CoefficientSymbol F n p q₁)
    (h₂ : CoefficientSymbol F n p q₂) : q₁ = q₂ := by
  rcases h₁ with ⟨hp₁, hq₁⟩
  rcases h₂ with ⟨hp₂, hq₂⟩
  ext r
  rw [← hq₁ r, ← hq₂ r]

/- A zero symbol is exactly the lower coefficient layer.  The forward
   direction is the one needed for descent; the reverse direction records
   the kernel calculation that would make the quotient map faithful. -/
theorem coefficientSymbol_zero_of_lower
    (n : ℕ) {p : Rees F}
    (hp : p ∈ AdditiveFilteredRingData.predecessor
      (coefficientFiltration F) n) :
    CoefficientSymbol F n p 0 := by
  by_cases hn : n = 0
  · subst n
    have hp0 : p = 0 := by
      simpa [AdditiveFilteredRingData.predecessor] using hp
    subst p
    exact coefficientSymbol_zero F 0
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hp₀ : p ∈ (coefficientFiltration F).carrier m := by
      simpa [AdditiveFilteredRingData.predecessor] using hp
    have hp' : p ∈ ReesCoefficientFiltration.layer F m.succ := by
      exact (coefficientFiltration F).monotone (Nat.le_succ m) hp₀
    refine ⟨hp', ?_⟩
    intro r
    have hcoeff : (p : ReesPolynomial R).coeff (m.succ + r) ∈ F.carrier m := by
      exact hp₀ (m.succ + r)
    change associatedClass F m.succ _ _ = 0
    rw [associatedClass_eq_zero_iff]
    simpa [AdditiveFilteredRingData.predecessor, Nat.succ_ne_zero] using hcoeff

theorem lower_of_coefficientSymbol_zero
    (n : ℕ) {p : Rees F}
    (hp : CoefficientSymbol F n p 0) :
    p ∈ AdditiveFilteredRingData.predecessor
      (coefficientFiltration F) n := by
  rcases hp with ⟨hp, hq⟩
  by_cases hn : n = 0
  · subst n
    have hcoeff : ∀ k : ℕ,
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
    simpa [AdditiveFilteredRingData.predecessor, hpzero]
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
      (Finsupp.single (r + s)
        (associatedLayerMul F n m x y)) := by
  refine ⟨ReesCoefficientFiltration.layer_mul
      F
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
      rw [SkewPolynomial.monomial_mul_monomial]
      rw [SkewPolynomial.coeff_monomial]
      simp only [if_pos hdeg]
      rw [SkewPolynomial.φ_iterate_apply]
      rfl
    change Submodule.Quotient.mk _ = _
    have hsub :
        (⟨((shiftedHomogeneousLift F n r x * shiftedHomogeneousLift F m s y :
            Rees F) : ReesPolynomial R).coeff (n + m + (r + s)),
          (ReesCoefficientFiltration.layer_mul F
            (shiftedHomogeneousLift_mem_layer F n r x)
            (shiftedHomogeneousLift_mem_layer F m s y)) (n + m + (r + s))⟩ :
          F.carrier (n + m)) =
        ⟨(representative F n x : R) * (representative F m y : R),
          F.mul_mem (representative F n x).property
            (representative F m y).property⟩ := by
      ext
      exact hcoeff
    rw [hsub]
    rw [show associatedLayerMul F n m x y =
        associatedClass F (n + m)
          ((representative F n x : R) * (representative F m y : R))
            (F.mul_mem (representative F n x).property
              (representative F m y).property) by
      calc
        associatedLayerMul F n m x y =
            associatedLayerMul F n m
              (associatedClass F n (representative F n x) (representative F n x).property)
              (associatedClass F m (representative F m y) (representative F m y).property) := by
                rw [associatedClass_representative, associatedClass_representative]
        _ = _ := associatedLayerMul_mk_mk F n m
          (representative F n x) (representative F m y)]
    simp only [Finsupp.single_eq_same]
    rfl
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
      rw [SkewPolynomial.monomial_mul_monomial]
      rw [SkewPolynomial.coeff_monomial]
      simp only [if_neg hdeg]
    change Submodule.Quotient.mk _ = _
    have hsub :
        (⟨((shiftedHomogeneousLift F n r x * shiftedHomogeneousLift F m s y :
            Rees F) : ReesPolynomial R).coeff (n + m + v),
          (ReesCoefficientFiltration.layer_mul F
            (shiftedHomogeneousLift_mem_layer F n r x)
            (shiftedHomogeneousLift_mem_layer F m s y)) (n + m + v)⟩ :
          F.carrier (n + m)) = 0 := by
      ext
      exact hprod
    rw [hsub]
    change associatedClass F (n + m) 0 _ = _
    simp [associatedClass_zero, Finsupp.single_apply, hv]

/- The coefficient formula is additive before passing to the quotient. -/
noncomputable def coefficientLayerAddHom (n : ℕ) :
    (coefficientFiltration F).carrier n →+
      (ℕ →₀ associatedLayer F n) where
  toFun p := coefficientSymbolPolynomial F n p.1 p.2
  map_zero' := by
    ext r
    simp [coefficientSymbolPolynomial_coeff, associatedClass_zero]
  map_add' p q := by
    apply coefficientSymbol_unique F n
    · exact coefficientSymbol_exists F n _ _
    · exact coefficientSymbol_add F n
        (coefficientSymbol_exists F n p.1 p.2)
        (coefficientSymbol_exists F n q.1 q.2)

/- The preceding layer is precisely the kernel, so the formula descends to
the actual quotient used in the associated graded ring. -/
noncomputable def degreeSymbolLinearMap (n : ℕ) :
    associatedLayer (coefficientFiltration F) n →ₗ[ℤ]
      (ℕ →₀ associatedLayer F n) :=
  (layerSubmodule (coefficientFiltration F) n).liftQ
    (coefficientLayerAddHom F n).toIntLinearMap (by
      intro p hp
      change coefficientSymbolPolynomial F n p.1 p.2 = 0
      apply coefficientSymbol_unique F n
      · exact coefficientSymbol_exists F n p.1 p.2
      · exact coefficientSymbol_zero_of_lower F n hp)

@[simp] theorem degreeSymbolLinearMap_mk (n : ℕ)
    (p : (coefficientFiltration F).carrier n) :
    degreeSymbolLinearMap F n (Submodule.Quotient.mk p) =
      coefficientSymbolPolynomial F n p.1 p.2 := rfl

theorem degreeSymbolLinearMap_injective (n : ℕ) :
    Function.Injective (degreeSymbolLinearMap F n) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : degreeSymbolLinearMap F n (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  let z := x - y
  change z = 0
  have hz' : degreeSymbolLinearMap F n z = 0 := by simpa [z] using hz
  revert hz'
  induction z using Quotient.inductionOn with
  | _ p =>
      intro hz'
      change coefficientSymbolPolynomial F n p.1 p.2 = 0 at hz'
      have hs := coefficientSymbol_exists F n p.1 p.2
      rw [hz'] at hs
      exact (Submodule.Quotient.mk_eq_zero
        (layerSubmodule (coefficientFiltration F) n)).2
          (lower_of_coefficientSymbol_zero F n hs)

theorem degreeSymbolLinearMap_surjective (n : ℕ) :
    Function.Surjective (degreeSymbolLinearMap F n) := by
  intro q
  induction q using Finsupp.induction with
  | zero => exact ⟨0, map_zero _⟩
  | @single_add r x q _ _ ih =>
      obtain ⟨z, hz⟩ := ih
      let p : (coefficientFiltration F).carrier n :=
        ⟨shiftedHomogeneousLift F n r x,
          shiftedHomogeneousLift_mem_layer F n r x⟩
      refine ⟨Submodule.Quotient.mk p + z, ?_⟩
      rw [map_add, hz, degreeSymbolLinearMap_mk]
      have hs := coefficientSymbol_shiftedHomogeneousLift F n r x
      exact congrArg (fun a => a + q)
        (coefficientSymbol_unique F n
          (coefficientSymbol_exists F n p.1 p.2) hs)

/- Exact degreewise quotient-symbol equivalence. -/
noncomputable def degreeSymbolEquiv (n : ℕ) :
    associatedLayer (coefficientFiltration F) n ≃ₗ[ℤ]
      (ℕ →₀ associatedLayer F n) :=
  LinearEquiv.ofBijective (degreeSymbolLinearMap F n)
    ⟨degreeSymbolLinearMap_injective F n,
      degreeSymbolLinearMap_surjective F n⟩

/- Multiplication in coefficient degree is heterogeneous convolution.  The
coefficient of residual degree `r+s` lies in associated degree `n+m`, so no
individual coefficient layer is incorrectly asked to carry a ring. -/
noncomputable def coefficientConvolution (n m : ℕ)
    (p : ℕ →₀ associatedLayer F n) (q : ℕ →₀ associatedLayer F m) :
    ℕ →₀ associatedLayer F (n + m) :=
  p.sum fun r x => q.sum fun s y =>
    Finsupp.single (r + s) (associatedLayerMul F n m x y)

@[simp] theorem coefficientConvolution_single_single
    (n m r s : ℕ) (x : associatedLayer F n) (y : associatedLayer F m) :
    coefficientConvolution F n m (Finsupp.single r x) (Finsupp.single s y) =
      Finsupp.single (r + s) (associatedLayerMul F n m x y) := by
  simp [coefficientConvolution, associatedLayerMul_zero_left,
    associatedLayerMul_zero_right]

@[simp] theorem coefficientConvolution_zero_left
    (n m : ℕ) (q : ℕ →₀ associatedLayer F m) :
    coefficientConvolution F n m 0 q = 0 := by
  simp [coefficientConvolution]

@[simp] theorem coefficientConvolution_zero_right
    (n m : ℕ) (p : ℕ →₀ associatedLayer F n) :
    coefficientConvolution F n m p 0 = 0 := by
  simp [coefficientConvolution]

@[simp] theorem coefficientConvolution_add_left
    (n m : ℕ) (p p' : ℕ →₀ associatedLayer F n)
    (q : ℕ →₀ associatedLayer F m) :
    coefficientConvolution F n m (p + p') q =
      coefficientConvolution F n m p q + coefficientConvolution F n m p' q := by
  unfold coefficientConvolution
  apply Finsupp.sum_add_index'
  · intro r
    simp [associatedLayerMul_zero_left]
  · intro r x x'
    simp [associatedLayerMul_add_left, Finsupp.single_add]

@[simp] theorem coefficientConvolution_add_right
    (n m : ℕ) (p : ℕ →₀ associatedLayer F n)
    (q q' : ℕ →₀ associatedLayer F m) :
    coefficientConvolution F n m p (q + q') =
      coefficientConvolution F n m p q + coefficientConvolution F n m p q' := by
  unfold coefficientConvolution
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro r hr
  apply Finsupp.sum_add_index'
  · intro s
    simp [associatedLayerMul_zero_right]
  · intro s y y'
    simp [associatedLayerMul_add_right, Finsupp.single_add]

private def sigmaFinsuppSingle (r : ℕ) :
    (Σ n : ℕ, associatedLayer F n) → (Σ n : ℕ, ℕ →₀ associatedLayer F n)
  | ⟨n, x⟩ => ⟨n, Finsupp.single r x⟩

private theorem coefficientZeroHEq {i j : ℕ} (h : i = j) :
    (0 : ℕ →₀ associatedLayer F i) ≍ (0 : ℕ →₀ associatedLayer F j) := by
  subst j
  rfl

private theorem coefficientAddHEq {i j : ℕ} (h : i = j)
    {a c : ℕ →₀ associatedLayer F i} {b d : ℕ →₀ associatedLayer F j}
    (hab : a ≍ b) (hcd : c ≍ d) :
    a + c ≍ b + d := by
  subst j
  exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq hab) (eq_of_heq hcd))

private theorem coefficientConvolution_one_left (n : ℕ)
    (p : ℕ →₀ associatedLayer F n) :
    HEq (coefficientConvolution F 0 n
      (Finsupp.single 0 (associatedOne F)) p) p := by
  induction p using Finsupp.induction with
  | zero => simpa using coefficientZeroHEq F (Nat.zero_add n)
  | @single_add r x p _ _ ih =>
      have h := congrArg (sigmaFinsuppSingle F r)
        (associatedLayerMul_one_left F n x)
      have hs := (Sigma.mk.inj_iff.mp h).2
      simpa [coefficientConvolution_add_right,
        coefficientConvolution_single_single] using
        coefficientAddHEq F (Nat.zero_add n) hs ih

private theorem coefficientConvolution_one_right (n : ℕ)
    (p : ℕ →₀ associatedLayer F n) :
    HEq (coefficientConvolution F n 0 p
      (Finsupp.single 0 (associatedOne F))) p := by
  induction p using Finsupp.induction with
  | zero => exact coefficientZeroHEq F (Nat.add_zero n)
  | @single_add r x p _ _ ih =>
      have h := congrArg (sigmaFinsuppSingle F r)
        (associatedLayerMul_one_right F n x)
      have hs := (Sigma.mk.inj_iff.mp h).2
      simpa [coefficientConvolution_add_left,
        coefficientConvolution_single_single] using
        coefficientAddHEq F (Nat.add_zero n) hs ih

private theorem coefficientConvolution_assoc_single_single (i j k r s : ℕ)
    (x : associatedLayer F i) (y : associatedLayer F j)
    (t : ℕ →₀ associatedLayer F k) :
    HEq (coefficientConvolution F (i + j) k
        (coefficientConvolution F i j (Finsupp.single r x) (Finsupp.single s y)) t)
      (coefficientConvolution F i (j + k) (Finsupp.single r x)
        (coefficientConvolution F j k (Finsupp.single s y) t)) := by
  induction t using Finsupp.induction with
  | zero => simpa using coefficientZeroHEq F (Nat.add_assoc i j k)
  | @single_add v z t _ _ ih =>
      have h := congrArg (sigmaFinsuppSingle F (r + s + v))
        (associatedLayerMul_assoc F i j k x y z)
      have hs := (Sigma.mk.inj_iff.mp h).2
      simpa [coefficientConvolution_add_right,
        coefficientConvolution_single_single, Nat.add_assoc] using
        coefficientAddHEq F (Nat.add_assoc i j k) hs ih

private theorem coefficientConvolution_assoc_single (i j k r : ℕ)
    (x : associatedLayer F i) (q : ℕ →₀ associatedLayer F j)
    (t : ℕ →₀ associatedLayer F k) :
    HEq (coefficientConvolution F (i + j) k
        (coefficientConvolution F i j (Finsupp.single r x) q) t)
      (coefficientConvolution F i (j + k) (Finsupp.single r x)
        (coefficientConvolution F j k q t)) := by
  induction q using Finsupp.induction with
  | zero => simpa using coefficientZeroHEq F (Nat.add_assoc i j k)
  | @single_add s y q _ _ ih =>
      simpa [coefficientConvolution_add_left,
        coefficientConvolution_add_right] using
        coefficientAddHEq F (Nat.add_assoc i j k)
          (coefficientConvolution_assoc_single_single F i j k r s x y t) ih

private theorem coefficientConvolution_assoc (i j k : ℕ)
    (p : ℕ →₀ associatedLayer F i) (q : ℕ →₀ associatedLayer F j)
    (t : ℕ →₀ associatedLayer F k) :
    HEq (coefficientConvolution F (i + j) k
        (coefficientConvolution F i j p q) t)
      (coefficientConvolution F i (j + k) p
        (coefficientConvolution F j k q t)) := by
  induction p using Finsupp.induction with
  | zero => exact coefficientZeroHEq F (Nat.add_assoc i j k)
  | @single_add r x p _ _ ih =>
      simpa [coefficientConvolution_add_left] using
        coefficientAddHEq F (Nat.add_assoc i j k)
          (coefficientConvolution_assoc_single F i j k r x q t) ih

instance coefficientPolynomialLayersGOne :
    GradedMonoid.GOne (fun n : ℕ => ℕ →₀ associatedLayer F n) where
  one := Finsupp.single 0 (associatedOne F)

instance coefficientPolynomialLayersGMul :
    GradedMonoid.GMul (fun n : ℕ => ℕ →₀ associatedLayer F n) where
  mul := fun {n m} => coefficientConvolution F n m

instance coefficientPolynomialLayersGRing :
    DirectSum.GRing (fun n : ℕ => ℕ →₀ associatedLayer F n) where
  mul := fun {n m} => coefficientConvolution F n m
  mul_zero := fun p => coefficientConvolution_zero_right F _ _ p
  zero_mul := fun q => coefficientConvolution_zero_left F _ _ q
  mul_add := fun p q q' => coefficientConvolution_add_right F _ _ p q q'
  add_mul := fun p p' q => coefficientConvolution_add_left F _ _ p p' q
  one := Finsupp.single 0 (associatedOne F)
  one_mul := by
    intro p
    cases p with
    | mk n p => exact Sigma.ext (Nat.zero_add n) (coefficientConvolution_one_left F n p)
  mul_one := by
    intro p
    cases p with
    | mk n p =>
        exact Sigma.ext (Nat.add_zero n) (coefficientConvolution_one_right F n p)
  mul_assoc := by
    intro p q t
    cases p with
    | mk i p =>
      cases q with
      | mk j q =>
        cases t with
        | mk k t =>
          apply Sigma.ext (Nat.add_assoc i j k)
          exact coefficientConvolution_assoc F i j k p q t
  natCast := fun a => a • Finsupp.single 0 (associatedOne F)
  natCast_zero := by simp
  natCast_succ := by intro a; rw [add_nsmul]; simp [add_comm]
  intCast := fun a => a • Finsupp.single 0 (associatedOne F)
  intCast_ofNat := by intro a; simp
  intCast_negSucc_ofNat := by
    intro a
    exact negSucc_zsmul (Finsupp.single 0 (associatedOne F)) a

noncomputable instance coefficientPolynomialGradedRing :
    Ring (DirectSum ℕ (fun n => ℕ →₀ associatedLayer F n)) := by
  infer_instance

abbrev coefficientPolynomialGraded :=
  DirectSum ℕ (fun n => ℕ →₀ associatedLayer F n)

noncomputable def coefficientGradedDegreeEquiv :
    coefficientAssociatedGraded F ≃+ coefficientPolynomialGraded F :=
  DFinsupp.mapRange.addEquiv fun n => (degreeSymbolEquiv F n).toAddEquiv

@[simp] private theorem coefficientGradedDegreeEquiv_of
    (n : ℕ) (x : associatedLayer (coefficientFiltration F) n) :
    coefficientGradedDegreeEquiv F
        (DirectSum.of (fun n : ℕ => associatedLayer (coefficientFiltration F) n) n x) =
      DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) n
        (degreeSymbolLinearMap F n x) := by
  classical
  apply DFinsupp.ext
  intro k
  change degreeSymbolLinearMap F k
      ((DirectSum.of
        (fun n : ℕ => associatedLayer (coefficientFiltration F) n) n x) k) =
    (DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) n
      (degreeSymbolLinearMap F n x)) k
  by_cases h : n = k
  · subst k
    simp [DirectSum.of_apply]
  · simp [DirectSum.of_apply, h]

private theorem degreeSymbol_mul_single
    (n m r s : ℕ) (x : associatedLayer F n) (y : associatedLayer F m) :
    degreeSymbolLinearMap F (n + m)
        (associatedLayerMul (coefficientFiltration F) n m
          (Submodule.Quotient.mk
            ⟨shiftedHomogeneousLift F n r x,
              shiftedHomogeneousLift_mem_layer F n r x⟩)
          (Submodule.Quotient.mk
            ⟨shiftedHomogeneousLift F m s y,
              shiftedHomogeneousLift_mem_layer F m s y⟩)) =
      Finsupp.single (r + s) (associatedLayerMul F n m x y) := by
  let pn : (coefficientFiltration F).carrier n :=
    ⟨shiftedHomogeneousLift F n r x,
      shiftedHomogeneousLift_mem_layer F n r x⟩
  let pm : (coefficientFiltration F).carrier m :=
    ⟨shiftedHomogeneousLift F m s y,
      shiftedHomogeneousLift_mem_layer F m s y⟩
  rw [associatedLayerMul_mk_mk]
  change coefficientSymbolPolynomial F (n + m) (pn.1 * pm.1)
      (ReesCoefficientFiltration.layer_mul F pn.2 pm.2) = _
  apply coefficientSymbol_unique F (n + m)
  · exact coefficientSymbol_exists F (n + m) _ _
  · exact coefficientSymbol_mul_shiftedHomogeneousLift F n m r s x y

private theorem degreeSymbol_mul_left_single
    (n m r : ℕ) (a : associatedLayer F n)
    (y : associatedLayer (coefficientFiltration F) m) :
    let xr : associatedLayer (coefficientFiltration F) n :=
      Submodule.Quotient.mk
        ⟨shiftedHomogeneousLift F n r a,
          shiftedHomogeneousLift_mem_layer F n r a⟩
    degreeSymbolLinearMap F (n + m)
        (associatedLayerMul (coefficientFiltration F) n m xr y) =
      coefficientConvolution F n m (Finsupp.single r a)
        (degreeSymbolLinearMap F m y) := by
  classical
  dsimp
  let em := degreeSymbolLinearMap F m
  have hm := degreeSymbolLinearMap_injective F m
  generalize hqy : em y = qy
  induction qy using Finsupp.induction generalizing y with
  | zero =>
      have hy : y = 0 := hm (by simpa [em] using hqy)
      subst y
      simp [associatedLayerMul_zero_right]
  | @single_add s b q _ _ ih =>
      let ys : associatedLayer (coefficientFiltration F) m :=
        Submodule.Quotient.mk
          ⟨shiftedHomogeneousLift F m s b,
            shiftedHomogeneousLift_mem_layer F m s b⟩
      have hys : em ys = Finsupp.single s b := by
        change degreeSymbolLinearMap F m ys = _
        change coefficientSymbolPolynomial F m (shiftedHomogeneousLift F m s b)
          (shiftedHomogeneousLift_mem_layer F m s b) = _
        apply coefficientSymbol_unique F m
        · exact coefficientSymbol_exists F m _ _
        · exact coefficientSymbol_shiftedHomogeneousLift F m s b
      have hyrest : em (y - ys) = q := by
        rw [map_sub, hqy, hys]
        simp
      have hd : degreeSymbolLinearMap F (n + m)
          (associatedLayerMul (coefficientFiltration F) n m
            (Submodule.Quotient.mk
              ⟨shiftedHomogeneousLift F n r a,
                shiftedHomogeneousLift_mem_layer F n r a⟩) ys) =
          Finsupp.single (r + s) (associatedLayerMul F n m a b) := by
        simpa [ys] using degreeSymbol_mul_single F n m r s a b
      rw [show y = ys + (y - ys) by abel,
        associatedLayerMul_add_right, map_add, hd, ih (y - ys) hyrest]
      simpa only [coefficientConvolution_single_single] using
        (coefficientConvolution_add_right F n m
          (Finsupp.single r a) (Finsupp.single s b) q).symm

theorem degreeSymbol_map_mul
    (n m : ℕ) (x : associatedLayer (coefficientFiltration F) n)
    (y : associatedLayer (coefficientFiltration F) m) :
    degreeSymbolLinearMap F (n + m)
        (associatedLayerMul (coefficientFiltration F) n m x y) =
      coefficientConvolution F n m
        (degreeSymbolLinearMap F n x) (degreeSymbolLinearMap F m y) := by
  classical
  let en := degreeSymbolLinearMap F n
  let em := degreeSymbolLinearMap F m
  let enm := degreeSymbolLinearMap F (n + m)
  have hn := degreeSymbolLinearMap_injective F n
  have hm := degreeSymbolLinearMap_injective F m
  generalize hqx : en x = qx
  induction qx using Finsupp.induction generalizing x with
  | zero =>
      have hx : x = 0 := hn (by simpa [en] using hqx)
      subst x
      simp [associatedLayerMul_zero_left]
  | @single_add r a q _ _ ih =>
      let xr : associatedLayer (coefficientFiltration F) n :=
        Submodule.Quotient.mk
          ⟨shiftedHomogeneousLift F n r a,
            shiftedHomogeneousLift_mem_layer F n r a⟩
      have hxr : en xr = Finsupp.single r a := by
        change degreeSymbolLinearMap F n xr = _
        change coefficientSymbolPolynomial F n (shiftedHomogeneousLift F n r a)
          (shiftedHomogeneousLift_mem_layer F n r a) = _
        apply coefficientSymbol_unique F n
        · exact coefficientSymbol_exists F n _ _
        · exact coefficientSymbol_shiftedHomogeneousLift F n r a
      have hxrest : en (x - xr) = q := by
        rw [map_sub, hqx, hxr]
        simp
      have hix := ih (x - xr) hxrest
      have hsingle := degreeSymbol_mul_left_single F n m r a y
      rw [show x = xr + (x - xr) by abel,
        associatedLayerMul_add_left, map_add, hsingle, hix]
      exact (coefficientConvolution_add_left F n m
        (Finsupp.single r a) q (degreeSymbolLinearMap F m y)).symm

theorem coefficientGradedDegreeEquiv_map_mul
    (a b : coefficientAssociatedGraded F) :
    coefficientGradedDegreeEquiv F (a * b) =
      coefficientGradedDegreeEquiv F a * coefficientGradedDegreeEquiv F b := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp [coefficientGradedDegreeEquiv]
  | of n x =>
      induction b using DirectSum.induction_on with
      | zero => simp [coefficientGradedDegreeEquiv]
      | of m y =>
          rw [AdditiveFilteredRingData.actualAssociatedGraded_of_mul_of]
          rw [coefficientGradedDegreeEquiv_of, coefficientGradedDegreeEquiv_of,
            coefficientGradedDegreeEquiv_of, DirectSum.of_mul_of,
            degreeSymbol_map_mul F n m x y]
          rfl
      | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
  | add x y hx hy => rw [add_mul, map_add, hx, hy, map_add, add_mul]

noncomputable def coefficientGradedRingEquiv :
    coefficientAssociatedGraded F ≃+*
      coefficientPolynomialGraded F :=
  { coefficientGradedDegreeEquiv F with
    map_mul' := coefficientGradedDegreeEquiv_map_mul F }

private def sigmaSwap : (Σ _ : ℕ, ℕ) ≃ (Σ _ : ℕ, ℕ) where
  toFun p := ⟨p.2, p.1⟩
  invFun p := ⟨p.2, p.1⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

private noncomputable def swappedFiberEquiv (k : Σ _ : ℕ, ℕ) :
    associatedLayer F (sigmaSwap.symm k).fst ≃+
      associatedLayer F k.snd := by
  cases k
  rfl

private def innerAssociatedEquiv (_r : ℕ) :
    DirectSum ℕ (fun n => associatedLayer F n) ≃+
      AdditiveFilteredRingData.actualAssociatedGraded F := AddEquiv.refl _

private noncomputable def layerSigmaCurryEquiv :
    DirectSum (Σ _ : ℕ, ℕ) (fun k => associatedLayer F k.snd) ≃+
      DirectSum ℕ (fun _ => DirectSum ℕ (fun n => associatedLayer F n)) :=
  DirectSum.sigmaCurryEquiv (δ := fun (_ : ℕ) n => associatedLayer F n)

private def finsuppPolynomialEquiv :
    (ℕ →₀ AdditiveFilteredRingData.actualAssociatedGraded F) ≃+
      AddMonoidAlgebra (AdditiveFilteredRingData.actualAssociatedGraded F) ℕ :=
  AddMonoidAlgebra.coeffAddEquiv.symm

noncomputable def finiteDirectSumPolynomialEquiv :
    coefficientPolynomialGraded F ≃+
      AddMonoidAlgebra (AdditiveFilteredRingData.actualAssociatedGraded F) ℕ :=
  by
    classical
    exact ((DFinsupp.mapRange.addEquiv (fun _n =>
      (finsuppAddEquivDFinsupp :
        (ℕ →₀ associatedLayer F _n) ≃+
          DirectSum ℕ (fun _ => associatedLayer F _n)))).trans
    ((DirectSum.sigmaCurryEquiv).symm.trans
      ((DirectSum.equivCongrLeft sigmaSwap).trans
        ((DFinsupp.mapRange.addEquiv (swappedFiberEquiv F)).trans
        ((layerSigmaCurryEquiv F).trans
          ((DFinsupp.mapRange.addEquiv (innerAssociatedEquiv F)).trans
          ((finsuppAddEquivDFinsupp :
            (ℕ →₀ AdditiveFilteredRingData.actualAssociatedGraded F) ≃+
              DirectSum ℕ (fun _ =>
                AdditiveFilteredRingData.actualAssociatedGraded F)).symm.trans
              (finsuppPolynomialEquiv F))))))))

@[simp] theorem finiteDirectSumPolynomialEquiv_of_single
    (n r : ℕ) (x : associatedLayer F n) :
    finiteDirectSumPolynomialEquiv F
        (DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) n
          (Finsupp.single r x)) =
      AddMonoidAlgebra.single r
        (DirectSum.of (fun n : ℕ => associatedLayer F n) n x) := by
  classical
  ext s m
  change ((DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) n
    (Finsupp.single r x)) m) s =
      ((Finsupp.single r
        (DirectSum.of (fun n : ℕ => associatedLayer F n) n x)) s) m
  by_cases hnm : n = m
  · subst m
    by_cases hrs : r = s
    · subst s
      simp [DirectSum.of_apply]
    · simp [Finsupp.single_apply, hrs]
  · by_cases hrs : r = s
    · subst s
      simp [DirectSum.of_apply, hnm]
    · simp [DirectSum.of_apply, hnm, hrs]

private theorem finiteDirectSumPolynomialEquiv_single_left
    (n m r : ℕ) (x : associatedLayer F n)
    (q : ℕ →₀ associatedLayer F m) :
    finiteDirectSumPolynomialEquiv F
        (DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) (n + m)
          (coefficientConvolution F n m (Finsupp.single r x) q)) =
      AddMonoidAlgebra.single r
          (DirectSum.of (fun n : ℕ => associatedLayer F n) n x) *
        finiteDirectSumPolynomialEquiv F
          (DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) m q) := by
  induction q using Finsupp.induction with
  | zero => simp [coefficientConvolution_zero_right]
  | @single_add s y q _ _ ih =>
      simp [coefficientConvolution_add_right,
        coefficientConvolution_single_single, ih,
        AddMonoidAlgebra.single_mul_single,
        AdditiveFilteredRingData.actualAssociatedGraded_of_mul_of, mul_add]

private theorem finiteDirectSumPolynomialEquiv_of_mul_of
    (n m : ℕ) (p : ℕ →₀ associatedLayer F n)
    (q : ℕ →₀ associatedLayer F m) :
    finiteDirectSumPolynomialEquiv F
        (DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) (n + m)
          (coefficientConvolution F n m p q)) =
      finiteDirectSumPolynomialEquiv F
          (DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) n p) *
        finiteDirectSumPolynomialEquiv F
          (DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) m q) := by
  classical
  induction p using Finsupp.induction with
  | zero => simp [coefficientConvolution_zero_left]
  | @single_add r x p _ _ ih =>
      simp [coefficientConvolution_add_left, ih,
        finiteDirectSumPolynomialEquiv_single_left F n m r x q, add_mul]

theorem finiteDirectSumPolynomialEquiv_map_mul
    (a b : coefficientPolynomialGraded F) :
    finiteDirectSumPolynomialEquiv F (a * b) =
      finiteDirectSumPolynomialEquiv F a * finiteDirectSumPolynomialEquiv F b := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp [coefficientPolynomialLayersGMul]
  | of n p =>
      induction b using DirectSum.induction_on with
      | zero => simp [coefficientPolynomialLayersGMul]
      | of m q =>
          rw [DirectSum.of_mul_of]
          change finiteDirectSumPolynomialEquiv F
              (DirectSum.of (fun n : ℕ => ℕ →₀ associatedLayer F n) (n + m)
                (coefficientConvolution F n m p q)) = _
          exact finiteDirectSumPolynomialEquiv_of_mul_of F n m p q
      | add x y hx hy => simp [mul_add, map_add, hx, hy]
  | add x y hx hy => simp [add_mul, map_add, hx, hy]

noncomputable def finiteDirectSumPolynomialRingEquiv :
    coefficientPolynomialGraded F ≃+*
      AddMonoidAlgebra (AdditiveFilteredRingData.actualAssociatedGraded F) ℕ :=
  { finiteDirectSumPolynomialEquiv F with
    map_mul' := finiteDirectSumPolynomialEquiv_map_mul F }

private def centralSkewMonoidAlgebraEquiv (A : Type*) [Ring A] :
    SkewMonoidAlgebra A (Multiplicative ℕ) ≃+*
      MonoidAlgebra A (Multiplicative ℕ) :=
  { toFun := fun p => ⟨p.coeff⟩
    invFun := fun p => ⟨p.coeff⟩
    left_inv := by intro p; cases p; rfl
    right_inv := by intro p; cases p; rfl
    map_add' := by intro p q; ext x; simp
    map_mul' := by
      intro p q
      apply MonoidAlgebra.coeff_injective
      ext x
      simp [SkewMonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_mul]
      rfl }

private def addMonoidAlgebraSkewPolynomialEquiv (A : Type*) [Ring A] :
    AddMonoidAlgebra A ℕ ≃+* SkewPolynomial A :=
  ((AddMonoidAlgebra.toMultiplicative A ℕ).trans
    (centralSkewMonoidAlgebraEquiv A).symm)

noncomputable def coefficientGradedPolynomialRingEquiv :
    coefficientAssociatedGraded F ≃+*
      SkewPolynomial (AdditiveFilteredRingData.actualAssociatedGraded F) :=
  (coefficientGradedRingEquiv F).trans
    ((finiteDirectSumPolynomialRingEquiv F).trans
    (addMonoidAlgebraSkewPolynomialEquiv
      (AdditiveFilteredRingData.actualAssociatedGraded F)))

private theorem rightNoetherian_iff_oppositeRing
    (A : Type*) [Ring A] :
    IsNoetherian Aᵐᵒᵖ A ↔ IsNoetherianRing Aᵐᵒᵖ := by
  let e : A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ := MulOpposite.opLinearEquiv Aᵐᵒᵖ
  exact e.isNoetherian_iff

theorem rightNoetherian_coefficientAssociatedGraded
    [IsNoetherian
      (AdditiveFilteredRingData.actualAssociatedGraded F)ᵐᵒᵖ
      (AdditiveFilteredRingData.actualAssociatedGraded F)] :
    IsNoetherian (coefficientAssociatedGraded F)ᵐᵒᵖ
      (coefficientAssociatedGraded F) := by
  letI : IsNoetherian
      (SkewPolynomial (AdditiveFilteredRingData.actualAssociatedGraded F))ᵐᵒᵖ
      (SkewPolynomial (AdditiveFilteredRingData.actualAssociatedGraded F)) :=
    rightNoetherian_centralSkewPolynomial
  letI : IsNoetherianRing
      (SkewPolynomial (AdditiveFilteredRingData.actualAssociatedGraded F))ᵐᵒᵖ :=
    (rightNoetherian_iff_oppositeRing _).mp inferInstance
  letI : IsNoetherianRing (coefficientAssociatedGraded F)ᵐᵒᵖ :=
    isNoetherianRing_of_ringEquiv
      (SkewPolynomial (AdditiveFilteredRingData.actualAssociatedGraded F))ᵐᵒᵖ
      (RingEquiv.op (coefficientGradedPolynomialRingEquiv F)).symm
  exact (rightNoetherian_iff_oppositeRing _).mpr inferInstance

/- The exact symbols form a right ideal without taking an additional span.
The componentwise definition is what makes equality of these ideals give
equality of the actual symbol ranges required by descending reduction. -/
noncomputable def exactSymbolRightIdeal
    (I : Submodule (Rees F)ᵐᵒᵖ (Rees F)) :
    Submodule (coefficientAssociatedGraded F)ᵐᵒᵖ
      (coefficientAssociatedGraded F) where
  carrier := {x | ∀ n, x n ∈ symbols (coefficientFiltration F) I n}
  zero_mem' := by
    intro n
    exact (symbolAddSubgroup (coefficientFiltration F) I n).zero_mem
  add_mem' := by
    intro x y hx hy n
    exact (symbolAddSubgroup (coefficientFiltration F) I n).add_mem (hx n) (hy n)
  smul_mem' := by
    classical
    intro a x hx
    change ∀ n, (x * a.unop) n ∈ symbols (coefficientFiltration F) I n
    intro n
    rw [DirectSum.mul_eq_dfinsuppSum]
    simp only [DFinsupp.sum_apply, DFinsupp.sum]
    change _ ∈ symbolAddSubgroup (coefficientFiltration F) I n
    rw [DFinsupp.finsetSum_apply]
    apply (symbolAddSubgroup (coefficientFiltration F) I n).toAddSubmonoid.sum_mem
    intro i hi
    rw [DFinsupp.finsetSum_apply]
    apply (symbolAddSubgroup (coefficientFiltration F) I n).toAddSubmonoid.sum_mem
    intro j hj
    by_cases hij : i + j = n
    · subst n
      rw [DirectSum.of_apply]
      simp only [dif_pos rfl]
      change associatedLayerMul (coefficientFiltration F) i j (x i) (a.unop j) ∈
        symbolAddSubgroup (coefficientFiltration F) I (i + j)
      exact mul_mem_symbols (coefficientFiltration F) I i j (hx i) (a.unop j)
    · simp [DirectSum.of_apply, hij]

theorem exactSymbolRightIdeal_mono
    {I J : Submodule (Rees F)ᵐᵒᵖ (Rees F)} (hIJ : I ≤ J) :
    exactSymbolRightIdeal F I ≤ exactSymbolRightIdeal F J := by
  intro x hx n
  obtain ⟨p, hp, hpI, hpx⟩ := hx n
  exact ⟨p, hp, hIJ hpI, hpx⟩

theorem symbols_subset_of_exactSymbolRightIdeal_le
    {I J : Submodule (Rees F)ᵐᵒᵖ (Rees F)}
    (h : exactSymbolRightIdeal F I ≤ exactSymbolRightIdeal F J) (n : ℕ) :
    symbols (coefficientFiltration F) I n ⊆
      symbols (coefficientFiltration F) J n := by
  intro x hx
  let z := DirectSum.of (fun n : ℕ =>
    associatedLayer (coefficientFiltration F) n) n x
  have hzI : z ∈ exactSymbolRightIdeal F I := by
    intro m
    by_cases hmn : n = m
    · subst m
      simpa [z] using hx
    · have hzval : z m = 0 := by simp [z, DirectSum.of_apply, hmn]
      rw [hzval]
      exact ⟨0, (coefficientFiltration F).zero_mem m, I.zero_mem, rfl⟩
  have hzJ := h hzI
  simpa [z] using hzJ n

/- The exact symbol descent is now available for arbitrary nested right
   ideals.  It is the finite natural-number reduction from the producer,
   restated here as the transfer-facing theorem. -/
theorem filteredLeadingSymbolDescent
    (I J : Submodule (Rees F)ᵐᵒᵖ (Rees F))
    (hJI : J ≤ I)
    (hSymbols : ∀ n : ℕ,
      symbols (coefficientFiltration F) I n ⊆
        symbols (coefficientFiltration F) J n) :
    I ≤ J := by
  exact ReesCoefficientFiltration.le_of_symbols_subset F I J hJI hSymbols

theorem filteredLeadingSymbolEquality
    (I J : Submodule (Rees F)ᵐᵒᵖ (Rees F))
    (hIJ : I ≤ J) (hJI : J ≤ I)
    (hSymbols : ∀ n : ℕ,
      symbols (coefficientFiltration F) I n ⊆
        symbols (coefficientFiltration F) J n) :
    I = J := by
  exact le_antisymm (filteredLeadingSymbolDescent F I J hJI hSymbols) hJI

/- The polynomial Noetherian input is a real theorem, not a callback.  It is
   conditional only on the right-Noetherianity of the actual associated ring;
   the coefficient-filtration quotient assembly below is what would connect
   this polynomial ring to the Rees filtration. -/
theorem rightNoetherian_associatedPolynomial
    [IsNoetherian
      (AdditiveFilteredRingData.actualAssociatedGraded F)ᵐᵒᵖ
      (AdditiveFilteredRingData.actualAssociatedGraded F)] :
    IsNoetherian
      (SkewPolynomial (AdditiveFilteredRingData.actualAssociatedGraded F))ᵐᵒᵖ
      (SkewPolynomial (AdditiveFilteredRingData.actualAssociatedGraded F)) := by
  exact rightNoetherian_centralSkewPolynomial

/-- Right Noetherianity descends from the actual associated graded ring to
the bounded Rees ring.  Stabilization of the exact symbol ideals followed by
the natural-number symbol reduction gives stabilization of every ascending
chain of right ideals. -/
theorem rightNoetherian_rees
    [IsNoetherian
      (AdditiveFilteredRingData.actualAssociatedGraded F)ᵐᵒᵖ
      (AdditiveFilteredRingData.actualAssociatedGraded F)] :
    IsNoetherian (Rees F)ᵐᵒᵖ (Rees F) := by
  letI : IsNoetherian (coefficientAssociatedGraded F)ᵐᵒᵖ
      (coefficientAssociatedGraded F) :=
    rightNoetherian_coefficientAssociatedGraded F
  apply (monotone_stabilizes_iff_noetherian
    (R := (Rees F)ᵐᵒᵖ) (M := Rees F)).mp
  intro c
  let sc : ℕ →o Submodule (coefficientAssociatedGraded F)ᵐᵒᵖ
      (coefficientAssociatedGraded F) :=
    { toFun := fun n => exactSymbolRightIdeal F (c n)
      monotone' := fun i j hij => exactSymbolRightIdeal_mono F (c.monotone hij) }
  obtain ⟨n, hn⟩ :=
    (monotone_stabilizes_iff_noetherian
      (R := (coefficientAssociatedGraded F)ᵐᵒᵖ)
      (M := coefficientAssociatedGraded F)).mpr
        (inferInstance : IsNoetherian
          (coefficientAssociatedGraded F)ᵐᵒᵖ
          (coefficientAssociatedGraded F)) sc
  refine ⟨n, ?_⟩
  intro m hnm
  apply le_antisymm
  · exact c.monotone hnm
  · apply filteredLeadingSymbolDescent F (c m) (c n) (c.monotone hnm)
    intro d
    apply symbols_subset_of_exactSymbolRightIdeal_le F
    have hs : exactSymbolRightIdeal F (c n) = exactSymbolRightIdeal F (c m) :=
      hn m hnm
    exact hs.ge

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

theorem isNoetherianRing (C : LocallyFiniteAffineGradedRing K G) :
    IsNoetherianRing G := by
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
## Exact transfer

The preceding results produce the shifted symbol on every actual homogeneous
Rees lift, identify its kernel with the predecessor coefficient layer, and
assemble the degreewise quotients and the two finite direct sums into

`actualAssociatedGraded (ReesCoefficientFiltration.filtration F) ≃+*`
`SkewPolynomial (actualAssociatedGraded F)`.

The exact componentwise symbol right ideal then turns polynomial
Noetherianity into stabilization of Rees right ideals by the finite descending
reduction theorem.
-/

end

end SymplecticStafford.Filtered
