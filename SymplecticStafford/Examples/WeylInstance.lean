import Stafford38.Weyl.CoordinateCommutatorSymbol
import Stafford38.Weyl.SymbolCompatibility
import Stafford38.Statement
import SymplecticStafford.Paper.Induction
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.CharZero.Infinite

/-!
# The Weyl algebra satisfies the hypotheses of target theorem A

This module is an independent non-vacuity check for the standing hypotheses of
`SymplecticStafford.Paper.FilteredAlgebraData.targetA`.  For every field `k`
and every rank `n` it builds

* `weylFilteredAlgebraData k n : FilteredAlgebraData k (PresentedWeyl k n)
    (MvPolynomial (PhaseVar n) k) (MvPolynomial.homogeneousSubmodule _ k)`,
  the Bernstein filtration (all generators of weight one) of the presented Weyl
  algebra with its associated graded ring identified with the polynomial ring
  graded by total degree;

and, in characteristic zero,

* `isSimpleRing k n : IsSimpleRing (PresentedWeyl k n)`;
* `not_finiteDimensional k n : ¬ FiniteDimensional k (PresentedWeyl k (n + 1))`;
* `ringKrullDim_lt_top k n : ringKrullDim (MvPolynomial (PhaseVar n) k) < ⊤`;
* `weyl_targetA` and `stafford38_universalStatement : Stafford38.UniversalStatement`,
  Stafford's Theorem 3.8 for every `Aₙ(k)` as the case `B = 0`, `a = 1`.

`PresentedWeyl k n` is definitionally the `RingQuot` of the free algebra used
in the Stafford 3.8 challenge (`Stafford38Challenge.WeylAlg k n`) and is the
same term as `Stafford38.WeylAlg k n`.

The data are taken from the pinned `stafford38Formal` dependency: the PBW
normal form, the weighted filtrations, the principal-component symbol maps
and their multiplicativity.  The simplicity proof is new: commutation with the
newest coordinate/momentum acts on normal forms as `∓ ∂/∂ξ₀`, `∂/∂x₀`, which
in characteristic zero strips the newest pair from a nonzero element of a
two-sided ideal; induction on the rank finishes in `A₀ = k`.

`SymplecticStafford.lean` imports this module; `Solution.lean` does not.
-/

namespace SymplecticStafford.Examples.WeylInstance

open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBW
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylCommutatorSymbol
open Stafford38.WeylCoordinateCommutatorSymbol
open SymplecticStafford.Paper

noncomputable section

universe u

variable (k : Type u) [Field k]

/-! ### The filtered-algebra data -/

theorem monomialWeight_bernstein_apply_le {n : ℕ} (m : PhaseVar n →₀ ℕ) (i : PhaseVar n) :
    m i ≤ monomialWeight (@bernsteinWeight n) m := by
  classical
  by_cases hi : m i = 0
  · rw [hi]; exact Nat.zero_le _
  have h := Finset.single_le_sum (f := fun j => m j * bernsteinWeight j)
    (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hi)
  simpa [monomialWeight, Finsupp.sum, bernsteinWeight] using h

theorem eq_zero_of_monomialWeight_bernstein_eq_zero {n : ℕ} {m : PhaseVar n →₀ ℕ}
    (h : monomialWeight (@bernsteinWeight n) m = 0) : m = 0 := by
  ext i
  have := monomialWeight_bernstein_apply_le m i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  omega

theorem normalForm_algebraMap (n : ℕ) (c : k) :
    presentedNormalFormLinearEquiv k n (algebraMap k (PresentedWeyl k n) c) =
      MvPolynomial.C c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, presentedNormalFormLinearEquiv_one,
    MvPolynomial.smul_eq_C_mul, mul_one]

theorem eq_algebraMap_of_normalForm_eq_C {n : ℕ} {z : PresentedWeyl k n} {c : k}
    (h : presentedNormalFormLinearEquiv k n z = MvPolynomial.C c) :
    z = algebraMap k (PresentedWeyl k n) c := by
  apply (presentedNormalFormLinearEquiv k n).injective
  rw [h, normalForm_algebraMap]

theorem bernstein_zero_piece (n : ℕ) :
    presentedWeightPiece k (@bernsteinWeight n) 0 =
      LinearMap.range (Algebra.linearMap k (PresentedWeyl k n)) := by
  apply le_antisymm
  · intro z hz
    rw [mem_presentedWeightPiece] at hz
    refine ⟨MvPolynomial.coeff 0 (presentedNormalFormLinearEquiv k n z), ?_⟩
    rw [Algebra.linearMap_apply]
    symm
    apply eq_algebraMap_of_normalForm_eq_C
    ext m
    rw [MvPolynomial.coeff_C]
    split_ifs with hm
    · rw [hm]
    · by_contra hne
      exact hm (eq_zero_of_monomialWeight_bernstein_eq_zero
        (Nat.eq_zero_of_le_zero (hz m hne))).symm
  · rintro _ ⟨c, rfl⟩
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c
      (Stafford38.WeylSymbolCompatibility.one_mem_bernsteinPiece k n)

theorem finite_bernsteinExponents (n N : ℕ) :
    {m : PhaseVar n →₀ ℕ | monomialWeight (@bernsteinWeight n) m ≤ N}.Finite := by
  classical
  let B : PhaseVar n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  refine (Set.finite_Iic B).subset ?_
  intro m hm
  change m ≤ B
  intro i
  simp only [B, Finsupp.equivFunOnFinite_symm_apply_apply]
  exact (monomialWeight_bernstein_apply_le m i).trans hm

instance finiteDimensional_bernsteinPiece (n N : ℕ) :
    FiniteDimensional k (presentedWeightPiece k (@bernsteinWeight n) N) := by
  rw [presentedWeightPiece_eq_span]
  apply FiniteDimensional.span_of_finite k
  refine ((finite_bernsteinExponents n N).image (presentedPBWBasis k n)).subset ?_
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, hm, rfl⟩

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The Bernstein symbol map `Fₙ → (k[x, ξ])ₙ`, the principal component. -/
def bernsteinGr (n N : ℕ) :
    presentedWeightPiece k (@bernsteinWeight n) N →ₗ[k]
      MvPolynomial.homogeneousSubmodule (PhaseVar n) k N :=
  principalComponentOnPiece k (@bernsteinWeight n) N

theorem bernsteinGr_eq_zero_iff {n N : ℕ}
    (x : presentedWeightPiece k (@bernsteinWeight n) N) :
    bernsteinGr k n N x = 0 ↔
      (x : PresentedWeyl k n) ∈ presentedStrictLowerPiece k (@bernsteinWeight n) N := by
  rw [← mem_ker_principalComponentOnPiece_iff, LinearMap.mem_ker]
  rfl

/-- **The Bernstein filtration of the Weyl algebra** satisfies the standing
hypotheses of the manuscript, with `G = k[x₁,…,xₙ,ξ₁,…,ξₙ]` graded by total
degree. -/
def weylFilteredAlgebraData (n : ℕ) :
    FilteredAlgebraData k (PresentedWeyl k n) (MvPolynomial (PhaseVar n) k)
      (MvPolynomial.homogeneousSubmodule (PhaseVar n) k) where
  F N := presentedWeightPiece k (@bernsteinWeight n) N
  mono _ _ h := presentedWeightPiece_mono k _ h
  exhaustive a := exists_mem_bernsteinPiece k a
  zero_piece := bernstein_zero_piece k n
  finiteDimensional N := finiteDimensional_bernsteinPiece k n N
  mul_mem hu hv := mul_mem_bernsteinPiece k hu hv
  gr N := bernsteinGr k n N
  gr_surjective N := principalComponentOnPiece_surjective k (@bernsteinWeight n)
  gr_zero_eq_zero_iff x := by
    rw [bernsteinGr_eq_zero_iff]
    change (x : PresentedWeyl k n) ∈ (⊥ : Submodule k (PresentedWeyl k n)) ↔ _
    rw [Submodule.mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  gr_succ_eq_zero_iff N x := bernsteinGr_eq_zero_iff k x
  gr_mul x y := presentedPrincipalComponent_mul_bernstein k x.2 y.2

/-! ### Commutators with the newest pair act as partial derivatives -/

section Commutators

variable (n : ℕ)

local notation "NF" => presentedNormalFormLinearEquiv k (n + 1)
local notation "X₀" => presentedCoordinate k n
local notation "P₀" => presentedMomentum k n

theorem extendPhaseExponent_sub_newestCoordinate (a p : ℕ) (m : PhaseVar n →₀ ℕ) :
    extendPhaseExponent n a p m - Finsupp.single (.inl (0 : Fin (n + 1))) 1 =
      extendPhaseExponent n (a - 1) p m := by
  classical
  have hnew : (Finsupp.mapDomain oldIndex m) (.inl (0 : Fin (n + 1))) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨i, hi⟩
    cases i <;> simp [oldIndex, Fin.succ_ne_zero] at hi
  ext i
  rcases i with i | i
  · by_cases hi : i = 0
    · subst i
      simp [extendPhaseExponent, hnew]
    · have h0i : (0 : Fin (n + 1)) ≠ i := Ne.symm hi
      simp [extendPhaseExponent, hi]
  · by_cases hi : i = 0
    · subst i
      simp [extendPhaseExponent]
    · have h0i : (0 : Fin (n + 1)) ≠ i := Ne.symm hi
      simp [extendPhaseExponent, hi]

theorem extendPhaseExponent_newestCoordinate_apply (a p : ℕ) (m : PhaseVar n →₀ ℕ) :
    extendPhaseExponent n a p m (.inl (0 : Fin (n + 1))) = a := by
  have hnew : (Finsupp.mapDomain oldIndex m) (.inl (0 : Fin (n + 1))) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨i, hi⟩
    cases i <;> simp [oldIndex, Fin.succ_ne_zero] at hi
  simp [extendPhaseExponent, hnew]

theorem momentum_commutator_coefficientOrdered (a p : ℕ) (z : PresentedWeyl k n) :
    P₀ * presentedCoefficientOrdered k n a p z - presentedCoefficientOrdered k n a p z * P₀ =
      (a : k) • presentedCoefficientOrdered k n (a - 1) p z := by
  have hPZ : P₀ * previousWeylEmbedding k n z = previousWeylEmbedding k n z * P₀ :=
    presentedMomentum_commutes_previous k n z
  have hPX : P₀ * X₀ - X₀ * P₀ = 1 := by
    rw [presentedMomentum_mul_coordinate k n]; abel
  have hpow : P₀ * X₀ ^ a - X₀ ^ a * P₀ = (a : k) • X₀ ^ (a - 1) := by
    cases a with
    | zero => simp
    | succ r =>
      rw [AlgebraicAnalysis.OreDivision.OreAmbient.commutator_pow_succ P₀ X₀ hPX r,
        Nat.cast_smul_eq_nsmul k]
      simp
  simp only [presentedCoefficientOrdered]
  set Z := previousWeylEmbedding k n z
  have e1 : P₀ * (Z * X₀ ^ a * P₀ ^ p) = Z * (P₀ * X₀ ^ a) * P₀ ^ p := by
    rw [← mul_assoc, ← mul_assoc, hPZ, mul_assoc Z, mul_assoc Z]
  have e2 : Z * X₀ ^ a * P₀ ^ p * P₀ = Z * (X₀ ^ a * P₀) * P₀ ^ p := by
    simp only [mul_assoc, ← pow_succ']; rw [pow_succ]
  rw [e1, e2, ← sub_mul, ← mul_sub, hpow, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

theorem normalForm_coordinate_commutator (w : PresentedWeyl k (n + 1)) :
    NF (X₀ * w - w * X₀) = -MvPolynomial.pderiv (.inr (0 : Fin (n + 1))) (NF w) := by
  have key : (NF).toLinearMap ∘ₗ (LinearMap.mulLeft k X₀ - LinearMap.mulRight k X₀) =
      (-(MvPolynomial.pderiv (R := k)
        (Sum.inr (0 : Fin (n + 1)) : PhaseVar (n + 1))).toLinearMap) ∘ₗ (NF).toLinearMap := by
    apply (presentedPBWBasis k (n + 1)).ext
    intro m
    rw [presentedPBWBasis_succ_eq_coefficientOrdered k n m]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, LinearEquiv.coe_coe, LinearMap.neg_apply,
      Derivation.coeFn_coe]
    have h := presentedCoordinate_commutator_coefficientOrdered k n
      (m (.inl (0 : Fin (n + 1)))) (m (.inr (0 : Fin (n + 1))))
      (presentedPBWBasis k n (phaseExponent (fun i => m (.inl i.succ))
        (fun i => m (.inr i.succ))))
    change _ * _ - _ * _ = _ at h
    rw [h, map_neg, map_smul, presentedCoefficientOrdered_basis_normal,
      presentedCoefficientOrdered_basis_normal, MvPolynomial.pderiv_monomial,
      extendPhaseExponent_sub_newestMomentum_general,
      extendPhaseExponent_newestMomentum_apply, MvPolynomial.smul_monomial]
    simp
  exact LinearMap.congr_fun key w

theorem normalForm_momentum_commutator (w : PresentedWeyl k (n + 1)) :
    NF (P₀ * w - w * P₀) = MvPolynomial.pderiv (.inl (0 : Fin (n + 1))) (NF w) := by
  have key : (NF).toLinearMap ∘ₗ (LinearMap.mulLeft k P₀ - LinearMap.mulRight k P₀) =
      ((MvPolynomial.pderiv (R := k)
        (Sum.inl (0 : Fin (n + 1)) : PhaseVar (n + 1))).toLinearMap) ∘ₗ (NF).toLinearMap := by
    apply (presentedPBWBasis k (n + 1)).ext
    intro m
    rw [presentedPBWBasis_succ_eq_coefficientOrdered k n m]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, LinearEquiv.coe_coe, Derivation.coeFn_coe]
    rw [momentum_commutator_coefficientOrdered, map_smul,
      presentedCoefficientOrdered_basis_normal,
      presentedCoefficientOrdered_basis_normal, MvPolynomial.pderiv_monomial,
      extendPhaseExponent_sub_newestCoordinate,
      extendPhaseExponent_newestCoordinate_apply, MvPolynomial.smul_monomial]
    simp
  exact LinearMap.congr_fun key w

theorem normalForm_previous (z : PresentedWeyl k n) :
    NF (previousWeylEmbedding k n z) =
      MvPolynomial.rename oldIndex (presentedNormalFormLinearEquiv k n z) := by
  have h := presentedNormalFormLinearEquiv_previous_ordered k n 0 0 z
  simpa [presentedCoefficientOrdered] using h

end Commutators

/-! ### Polynomial lemmas in characteristic zero -/

section Poly

variable {σ : Type*}

/-- `v` does not occur in any monomial of `g`. -/
def AvoidsVar (v : σ) (g : MvPolynomial σ k) : Prop :=
  ∀ m ∈ g.support, m v = 0

theorem avoidsVar_of_pderiv_eq_zero [CharZero k] {v : σ} {g : MvPolynomial σ k}
    (h : MvPolynomial.pderiv v g = 0) : AvoidsVar k v g := by
  classical
  intro m hm
  by_contra hmv
  have hle : Finsupp.single v 1 ≤ m := by
    rw [Finsupp.single_le_iff]; omega
  have hc := MvPolynomial.coeff_pderiv (i := v) g (m - Finsupp.single v 1)
  rw [h, MvPolynomial.coeff_zero, tsub_add_cancel_of_le hle] at hc
  have hm' : MvPolynomial.coeff m g ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  exact mul_ne_zero hm' (Nat.cast_add_one_ne_zero _) hc.symm

theorem avoidsVar_pderiv {v w : σ} {g : MvPolynomial σ k} (hg : AvoidsVar k v g)
    (hvw : v ≠ w) : AvoidsVar k v (MvPolynomial.pderiv w g) := by
  classical
  intro m hm
  have hc := MvPolynomial.coeff_pderiv (i := w) g m
  have hne : MvPolynomial.coeff m (MvPolynomial.pderiv w g) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [hc] at hne
  have hs : m + Finsupp.single w 1 ∈ g.support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne)
  have := hg _ hs
  simpa [Finsupp.single_apply, Ne.symm hvw] using this

/-- The largest exponent of `v` in `g`. -/
def varDegree (v : σ) (g : MvPolynomial σ k) : ℕ := g.support.sup fun m => m v

theorem varDegree_pderiv_lt {v : σ} {g : MvPolynomial σ k}
    (h : MvPolynomial.pderiv v g ≠ 0) :
    varDegree k v (MvPolynomial.pderiv v g) < varDegree k v g := by
  classical
  have key : ∀ m ∈ (MvPolynomial.pderiv v g).support, m v + 1 ≤ varDegree k v g := by
    intro m hm
    have hne : MvPolynomial.coeff m (MvPolynomial.pderiv v g) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hne
    have hs : m + Finsupp.single v 1 ∈ g.support :=
      MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne)
    have := Finset.le_sup (f := fun m => m v) hs
    simpa [varDegree] using this
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty
    (fun he => h (MvPolynomial.support_eq_empty.mp he))
  have hpos : 0 < varDegree k v g := by have := key m hm; omega
  show (MvPolynomial.pderiv v g).support.sup (fun m => m v) < varDegree k v g
  refine (Finset.sup_lt_iff hpos).2 fun m hm => ?_
  have := key m hm
  omega

/-- A set of polynomials closed under `∂/∂v` contains, with a nonzero
element, a nonzero element killed by `∂/∂v`. -/
theorem exists_pderiv_eq_zero {v : σ} (S : Set (MvPolynomial σ k))
    (hS : ∀ g ∈ S, MvPolynomial.pderiv v g ∈ S) :
    ∀ f ∈ S, f ≠ 0 → ∃ g ∈ S, g ≠ 0 ∧ MvPolynomial.pderiv v g = 0 := by
  intro f
  induction hN : varDegree k v f using Nat.strong_induction_on generalizing f with
  | _ N ih =>
    intro hf hf0
    by_cases hd : MvPolynomial.pderiv v f = 0
    · exact ⟨f, hf, hf0, hd⟩
    · exact ih _ (hN ▸ varDegree_pderiv_lt k hd) _ rfl (hS f hf) hd

end Poly

/-! ### Simplicity -/

section Simple

variable [CharZero k]

theorem nontrivial (n : ℕ) : Nontrivial (PresentedWeyl k n) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := congrArg (presentedNormalFormLinearEquiv k n) h
  rw [presentedNormalFormLinearEquiv_one, map_zero] at this
  exact one_ne_zero this

/-- Stripping the newest pair: a two-sided ideal of `A_{n+1}` containing a
nonzero element contains the image of a nonzero element of `A_n`. -/
theorem exists_previous_mem (n : ℕ) (I : TwoSidedIdeal (PresentedWeyl k (n + 1)))
    {z : PresentedWeyl k (n + 1)} (hz : z ∈ I) (hz0 : z ≠ 0) :
    ∃ z' : PresentedWeyl k n, z' ≠ 0 ∧ previousWeylEmbedding k n z' ∈ I := by
  classical
  let NF := presentedNormalFormLinearEquiv k (n + 1)
  let S : Set (MvPolynomial (PhaseVar (n + 1)) k) := {g | ∃ w ∈ I, NF w = g}
  have hSmom : ∀ g ∈ S, MvPolynomial.pderiv (.inr (0 : Fin (n + 1))) g ∈ S := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨-(presentedCoordinate k n * w - w * presentedCoordinate k n), ?_, ?_⟩
    · exact I.neg_mem (I.sub_mem (I.mul_mem_left _ _ hw) (I.mul_mem_right _ _ hw))
    · rw [map_neg, normalForm_coordinate_commutator, neg_neg]
  have hScoord : ∀ g ∈ S, MvPolynomial.pderiv (.inl (0 : Fin (n + 1))) g ∈ S := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨presentedMomentum k n * w - w * presentedMomentum k n, ?_, ?_⟩
    · exact I.sub_mem (I.mul_mem_left _ _ hw) (I.mul_mem_right _ _ hw)
    · rw [normalForm_momentum_commutator]
  have hf0 : NF z ≠ 0 := by
    intro h; exact hz0 (NF.injective (h.trans (map_zero NF).symm))
  obtain ⟨g₁, hg₁S, hg₁0, hg₁⟩ := exists_pderiv_eq_zero k S hSmom (NF z) ⟨z, hz, rfl⟩ hf0
  let S' : Set (MvPolynomial (PhaseVar (n + 1)) k) :=
    {g | g ∈ S ∧ AvoidsVar k (.inr (0 : Fin (n + 1))) g}
  have hS' : ∀ g ∈ S', MvPolynomial.pderiv (.inl (0 : Fin (n + 1))) g ∈ S' := by
    rintro g ⟨hgS, hgA⟩
    exact ⟨hScoord g hgS, avoidsVar_pderiv k hgA (by simp)⟩
  obtain ⟨g₂, ⟨hg₂S, hg₂A⟩, hg₂0, hg₂⟩ := exists_pderiv_eq_zero k S' hS' g₁
    ⟨hg₁S, avoidsVar_of_pderiv_eq_zero k hg₁⟩ hg₁0
  have hg₂A' := avoidsVar_of_pderiv_eq_zero k hg₂
  obtain ⟨w, hw, hwg⟩ := hg₂S
  have hvars : (g₂.vars : Set (PhaseVar (n + 1))) ⊆ Set.range oldIndex := by
    intro v hv
    rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hv
    obtain ⟨d, hd, hvd⟩ := hv
    rw [Finsupp.mem_support_iff] at hvd
    rcases v with i | i
    · induction i using Fin.cases with
      | zero => exact absurd (hg₂A' d hd) hvd
      | succ j => exact ⟨.inl j, rfl⟩
    · induction i using Fin.cases with
      | zero => exact absurd (hg₂A d hd) hvd
      | succ j => exact ⟨.inr j, rfl⟩
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range g₂ oldIndex
    oldIndex_injective hvars
  refine ⟨(presentedNormalFormLinearEquiv k n).symm q, ?_, ?_⟩
  · intro h0
    apply hg₂0
    rw [← hq, ← LinearEquiv.apply_symm_apply (presentedNormalFormLinearEquiv k n) q, h0,
      map_zero, map_zero]
  · have : previousWeylEmbedding k n ((presentedNormalFormLinearEquiv k n).symm q) = w := by
      apply NF.injective
      change presentedNormalFormLinearEquiv k (n + 1) _ = _
      rw [normalForm_previous, LinearEquiv.apply_symm_apply, hq]
      exact hwg.symm
    rw [this]; exact hw

theorem one_mem_of_ne_zero_mem :
    ∀ (n : ℕ) (I : TwoSidedIdeal (PresentedWeyl k n)) (z : PresentedWeyl k n),
      z ∈ I → z ≠ 0 → (1 : PresentedWeyl k n) ∈ I := by
  intro n
  induction n with
  | zero =>
    intro I z hz hz0
    have hC : presentedNormalFormLinearEquiv k 0 z =
        MvPolynomial.C (MvPolynomial.coeff 0 (presentedNormalFormLinearEquiv k 0 z)) := by
      ext m
      have hm : m = 0 := Subsingleton.elim _ _
      subst hm
      simp
    have hz' := eq_algebraMap_of_normalForm_eq_C k hC
    set c := MvPolynomial.coeff 0 (presentedNormalFormLinearEquiv k 0 z)
    have hc : c ≠ 0 := by
      rintro hc; rw [hc, map_zero] at hz'; exact hz0 hz'
    have : algebraMap k (PresentedWeyl k 0) c⁻¹ * z = 1 := by
      rw [hz', ← map_mul, inv_mul_cancel₀ hc, map_one]
    rw [← this]
    exact I.mul_mem_left _ _ hz
  | succ n ih =>
    intro I z hz hz0
    obtain ⟨z', hz'0, hz'⟩ := exists_previous_mem k n I hz hz0
    have h1 := ih (I.comap (previousWeylEmbedding k n)) z'
      ((TwoSidedIdeal.mem_comap _).mpr hz') hz'0
    rw [TwoSidedIdeal.mem_comap, map_one] at h1
    exact h1

/-- **The Weyl algebra is simple** in characteristic zero. -/
theorem isSimpleRing (n : ℕ) : IsSimpleRing (PresentedWeyl k n) := by
  have := nontrivial k n
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases h : ∃ z ∈ I, z ≠ 0
  · obtain ⟨z, hz, hz0⟩ := h
    exact Or.inr ((TwoSidedIdeal.one_mem_iff I).mp (one_mem_of_ne_zero_mem k n I z hz hz0))
  · left
    push Not at h
    ext x
    rw [TwoSidedIdeal.mem_bot]
    exact ⟨fun hx => h x hx, fun hx => hx ▸ I.zero_mem⟩

end Simple

/-! ### Infinite dimension and the commutative side -/

theorem not_finiteDimensional (n : ℕ) : ¬ FiniteDimensional k (PresentedWeyl k (n + 1)) := by
  intro h
  have hfin : Finite (PhaseVar (n + 1) →₀ ℕ) :=
    Module.Finite.finite_basis (presentedPBWBasis k (n + 1))
  have hinj : Function.Injective fun j : ℕ =>
      Finsupp.single (Sum.inl (0 : Fin (n + 1)) : PhaseVar (n + 1)) j :=
    Finsupp.single_injective _
  exact (Infinite.of_injective _ hinj).not_finite hfin

theorem ringKrullDim_lt_top (n : ℕ) : ringKrullDim (MvPolynomial (PhaseVar n) k) < ⊤ := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _) |>.trans_le le_top

/-! ### Stafford 3.8 as a corollary of target theorem A -/

/-- Target theorem A for the Weyl algebra, in the manuscript's general form. -/
theorem weyl_targetA [CharZero k] (n : ℕ) (d a : PresentedWeyl k n) (hd : d ≠ 0)
    (ha : a ≠ 0) (B : PresentedWeyl k n) :
    ∃ H R S : PresentedWeyl k n, 1 = d * R + (B + H * a) * d * S := by
  have := isSimpleRing k n
  have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  exact (weylFilteredAlgebraData k n).targetA (ringKrullDim_lt_top k n) d a hd ha B

/-- **Stafford's Theorem 3.8** (`1 = d R + F d S` in `Aₙ(k)`, `char k = 0`)
follows from target theorem A with `B = 0`, `a = 1`. -/
theorem stafford38_universalStatement : Stafford38.UniversalStatement := by
  intro k _ _ n d hd
  have := nontrivial k n
  obtain ⟨H, R, S, h⟩ := weyl_targetA k n d 1 hd one_ne_zero 0
  exact ⟨H, R, S, by simpa using h⟩

end

end SymplecticStafford.Examples.WeylInstance
