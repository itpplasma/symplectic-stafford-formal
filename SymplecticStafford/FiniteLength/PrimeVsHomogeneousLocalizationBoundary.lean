module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length

@[expose] public section

/-!
# Ordinary-prime versus homogeneous-symbol localization

This is a small algebraic boundary for Part I.5.  In the A1 model
`G = ℚ[X, ξ]` with homogeneous prime `p = (X)`, killing `X` after inverting
homogeneous symbols outside `p` leaves the Laurent coefficient ring
`ℚ[ξ, ξ⁻¹]`.  Ordinary localization at the prime and then killing `X`
instead has coefficient field `Frac(ℚ[ξ])`.  The two coefficient rings have
different submodule behavior: the Laurent ring has the proper nonzero ideal
`(ξ - 1)`, while a fraction field has no nontrivial submodules of its regular
module.

The file formalizes these two precise model facts.  It does not assert the
filtered/noncommutative isomorphisms from the paper; those remain hypotheses
to establish.  In particular, it does not refute S1 or any Weyl-algebra
theorem.  It only prevents replacing homogeneous localization by ordinary
prime localization in a length argument without an additional bridge.
-/

namespace SymplecticStafford.FiniteLength

open LaurentPolynomial

noncomputable def homogeneousLaurentIdeal : Ideal (LaurentPolynomial ℚ) :=
  Ideal.span {LaurentPolynomial.T 1 - LaurentPolynomial.C (1 : ℚ)}

private noncomputable def evalAtOne : LaurentPolynomial ℚ →+* ℚ :=
  LaurentPolynomial.eval₂ (RingHom.id ℚ) (Units.mk0 1 (by norm_num))

private noncomputable def evalAtTwo : LaurentPolynomial ℚ →+* ℚ :=
  LaurentPolynomial.eval₂ (RingHom.id ℚ) (Units.mk0 2 (by norm_num))

/- The kernel of evaluation at one is a prime (in fact maximal) ideal.  We
   keep it separate from `homogeneousLaurentIdeal`: the latter is the
   concrete principal ideal used above, while the kernel gives a short,
   independent proof that the homogeneous localization is not Artinian. -/
private noncomputable def evalAtOneKernel : Ideal (LaurentPolynomial ℚ) :=
  RingHom.ker evalAtOne

private theorem evalAtOneKernel_ne_bot :
    evalAtOneKernel ≠ (⊥ : Ideal (LaurentPolynomial ℚ)) := by
  intro hbot
  have hmem : LaurentPolynomial.T 1 - LaurentPolynomial.C (1 : ℚ) ∈
      evalAtOneKernel := by
    change evalAtOne (LaurentPolynomial.T 1 - LaurentPolynomial.C (1 : ℚ)) = 0
    norm_num [evalAtOne]
  rw [hbot] at hmem
  have hz : LaurentPolynomial.T 1 - LaurentPolynomial.C (1 : ℚ) = 0 :=
    Ideal.mem_bot.mp hmem
  have he := congrArg evalAtTwo hz
  norm_num [evalAtTwo] at he

private theorem evalAtOneKernel_ne_top :
    evalAtOneKernel ≠ (⊤ : Ideal (LaurentPolynomial ℚ)) := by
  intro htop
  have hmem : (1 : LaurentPolynomial ℚ) ∈ evalAtOneKernel := by
    rw [htop]
    trivial
  change evalAtOne (1 : LaurentPolynomial ℚ) = 0 at hmem
  norm_num [evalAtOne] at hmem

private theorem evalAtOneKernel_isPrime : evalAtOneKernel.IsPrime := by
  exact RingHom.ker_isPrime evalAtOne

/- The homogeneous-symbol localization in the A1 model has a genuine prime
   strictly above zero.  Hence it cannot be Artinian: in an Artinian
   commutative ring every prime ideal is maximal, so the zero prime would
   already be maximal and could not lie strictly below this kernel. -/
theorem homogeneousLaurent_not_isArtinianRing :
    ¬ IsArtinianRing (LaurentPolynomial ℚ) := by
  intro hArt
  letI : IsArtinianRing (LaurentPolynomial ℚ) := hArt
  have hbotPrime : (⊥ : Ideal (LaurentPolynomial ℚ)).IsPrime := by
    infer_instance
  letI : (⊥ : Ideal (LaurentPolynomial ℚ)).IsPrime := hbotPrime
  have hbotMax : (⊥ : Ideal (LaurentPolynomial ℚ)).IsMaximal := by
    infer_instance
  have hEq : (⊥ : Ideal (LaurentPolynomial ℚ)) = evalAtOneKernel :=
    hbotMax.eq_of_le evalAtOneKernel_ne_top bot_le
  exact evalAtOneKernel_ne_bot hEq.symm

/- By Hopkins--Levitzki, finite length of the regular module would make the
   coefficient ring Artinian.  This is the exact length obstruction needed
   for the Part I.5 warning, rather than merely exhibiting one proper ideal. -/
theorem homogeneousLaurent_not_isFiniteLength :
    ¬ IsFiniteLength (LaurentPolynomial ℚ) (LaurentPolynomial ℚ) := by
  intro hLength
  exact homogeneousLaurent_not_isArtinianRing
    ((isArtinianRing_iff_isFiniteLength (R := LaurentPolynomial ℚ)).mpr hLength)

theorem homogeneousLaurentIdeal_ne_top :
    homogeneousLaurentIdeal ≠ (⊤ : Ideal (LaurentPolynomial ℚ)) := by
  intro htop
  have hm : (1 : LaurentPolynomial ℚ) ∈ homogeneousLaurentIdeal := by
    rw [htop]
    trivial
  rcases (Ideal.mem_span_singleton.mp hm) with ⟨q, hq⟩
  have he := congrArg evalAtOne hq
  norm_num [homogeneousLaurentIdeal, evalAtOne] at he

theorem homogeneousLaurentIdeal_ne_bot :
    homogeneousLaurentIdeal ≠ (⊥ : Ideal (LaurentPolynomial ℚ)) := by
  intro hbot
  have hm : LaurentPolynomial.T 1 - LaurentPolynomial.C (1 : ℚ) ∈
      homogeneousLaurentIdeal := Ideal.subset_span (by simp)
  have hm0 : LaurentPolynomial.T 1 - LaurentPolynomial.C (1 : ℚ) = 0 := by
    rw [hbot] at hm
    exact (Ideal.mem_bot.mp hm)
  have he := congrArg evalAtTwo hm0
  norm_num [evalAtTwo] at he

theorem homogeneousLaurentIdeal_strict :
    (⊥ : Ideal (LaurentPolynomial ℚ)) < homogeneousLaurentIdeal ∧
      homogeneousLaurentIdeal < (⊤ : Ideal (LaurentPolynomial ℚ)) := by
  exact ⟨lt_of_le_of_ne bot_le homogeneousLaurentIdeal_ne_bot.symm,
    lt_top_iff_ne_top.mpr homogeneousLaurentIdeal_ne_top⟩

theorem divisionRing_submodule_eq_bot_or_top {K : Type*} [DivisionRing K]
    (I : Submodule K K) : I = ⊥ ∨ I = ⊤ := by
  by_cases hbot : I = ⊥
  · exact Or.inl hbot
  · right
    apply le_antisymm le_top
    intro x hx
    have hex : ∃ y, y ∈ I ∧ y ≠ 0 := by
      by_contra h'
      push_neg at h'
      apply hbot
      apply le_antisymm
      · intro y hy
        exact (Submodule.mem_bot K).2 (h' y hy)
      · exact bot_le
    obtain ⟨y, hy, hy0⟩ := hex
    have h1 : (1 : K) ∈ I := by
      have hi := I.smul_mem (y⁻¹) hy
      simpa [smul_eq_mul, inv_mul_cancel₀ hy0] using hi
    simpa using I.smul_mem x h1

theorem fractionField_no_strict_submodule
    (I : Submodule (FractionRing (Polynomial ℚ))
      (FractionRing (Polynomial ℚ))) :
    ¬ ((⊥ : Submodule (FractionRing (Polynomial ℚ))
      (FractionRing (Polynomial ℚ))) < I ∧
      I < (⊤ : Submodule (FractionRing (Polynomial ℚ))
        (FractionRing (Polynomial ℚ)))) := by
  intro h
  rcases divisionRing_submodule_eq_bot_or_top I with hbot | htop
  · subst I
    exact (lt_irrefl _ h.1)
  · subst I
    exact (lt_irrefl _ h.2)

/- The ordinary-prime coefficient model is a one-simple-factor regular
   module: its scalar ring is a division ring.  Stating its exact length makes
   the boundary quantitative, rather than merely saying that the two module
   lattices have different strict inclusions. -/
theorem fractionField_regular_module_length_eq_one :
    Module.length (FractionRing (Polynomial ℚ))
      (FractionRing (Polynomial ℚ)) = 1 := by
  exact Module.length_eq_one _ _

/- The model comparison used by the Part I.5 warning.  The ordinary prime
   coefficient module has length one, whereas the homogeneous-symbol Laurent
   coefficient module is not finite length.  No identification of either
   model with a filtered quantum localization is asserted here. -/
theorem homogeneous_vs_ordinary_length_contrast :
    (¬ IsFiniteLength (LaurentPolynomial ℚ) (LaurentPolynomial ℚ)) ∧
      Module.length (FractionRing (Polynomial ℚ))
        (FractionRing (Polynomial ℚ)) = 1 := by
  exact ⟨homogeneousLaurent_not_isFiniteLength,
    fractionField_regular_module_length_eq_one⟩

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.homogeneousLaurentIdeal_strict
#print axioms SymplecticStafford.FiniteLength.fractionField_no_strict_submodule
