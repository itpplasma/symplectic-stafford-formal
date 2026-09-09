import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.FractionRing

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

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.homogeneousLaurentIdeal_strict
#print axioms SymplecticStafford.FiniteLength.fractionField_no_strict_submodule
