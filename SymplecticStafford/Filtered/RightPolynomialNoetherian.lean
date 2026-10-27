module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.SkewPolynomial.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Opposites
public import SymplecticStafford.Filtered.ReesAlgebra

@[expose] public section

/-!
# Right Noetherianity of the central Rees polynomial ambient ring

The `ReesPolynomial` used by this project is a `SkewPolynomial` whose degree
action is trivial.  Its underlying convolution ring is therefore the usual
polynomial ring, but the two constructions are different structures in
Mathlib.  This file supplies the ring equivalence explicitly and transports
the ordinary Hilbert basis theorem across it.

Right Noetherianity is represented by `IsNoetherian Rᵐᵒᖘ R`.  The opposite
linear equivalence identifies this with ordinary (left) Noetherianity of the
opposite ring, which is the form consumed by Mathlib's polynomial theorem.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

/- The two formal-sum wrappers have the same coefficients.  Under the
   trivial action their convolution products agree, giving this explicit
   ring equivalence. -/
private def centralSkewMonoidAlgebraRingEquiv
    (R : Type u) [Ring R] :
    SkewMonoidAlgebra R (Multiplicative ℕ) ≃+*
      MonoidAlgebra R (Multiplicative ℕ) :=
  { toFun := fun p => ⟨p.coeff⟩
    invFun := fun p => ⟨p.coeff⟩
    left_inv := by
      intro p
      cases p
      rfl
    right_inv := by
      intro p
      cases p
      rfl
    map_add' := by
      intro p q
      apply MonoidAlgebra.coeff_injective
      simp
    map_mul' := by
      intro p q
      apply MonoidAlgebra.coeff_injective
      ext x
      simp only [SkewMonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_mul]
      change
        p.coeff.sum (fun a₁ b₁ => q.coeff.sum fun a₂ b₂ =>
          if a₁ * a₂ = x then b₁ * b₂ else 0) = _
      rfl }

private def centralSkewPolynomialRingEquiv (R : Type u) [Ring R] :
    SkewPolynomial R ≃+* Polynomial R :=
  (((centralSkewMonoidAlgebraRingEquiv R).trans
      (AddMonoidAlgebra.toMultiplicative R ℕ).symm).trans
    (Polynomial.toFinsuppIso R).symm)

private theorem rightNoetherian_iff_isNoetherianRing
    (A : Type u) [Ring A] :
    IsNoetherian Aᵐᵒᵖ A ↔ IsNoetherianRing Aᵐᵒᵖ := by
  let e : A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ := MulOpposite.opLinearEquiv Aᵐᵒᵖ
  exact e.isNoetherian_iff

namespace NoncommutativePolynomial

open Polynomial

variable {A : Type u} [Ring A]

/-- A left ideal of `A[X]`, regarded only as an `A`-submodule. -/
private def restrictCoefficients (I : Submodule A[X] A[X]) : Submodule A A[X] where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' a p hp := by
    rw [Polynomial.smul_eq_C_mul]
    exact I.smul_mem (C a) hp

private def degreeLE (I : Submodule A[X] A[X]) (n : WithBot ℕ) : Submodule A A[X] :=
  Polynomial.degreeLE A n ⊓ restrictCoefficients I

private def leadingCoeffNth (I : Submodule A[X] A[X]) (n : ℕ) : Submodule A A :=
  (degreeLE I n).map (lcoeff A n)

private theorem mem_leadingCoeffNth (I : Submodule A[X] A[X]) (n : ℕ) (x : A) :
    x ∈ leadingCoeffNth I n ↔
      ∃ p ∈ I, Polynomial.degree p ≤ n ∧ p.leadingCoeff = x := by
  simp only [leadingCoeffNth, degreeLE, Submodule.mem_map, lcoeff_apply,
    Submodule.mem_inf, Polynomial.mem_degreeLE]
  constructor
  · rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩
    rcases lt_or_eq_of_le hpdeg with hpdeg | hpdeg
    · refine ⟨0, I.zero_mem, bot_le, ?_⟩
      rw [leadingCoeff_zero, eq_comm]
      exact coeff_eq_zero_of_degree_lt hpdeg
    · refine ⟨p, hpI, le_of_eq hpdeg, ?_⟩
      rw [Polynomial.leadingCoeff, natDegree, hpdeg, Nat.cast_withBot,
        WithBot.unbotD_coe]
  · rintro ⟨p, hpI, hpdeg, rfl⟩
    have hadd : natDegree p + (n - natDegree p) = n :=
      add_tsub_cancel_of_le (natDegree_le_of_degree_le hpdeg)
    refine ⟨p * X ^ (n - natDegree p), ⟨?_, ?_⟩, ?_⟩
    · apply le_trans (degree_mul_le _ _) _
      apply le_trans (add_le_add degree_le_natDegree (degree_X_pow_le _)) _
      rw [← Nat.cast_add, hadd]
    · rw [← Polynomial.X_pow_mul]
      exact I.smul_mem _ hpI
    · rw [Polynomial.leadingCoeff, ← coeff_mul_X_pow p (n - natDegree p), hadd]

private theorem leadingCoeffNth_mono (I : Submodule A[X] A[X]) {m n : ℕ} (h : m ≤ n) :
    leadingCoeffNth I m ≤ leadingCoeffNth I n := by
  intro r hr
  rw [mem_leadingCoeffNth] at hr ⊢
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩
  refine ⟨p * X ^ (n - m), ?_, ?_, leadingCoeff_mul_X_pow⟩
  · rw [← Polynomial.X_pow_mul]
    exact I.smul_mem _ hpI
  · refine le_trans (degree_mul_le _ _) ?_
    grw [hpdeg, degree_X_pow_le]
    rw [← Nat.cast_add, add_tsub_cancel_of_le h]

private theorem fg_degreeLE [IsNoetherianRing A] (I : Submodule A[X] A[X]) (n : ℕ) :
    (degreeLE I n).FG := by
  letI := Classical.decEq A
  exact (show (Polynomial.degreeLE A n).FG from
    ⟨_, Polynomial.degreeLE_eq_span_X_pow.symm⟩).of_le inf_le_left

/-- The Hilbert basis theorem for a polynomial with central variable over an
arbitrary (possibly noncommutative) left Noetherian ring. -/
private theorem isNoetherianRing_polynomial [inst : IsNoetherianRing A] :
    IsNoetherianRing A[X] :=
  ⟨fun I : Submodule A[X] A[X] =>
    let M := inst.wf.min (Set.range (leadingCoeffNth I)) ⟨_, ⟨0, rfl⟩⟩
    have hm : M ∈ Set.range (leadingCoeffNth I) := WellFounded.min_mem _ _ _
    let ⟨N, hN⟩ := hm
    let ⟨s, hs⟩ := fg_degreeLE I N
    have hm2 : ∀ k, leadingCoeffNth I k ≤ M := fun k =>
      Or.casesOn (le_or_gt k N)
        (fun h => hN ▸ leadingCoeffNth_mono I h)
        (fun h _ hx => Classical.by_contradiction fun hxm =>
          have hnot : ¬ M < leadingCoeffNth I k := by
            refine WellFounded.not_lt_min inst.wf _ ?_
            exact ⟨k, rfl⟩
          hnot ⟨hN ▸ leadingCoeffNth_mono I (le_of_lt h), fun heq => hxm (heq hx)⟩)
    have hs2 : ∀ {p}, p ∈ degreeLE I N → p ∈ Submodule.span A[X] (↑s : Set A[X]) :=
      hs ▸ fun hp => Submodule.span_induction (hx := hp)
        (fun _ hp => Submodule.subset_span hp)
        (Submodule.zero_mem _)
        (fun _ _ _ _ hp hq => Submodule.add_mem _ hp hq)
        (fun a p _ hp => by
          rw [Polynomial.smul_eq_C_mul]
          exact (Submodule.span A[X] (↑s : Set A[X])).smul_mem (C a) hp)
    ⟨s, le_antisymm
      (Submodule.span_le.2 fun p hp => by
        have : p ∈ degreeLE I N := hs ▸ Submodule.subset_span hp
        exact this.2)
      (by
        intro p hp
        generalize hn : p.natDegree = k
        induction k using Nat.strong_induction_on generalizing p with
        | _ k ih =>
          rcases le_or_gt k N with h | h
          · subst k
            exact hs2 ⟨Polynomial.mem_degreeLE.2
              (le_trans Polynomial.degree_le_natDegree (WithBot.coe_le_coe.2 h)), hp⟩
          · have hp0 : p ≠ 0 := by
              rintro rfl
              cases hn
              exact Nat.not_lt_zero _ h
            have h01 : (0 : A) ≠ 1 := by
              intro hzero
              apply hp0
              letI := subsingleton_of_zero_eq_one hzero
              ext i
              exact Subsingleton.elim _ _
            letI : Nontrivial A := ⟨⟨0, 1, h01⟩⟩
            have hlc : p.leadingCoeff ∈ leadingCoeffNth I N := by
              rw [hN]
              exact hm2 k ((mem_leadingCoeffNth I k p.leadingCoeff).2
                ⟨p, hp, hn ▸ Polynomial.degree_le_natDegree, rfl⟩)
            rw [mem_leadingCoeffNth] at hlc
            rcases hlc with ⟨q, hq, hdq, hlqp⟩
            have hq0 : q ≠ 0 := by
              intro hqzero
              rw [← Polynomial.leadingCoeff_eq_zero] at hqzero
              rw [hlqp, Polynomial.leadingCoeff_eq_zero] at hqzero
              exact hp0 hqzero
            have hdegree : p.degree = (q * X ^ (k - q.natDegree)).degree := by
              rw [Polynomial.degree_mul', Polynomial.degree_X_pow]
              · rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0,
                  ← Nat.cast_add, add_tsub_cancel_of_le, hn]
                exact le_trans (Polynomial.natDegree_le_of_degree_le hdq) (le_of_lt h)
              rw [Polynomial.leadingCoeff_X_pow, mul_one]
              exact mt Polynomial.leadingCoeff_eq_zero.1 hq0
            have hlc' : p.leadingCoeff =
                (q * X ^ (k - q.natDegree)).leadingCoeff := by
              rw [← hlqp, Polynomial.leadingCoeff_mul_X_pow]
            have hlower := Polynomial.degree_sub_lt_left hdegree hp0 hlc'
            rw [Polynomial.degree_eq_natDegree hp0] at hlower
            rw [← sub_add_cancel p (q * X ^ (k - q.natDegree))]
            apply Submodule.add_mem
            · by_cases hpq : p - q * X ^ (k - q.natDegree) = 0
              · rw [hpq]
                exact Submodule.zero_mem _
              · refine ih _ ?_ (I.sub_mem hp ?_) rfl
                · rwa [Polynomial.degree_eq_natDegree hpq, Nat.cast_lt, hn] at hlower
                · rw [← Polynomial.X_pow_mul]
                  exact I.smul_mem _ hq
            · rw [← Polynomial.X_pow_mul]
              exact (Submodule.span A[X] (↑s : Set A[X])).smul_mem _
                (hs2 ⟨Polynomial.mem_degreeLE.2 hdq, hq⟩))⟩⟩

end NoncommutativePolynomial

/-- A right Noetherian coefficient ring has right Noetherian central skew
polynomial ring.  The central action is the trivial degree action used by
`ReesPolynomial`. -/
theorem rightNoetherian_centralSkewPolynomial
    {R : Type u} [Ring R] [IsNoetherian Rᵐᵒᵖ R] :
    IsNoetherian (SkewPolynomial R)ᵐᵒᵖ (SkewPolynomial R) := by
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    (rightNoetherian_iff_isNoetherianRing R).mp
      (inferInstance : IsNoetherian Rᵐᵒᵖ R)
  letI : IsNoetherianRing (Polynomial Rᵐᵒᵖ) :=
    NoncommutativePolynomial.isNoetherianRing_polynomial
  letI : IsNoetherianRing (Polynomial R)ᵐᵒᵖ :=
    isNoetherianRing_of_ringEquiv (Polynomial Rᵐᵒᵖ)
      (Polynomial.opRingEquiv R).symm
  letI : IsNoetherianRing (SkewPolynomial R)ᵐᵒᵖ :=
    isNoetherianRing_of_ringEquiv (Polynomial R)ᵐᵒᵖ
      (RingEquiv.op (centralSkewPolynomialRingEquiv R)).symm
  exact (rightNoetherian_iff_isNoetherianRing (SkewPolynomial R)).mpr
    (inferInstance : IsNoetherianRing (SkewPolynomial R)ᵐᵒᵖ)

end

end SymplecticStafford.Filtered
