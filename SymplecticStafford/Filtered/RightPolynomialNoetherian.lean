import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Opposites
import SymplecticStafford.Filtered.ReesAlgebra

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
      simp [SkewMonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_mul] }

private def centralSkewPolynomialRingEquiv (R : Type u) [Ring R] :
    SkewPolynomial R ≃+* Polynomial R :=
  (((centralSkewMonoidAlgebraRingEquiv R).trans
      (AddMonoidAlgebra.toMultiplicative R ℕ).symm).trans
    (Polynomial.toFinsuppIso R).symm)

private theorem rightNoetherian_iff_isNoetherianRing
    (A : Type u) [Ring A] :
    IsNoetherian Aᵐᵒᖘ A ↔ IsNoetherianRing Aᵐᵒᖘ := by
  let e : A ≃ₗ[Aᵐᵒᖘ] Aᵐᵒᖘ := MulOpposite.opLinearEquiv Aᵐᵒᖘ
  exact e.isNoetherian_iff

/-- A right Noetherian coefficient ring has right Noetherian central skew
polynomial ring.  The central action is the trivial degree action used by
`ReesPolynomial`. -/
theorem rightNoetherian_centralSkewPolynomial
    {R : Type u} [Ring R] [IsNoetherian Rᵐᵒᖘ R] :
    IsNoetherian (SkewPolynomial R)ᵐᵒᖘ (SkewPolynomial R) := by
  letI : IsNoetherianRing Rᵐᵒᖘ :=
    (rightNoetherian_iff_isNoetherianRing R).mp
      (inferInstance : IsNoetherian Rᵐᵒᖘ R)
  letI : IsNoetherianRing (Polynomial Rᵐᵒᖘ) :=
    Polynomial.isNoetherianRing
  letI : IsNoetherianRing (Polynomial R)ᵐᵒᖘ :=
    isNoetherianRing_of_ringEquiv (Polynomial Rᵐᵒᖘ)
      (Polynomial.opRingEquiv R).symm
  letI : IsNoetherianRing (SkewPolynomial R)ᵐᵒᖘ :=
    isNoetherianRing_of_ringEquiv (Polynomial R)ᵐᵒᖘ
      (RingEquiv.op (centralSkewPolynomialRingEquiv R)).symm
  exact (rightNoetherian_iff_isNoetherianRing (SkewPolynomial R)).mpr
    (inferInstance : IsNoetherianRing (SkewPolynomial R)ᵐᵒᖘ)

end

end SymplecticStafford.Filtered
