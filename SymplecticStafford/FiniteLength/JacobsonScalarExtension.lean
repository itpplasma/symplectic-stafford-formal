import SymplecticStafford.FiniteLength.FiniteOrbitPencil
import SymplecticStafford.FiniteLength.JacobsonTop
import SymplecticStafford.FiniteLength.RightFiltration

/-!
# Jacobson-top bridge for auxiliary scalar fields

This file packages the exact bridge needed when a finite-length top is
represented over a commutative auxiliary field.  The map to the block is
required to compare the *actual* Jacobson quotient with the orbit span; it is
not a completed quotient or a formal matrix surrogate.  The orbit basis is
over `E`, while the pencil parameter is in the central field `K`, so no
finite-dimensionality over `K` is inferred.

The resulting consumer is useful for repeated simple factors: the block type
`Q` may carry any supplied `E`-linear orbit action, including a product of
matrix or division-ring blocks.  All noncommutative coefficient data remain
in the explicit action and orbit-basis hypotheses.
-/

namespace SymplecticStafford.FiniteLength

open Module

universe u v w

section Data

variable {R : Type u} {M : Type v} {K : Type w}
variable [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [Field K] [Module K M] [Infinite K]
variable {E Q : Type*} [Field E] [Infinite E] [AddCommGroup Q] [Module E Q]

/-- A scalar-extension model of the actual Jacobson top.

`top_cyclic_iff` is deliberately stated using `Module.jacobson`, so a caller
must identify the supplied block with the actual radical quotient.  The
finite orbit basis is only required for vectors whose Jacobson image is
cyclic.  In particular, finite length alone is not used to manufacture a
finite-dimensional block or a division-ring decomposition.
-/
structure JacobsonScalarExtensionTopData where
  top : M →+ Q
  act : (Rᵐᵒᵖ) → Q →ₗ[E] Q
  ι : K →+* E
  ι_injective : Function.Injective ι
  top_smul : ∀ (z : K) (m : M), top (z • m) = ι z • top m
  top_cyclic_iff : ∀ m : M,
    RightCyclic (R := R)
        ((Module.jacobson Rᵐᵒᵖ M).mkQ m) ↔
      OrbitSpanTop (K := E) act (top m)
  orbit_basis : ∀ m : M,
    RightCyclic (R := R)
        ((Module.jacobson Rᵐᵒᵖ M).mkQ m) →
      ∃ n : Nat, ∃ b : Basis (Fin n) E Q,
        ∃ c : Fin n → Rᵐᵒᵖ,
          ∀ i, act (c i) (top m) = b i

end Data

section Consumer

variable {R : Type u} {M : Type v} {K : Type w}
variable [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [Field K] [Module K M] [Infinite K]
variable {E Q : Type*} [Field E] [Infinite E] [AddCommGroup Q] [Module E Q]

/-- Finite-length Jacobson-top activation over an auxiliary scalar field.

The filtration contributes the finite-generation instance needed to reflect
cyclicity through the actual Jacobson quotient.  The scalar is then selected
by the finite orbit-basis calculation over `E` and restricted along the
injective map from `K`.  The final identity keeps the original right-action
order visible.
-/
theorem exists_activated_right_cyclic_of_jacobson_scalar_extension
    {n : Nat}
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) n)
    (T : JacobsonScalarExtensionTopData (R := R) (M := M) (K := K)
      (E := E) (Q := Q))
    (rightAction : R → M → M)
    (rightAction_add : ∀ (r : R) (x y : M),
      rightAction r (x + y) = rightAction r x + rightAction r y)
    (central_smul_right : ∀ (k : K) (m : M) (r : R),
      rightAction r (k • m) = k • rightAction r m)
    (v u e : M) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : RightCyclic (R := R) v) (forbidden : Set K)
    (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧
      RightCyclic (R := R) (v + z • u) ∧
      rightAction l (v + z • u) + z • rightAction b v = z • e := by
  letI : Module.Finite Rᵐᵒᵖ M := F.moduleFinite
  have htop : ∀ m : M,
      RightCyclic (R := R) m ↔
        OrbitSpanTop (K := E) T.act (T.top m) := by
    intro m
    exact (rightCyclic_iff_jacobson_quotient (R := R) m).trans
      (T.top_cyclic_iff m)
  have horbit : ∀ m : M, RightCyclic (R := R) m →
      ∃ n : Nat, ∃ b : Basis (Fin n) E Q,
        ∃ c : Fin n → Rᵐᵒᵖ,
          ∀ i, T.act (c i) (T.top m) = b i := by
    intro m hm
    exact T.orbit_basis m
      ((rightCyclic_iff_jacobson_quotient (R := R) m).mp hm)
  exact exists_activated_right_cyclic_of_scalar_extension_orbit_basis
    (K := K) (R := R) (M := M) T.top T.act T.ι T.ι_injective T.top_smul
    htop horbit rightAction rightAction_add central_smul_right
    v u e b l vL_zero e_decomp hv forbidden hforbidden

end Consumer

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_jacobson_scalar_extension
