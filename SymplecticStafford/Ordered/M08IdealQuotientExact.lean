module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Support
public import SymplecticStafford.Ordered.M08ExactSupportBridge

@[expose] public section

/-!
# The actual ideal-quotient exact sequence for M08

For a commutative ring `A` and ideals `I ≤ J`, this file constructs the
canonical sequence

```text
J / I  --->  A / I  --->  A / J.
```

The maps are induced by the inclusion `J → A` and the identity of `A`; their
injectivity, exactness, and surjectivity are proved from quotient
representatives.  This is the standard commutative ideal-chain instance of
the exact-support bridge.  Identifying the paper's common-colon modules with
these quotients remains a separate obligation.
-/

namespace SymplecticStafford.Ordered

universe u

section

variable {A : Type u} [CommRing A]

/-- The submodule of `J` induced by the smaller ideal `I`. -/
abbrev idealQuotientKernel (I J : Ideal A) : Submodule A J :=
  Submodule.comap J.subtype I

/-- The left map in `J/I → A/I → A/J`. -/
def idealQuotientLeftMap (I J : Ideal A) (_hIJ : I ≤ J) :
    (J ⧸ idealQuotientKernel I J) →ₗ[A] (A ⧸ I) :=
  (idealQuotientKernel I J).mapQ I J.subtype le_rfl

/-- The right map in `J/I → A/I → A/J`. -/
def idealQuotientRightMap (I J : Ideal A) (hIJ : I ≤ J) :
    (A ⧸ I) →ₗ[A] (A ⧸ J) :=
  I.mapQ J LinearMap.id (by
    intro x hx
    exact hIJ hx)

theorem idealQuotientLeftMap_injective
    (I J : Ideal A) (hIJ : I ≤ J) :
    Function.Injective (idealQuotientLeftMap I J hIJ) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Quotient.exists_rep x
  obtain ⟨y, rfl⟩ := Quotient.exists_rep y
  apply (Submodule.Quotient.eq (idealQuotientKernel I J)).mpr
  have hdiff :
      I.mkQ ((x : A) - (y : A)) = 0 := by
    have hdiff' :
        idealQuotientLeftMap I J hIJ
            (Submodule.Quotient.mk (p := idealQuotientKernel I J) x) -
          idealQuotientLeftMap I J hIJ
            (Submodule.Quotient.mk (p := idealQuotientKernel I J) y) = 0 := by
      exact sub_eq_zero.mpr hxy
    simpa [idealQuotientLeftMap] using hdiff'
  have hmem : (x : A) - (y : A) ∈ I :=
    (Submodule.Quotient.mk_eq_zero I).mp hdiff
  change J.subtype (x - y) ∈ I
  simpa using hmem

theorem idealQuotientRightMap_surjective
    (I J : Ideal A) (hIJ : I ≤ J) :
    Function.Surjective (idealQuotientRightMap I J hIJ) := by
  intro z
  obtain ⟨a, rfl⟩ := Quotient.exists_rep z
  exact ⟨I.mkQ a, by rfl⟩

theorem idealQuotient_maps_exact
    (I J : Ideal A) (hIJ : I ≤ J) :
    Function.Exact (idealQuotientLeftMap I J hIJ)
      (idealQuotientRightMap I J hIJ) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · ext x
    change J.mkQ (x : A) = 0
    exact (Submodule.Quotient.mk_eq_zero J).mpr x.property
  · intro x hx
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    have haJ : a ∈ J := by
      apply (Submodule.Quotient.mk_eq_zero J).mp
      change (I.mapQ J LinearMap.id _) (Submodule.Quotient.mk a) = 0 at hx
      rw [Submodule.mapQ_apply] at hx
      simpa using hx
    refine ⟨Submodule.Quotient.mk
      (p := idealQuotientKernel I J) ⟨a, haJ⟩, ?_⟩
    change I.mkQ a = I.mkQ a
    rfl

/-- The constructed exact-support bridge for the ideal chain `I ≤ J`. -/
def idealQuotientExactSupportBridge
    (I J : Ideal A) (hIJ : I ≤ J) :
    ExactCharacteristicSupportBridge
      (A := A) (QF := (J ⧸ idealQuotientKernel I J))
      (QJ := (A ⧸ I)) (QG := (A ⧸ J)) where
  left := idealQuotientLeftMap I J hIJ
  right := idealQuotientRightMap I J hIJ
  exact := idealQuotient_maps_exact I J hIJ
  left_injective := idealQuotientLeftMap_injective I J hIJ
  right_surjective := idealQuotientRightMap_surjective I J hIJ

/-- Actual support equality supplied by the canonical commutative
    ideal-chain sequence. -/
theorem idealQuotient_support_eq_union
    (I J : Ideal A) (hIJ : I ≤ J) :
    Module.support A (A ⧸ I) =
      Module.support A (J ⧸ idealQuotientKernel I J) ∪
        Module.support A (A ⧸ J) := by
  exact characteristicSupport_eq_union_of_exact_bridge
    (idealQuotientExactSupportBridge I J hIJ)

end

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.idealQuotientLeftMap_injective
#print axioms SymplecticStafford.Ordered.idealQuotient_maps_exact
#print axioms SymplecticStafford.Ordered.idealQuotient_support_eq_union
