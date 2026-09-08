import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.NoncommRing
import SymplecticStafford.Semantics.S1Consequences

/-!
# The ordered common-colon algebra

This file records the algebraic part of the common-colon construction used by
the all-dimensional paper.  For `d`, `F`, and `G` in the original ring, put

`K = {s | G * d * s ∈ dU}` and `J = dU + F * d * K`.

All products below retain this order.  The definitions and closure lemmas are
purely algebraic.  In particular, this file does not assert that a source
exists, that a localization is faithful, or that a geometric support is a
particular set.  Such statements belong to later hypotheses/consumers.
-/

namespace SymplecticStafford.Ordered

universe u

variable {R : Type u} [Semiring R]

/- The right principal set `dU = {d * r | r ∈ U}`. -/
def rightPrincipalSet (d : R) : Set R := {x | ∃ r : R, x = d * r}

theorem mem_rightPrincipalSet_iff (d x : R) :
    x ∈ rightPrincipalSet d ↔ ∃ r : R, x = d * r := Iff.rfl

/- The right common colon `(dU : Gd)`. -/
def commonColon (d G : R) : Set R :=
  {s | G * d * s ∈ rightPrincipalSet d}

theorem mem_commonColon_iff (d G s : R) :
    s ∈ commonColon d G ↔ ∃ c : R, G * d * s = d * c := Iff.rfl

theorem commonColon_zero_mem (d G : R) :
    (0 : R) ∈ commonColon d G := by
  change ∃ c : R, G * d * 0 = d * c
  exact ⟨0, by simp⟩

theorem commonColon_add_mem {d G s₁ s₂ : R}
    (h₁ : s₁ ∈ commonColon d G) (h₂ : s₂ ∈ commonColon d G) :
    s₁ + s₂ ∈ commonColon d G := by
  rcases h₁ with ⟨c₁, hc₁⟩
  rcases h₂ with ⟨c₂, hc₂⟩
  refine ⟨c₁ + c₂, ?_⟩
  calc
    G * d * (s₁ + s₂) = G * d * s₁ + G * d * s₂ := by
      noncomm_ring
    _ = d * c₁ + d * c₂ := by rw [hc₁, hc₂]
    _ = d * (c₁ + c₂) := by rw [mul_add]

theorem commonColon_right_mul_mem {d G s q : R}
    (h : s ∈ commonColon d G) :
    s * q ∈ commonColon d G := by
  rcases h with ⟨c, hc⟩
  refine ⟨c * q, ?_⟩
  calc
    G * d * (s * q) = (G * d * s) * q := by
      simp only [mul_assoc]
    _ = (d * c) * q := by rw [hc]
    _ = d * (c * q) := by rw [mul_assoc]

/- The colon, packaged as the right ideal it algebraically is. -/
def commonColonRightIdeal (d G : R) : RightIdeal (R := R) where
  carrier := commonColon d G
  zero_mem := commonColon_zero_mem d G
  add_mem := by
    intro a b ha hb
    exact commonColon_add_mem ha hb
  right_mul_mem := by
    intro a ha q
    exact commonColon_right_mul_mem ha

theorem mem_commonColonRightIdeal_iff (d G s : R) :
    s ∈ commonColonRightIdeal d G ↔ s ∈ commonColon d G := Iff.rfl

/- The common-colon ideal `J = dU + F*d*K`, with ordered factors exposed. -/
def commonIdeal (d F G : R) : Set R :=
  {x | ∃ r k : R, k ∈ commonColon d G ∧
    x = d * r + (F * d) * k}

theorem mem_commonIdeal_iff (d F G x : R) :
    x ∈ commonIdeal d F G ↔
      ∃ r k : R, k ∈ commonColon d G ∧
        x = d * r + (F * d) * k := Iff.rfl

theorem principal_mem_commonIdeal {d F G r : R} :
    d * r ∈ commonIdeal d F G := by
  refine ⟨r, 0, commonColon_zero_mem d G, ?_⟩
  simp

theorem correction_mem_commonIdeal {d F G k : R}
    (hk : k ∈ commonColon d G) :
    (F * d) * k ∈ commonIdeal d F G := by
  exact ⟨0, k, hk, by simp⟩

theorem commonIdeal_zero_mem (d F G : R) :
    (0 : R) ∈ commonIdeal d F G := by
  refine ⟨0, 0, commonColon_zero_mem d G, ?_⟩
  simp

theorem commonIdeal_add_mem {d F G x y : R}
    (hx : x ∈ commonIdeal d F G) (hy : y ∈ commonIdeal d F G) :
    x + y ∈ commonIdeal d F G := by
  rcases hx with ⟨r₁, k₁, hk₁, h₁⟩
  rcases hy with ⟨r₂, k₂, hk₂, h₂⟩
  refine ⟨r₁ + r₂, k₁ + k₂, commonColon_add_mem hk₁ hk₂, ?_⟩
  rw [h₁, h₂]
  noncomm_ring

theorem commonIdeal_right_mul_mem {d F G x q : R}
    (hx : x ∈ commonIdeal d F G) :
    x * q ∈ commonIdeal d F G := by
  rcases hx with ⟨r, k, hk, h⟩
  refine ⟨r * q, k * q, commonColon_right_mul_mem hk, ?_⟩
  rw [h]
  noncomm_ring

/- The common ideal, packaged as a right ideal without adding hypotheses. -/
def commonRightIdeal (d F G : R) : RightIdeal (R := R) where
  carrier := commonIdeal d F G
  zero_mem := commonIdeal_zero_mem d F G
  add_mem := by
    intro a b ha hb
    exact commonIdeal_add_mem ha hb
  right_mul_mem := by
    intro a ha q
    exact commonIdeal_right_mul_mem ha

theorem mem_commonRightIdeal_iff (d F G x : R) :
    x ∈ commonRightIdeal d F G ↔ x ∈ commonIdeal d F G := Iff.rfl

section Ring

variable {R : Type u} [Ring R]

/- The exact ordered pencil identity.  The centrality hypothesis is explicit
  rather than hidden in a typeclass: this makes the only commutation used by
  the identity visible to a later localization/support consumer. -/
theorem central_commonColon_identity
    (d F G k c t : R)
    (hcolon : G * d * k = d * c)
    (hcentral : ∀ x : R, t * x = x * t) :
    F * d * k = d * (-t * c) + (F + t * G) * d * k := by
  calc
    F * d * k = d * (-t * c) + F * d * k + t * (G * d * k) := by
      rw [hcolon]
      have htc : t * (d * c) = d * t * c := by
        rw [← mul_assoc, hcentral d]
      rw [htc]
      noncomm_ring
    _ = d * (-t * c) + (F + t * G) * d * k := by
      noncomm_ring

theorem central_commonColon_identity_of_mem
    (d F G k t : R)
    (hk : k ∈ commonColon d G)
    (hcentral : ∀ x : R, t * x = x * t) :
    ∃ c : R,
      F * d * k = d * (-t * c) + (F + t * G) * d * k := by
  rcases hk with ⟨c, hc⟩
  exact ⟨c, central_commonColon_identity d F G k c t hc hcentral⟩

/- This is the algebraic inclusion used before any support argument: every
  element of J has a right-certificate for the affine source.  It is not a
  claim that either source ideal is the geometric universal ideal. -/
theorem commonIdeal_subset_affineRightIdeal
    (d F G t : R)
    (hcentral : ∀ x : R, t * x = x * t) :
    commonIdeal d F G ⊆ (twoGeneratedRightIdeal d (F + t * G)).carrier := by
  intro x hx
  rcases hx with ⟨r, k, hk, hx⟩
  rcases hk with ⟨c, hc⟩
  refine ⟨r - t * c, k, ?_⟩
  rw [hx]
  rw [central_commonColon_identity d F G k c t hc hcentral]
  noncomm_ring

end Ring

/- A support-union statement is deliberately an interface, not a theorem of
  this file.  The auxiliary divisor is explicit because the paper's second
  support branch need not use the original divisor `d`.  A later geometric
  consumer may supply this hypothesis after proving the relevant
  localization/support facts. -/
def SupportUnionHypothesis {X : Type*}
    (support : RightIdeal (R := R) → Set X)
    (d F G dAux : R) : Prop :=
  support (commonRightIdeal d F G) ⊆
    support (twoGeneratedRightIdeal d F) ∪
      support (twoGeneratedRightIdeal dAux G)

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.commonColon_add_mem
#print axioms SymplecticStafford.Ordered.commonIdeal_right_mul_mem
#print axioms SymplecticStafford.Ordered.central_commonColon_identity
#print axioms SymplecticStafford.Ordered.commonIdeal_subset_affineRightIdeal
