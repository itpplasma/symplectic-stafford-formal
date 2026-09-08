import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ext

/-!
# The literal right-certificate semantics of S1

This file deliberately contains only algebraic consequences of a certificate.
In particular, it does not assume (or state) any rank, cancellation, support,
or filtered-algebra theorem.  The multiplication order in `RightCertificate`
is the order in the original algebra.
-/

namespace SymplecticStafford

universe u

section Semiring

variable {R : Type u} [Semiring R]

/- A small, explicit right-ideal interface.  We do not identify right ideals
  with left ideals in the same ring: closure is stated using multiplication on
  the right. -/
structure RightIdeal (R : Type u) [Semiring R] where
  carrier : Set R
  zero_mem : 0 ∈ carrier
  add_mem : ∀ {a b : R}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  right_mul_mem : ∀ {a : R}, a ∈ carrier → ∀ r : R, a * r ∈ carrier

instance : Membership R (RightIdeal (R := R)) :=
  ⟨fun I a => a ∈ I.carrier⟩

@[ext]
theorem RightIdeal.ext {I J : RightIdeal (R := R)}
    (h : ∀ a : R, a ∈ I ↔ a ∈ J) : I = J := by
  cases I with
  | mk I hI0 hIadd hImul =>
    cases J with
    | mk J hJ0 hJadd hJmul =>
      simp only [Membership.mem] at h
      congr
      ext a
      exact h a

theorem rightIdeal_zero_mem (I : RightIdeal (R := R)) : (0 : R) ∈ I := I.zero_mem

theorem rightIdeal_add_mem {I : RightIdeal (R := R)} {a b : R}
    (ha : a ∈ I) (hb : b ∈ I) : a + b ∈ I := I.add_mem ha hb

theorem rightIdeal_right_mul_mem {I : RightIdeal (R := R)} {a : R}
    (ha : a ∈ I) (r : R) : a * r ∈ I := I.right_mul_mem ha r

def twoGeneratedRightIdeal (d f : R) : RightIdeal (R := R) where
  carrier := {a | ∃ r s : R, a = d * r + (f * d) * s}
  zero_mem := by
    exact ⟨0, 0, by simp⟩
  add_mem := by
    rintro a b ⟨r₁, s₁, ha⟩ ⟨r₂, s₂, hb⟩
    refine ⟨r₁ + r₂, s₁ + s₂, ?_⟩
    rw [ha, hb]
    simp only [mul_add, add_assoc, add_left_comm]
  right_mul_mem := by
    rintro a ⟨r, s, ha⟩ q
    refine ⟨r * q, s * q, ?_⟩
    rw [ha]
    simp only [add_mul, mul_assoc]

theorem mem_twoGeneratedRightIdeal_iff (d f a : R) :
    a ∈ twoGeneratedRightIdeal d f ↔
      ∃ r s : R, a = d * r + (f * d) * s := Iff.rfl

structure RightCertificate (R : Type u) [Semiring R] (d f a : R) where
  right₁ : R
  right₂ : R
  identity : a = d * right₁ + (f * d) * right₂

theorem rightCertificate_mem (c : RightCertificate (R := R) d f a) :
    a ∈ twoGeneratedRightIdeal d f :=
  ⟨c.right₁, c.right₂, c.identity⟩

theorem rightCertificate_iff_mem (d f a : R) :
    Nonempty (RightCertificate (R := R) d f a) ↔
      a ∈ twoGeneratedRightIdeal d f := by
  constructor
  · rintro ⟨c⟩
    exact rightCertificate_mem c
  · rintro h
    rcases h with ⟨r, s, hs⟩
    exact ⟨⟨r, s, hs⟩⟩

theorem rightCertificate_iff_mem_iff (d f a : R) :
    (∃ r s : R, a = d * r + (f * d) * s) ↔
      a ∈ twoGeneratedRightIdeal d f := Iff.rfl

def SameDivisorS1 : Prop :=
  ∀ ⦃d : R⦄, d ≠ 0 → ∃ f r s : R, 1 = d * r + (f * d) * s

theorem sameDivisorS1_iff_rightCertificate :
    SameDivisorS1 (R := R) ↔
      ∀ ⦃d : R⦄, d ≠ 0 →
        ∃ f : R, Nonempty (RightCertificate (R := R) d f 1) := by
  constructor
  · intro h d hd
    rcases h hd with ⟨f, r, s, hs⟩
    exact ⟨f, ⟨⟨r, s, hs⟩⟩⟩
  · intro h d hd
    rcases h hd with ⟨f, ⟨c⟩⟩
    exact ⟨f, c.right₁, c.right₂, c.identity⟩

theorem certificate_mul_right {d f a q r s : R}
    (h : a = d * r + (f * d) * s) :
    a * q = d * (r * q) + (f * d) * (s * q) := by
  rw [h]
  simp only [add_mul, mul_assoc]

theorem one_certificate_generates_quotient {d f r s : R}
    (h : (1 : R) = d * r + (f * d) * s) :
    ∀ a : R, ∃ r' s' : R, a = d * r' + (f * d) * s' := by
  intro a
  refine ⟨r * a, s * a, ?_⟩
  calc
    a = 1 * a := (one_mul a).symm
    _ = (d * r + (f * d) * s) * a := by rw [h]
    _ = d * (r * a) + (f * d) * (s * a) := by
      simp only [add_mul, mul_assoc]

theorem one_certificate_mem_generates_quotient {d f r s : R}
    (h : (1 : R) = d * r + (f * d) * s) :
    ∀ a : R, a ∈ twoGeneratedRightIdeal d f := by
  intro a
  exact (one_certificate_generates_quotient h a)

theorem one_mem_iff_generates_right_ideal (d f : R) :
    (1 : R) ∈ twoGeneratedRightIdeal d f ↔
      ∀ a : R, a ∈ twoGeneratedRightIdeal d f := by
  constructor
  · intro h a
    rcases h with ⟨r, s, h⟩
    exact one_certificate_mem_generates_quotient h a
  · intro h
    exact h 1

theorem certificate_rewrite {d f r s : R}
    (h : (1 : R) = d * r + (f * d) * s) :
    ∀ a : R, a = d * (r * a) + (f * d) * (s * a) := by
  intro a
  calc
    a = 1 * a := (one_mul a).symm
    _ = (d * r + (f * d) * s) * a := by rw [h]
    _ = d * (r * a) + (f * d) * (s * a) := by
      simp only [add_mul, mul_assoc]

end Semiring

section Opposite

variable {R : Type u} [Semiring R]

/- Reversing every product gives a left certificate in the opposite ring.
  This is intentionally a separate predicate, so a right-ideal statement is
  never silently reused as a left-ideal statement. -/
def LeftOppositeCertificate (R : Type u) [Semiring R] (d f a : Rᵐᵒᵖ) : Prop :=
  ∃ r s : Rᵐᵒᵖ, a = r * d + s * (d * f)

theorem rightCertificate_opposite {d f r s : R}
    (h : (1 : R) = d * r + (f * d) * s) :
    LeftOppositeCertificate (R := R) (MulOpposite.op d) (MulOpposite.op f)
      (MulOpposite.op (1 : R)) := by
  refine ⟨MulOpposite.op r, MulOpposite.op s, ?_⟩
  simpa only [MulOpposite.op_one, MulOpposite.op_add, MulOpposite.op_mul] using
    congrArg MulOpposite.op h

theorem leftOppositeCertificate_iff_rightCertificate
    {d f : R} :
    (∃ r s : R, (1 : R) = d * r + (f * d) * s) ↔
      LeftOppositeCertificate (R := R) (MulOpposite.op d) (MulOpposite.op f)
        (MulOpposite.op (1 : R)) := by
  constructor
  · intro h
    rcases h with ⟨r, s, hs⟩
    exact rightCertificate_opposite hs
  · rintro ⟨r, s, hs⟩
    have h := congrArg MulOpposite.unop hs
    simpa only [MulOpposite.unop_one, MulOpposite.unop_add,
      MulOpposite.unop_mul] using
      ⟨MulOpposite.unop r, MulOpposite.unop s, h⟩

end Opposite

end SymplecticStafford
