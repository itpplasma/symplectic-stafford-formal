module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Set.Defs
public import SymplecticStafford.Ordered.RightClear

@[expose] public section

/-!
# Filtered localization contract scaffold

This file records a small contract for a filtered or localized chart.  It is
deliberately not the paper's M03 theorem: the single-denominator power
clearing here is only a checkpoint utility, while the paper requires a full
homogeneous-symbol Ore set and algebraic Rees/module transfer.  The
right-clearing field is supplied by a future source theorem and does not
assert the same-divisor statement in the original ring.
-/

namespace SymplecticStafford.Filtered

universe u v

section Filtration

variable {R : Type u} [Semiring R]

/-- The nonnegative part of a multiplicative filtration.

`exhaustive` is included because a filtered chart may only be used after it
has been shown to contain every element.  No separatedness or commutativity is
silently bundled into this interface.
-/
structure FiltrationData (R : Type u) [Semiring R] where
  carrier : ℕ → Set R
  zero_mem : 0 ∈ carrier 0
  one_mem : 1 ∈ carrier 0
  add_mem : ∀ {i j : ℕ} {a b : R}, a ∈ carrier i → b ∈ carrier j →
    a + b ∈ carrier (max i j)
  mul_mem : ∀ {i j : ℕ} {a b : R}, a ∈ carrier i → b ∈ carrier j →
    a * b ∈ carrier (i + j)
  monotone : Monotone carrier
  exhaustive : ∀ a : R, ∃ n : ℕ, a ∈ carrier n

def HasDegreeAtMost (F : FiltrationData R) (n : ℕ) (a : R) : Prop :=
  a ∈ F.carrier n

theorem degreeAtMost_zero (F : FiltrationData R) :
    HasDegreeAtMost F 0 0 := F.zero_mem

theorem degreeAtMost_one (F : FiltrationData R) :
    HasDegreeAtMost F 0 1 := F.one_mem

theorem degreeAtMost_add {F : FiltrationData R} {i j : ℕ} {a b : R}
    (ha : HasDegreeAtMost F i a) (hb : HasDegreeAtMost F j b) :
    HasDegreeAtMost F (max i j) (a + b) :=
  F.add_mem ha hb

theorem degreeAtMost_mul {F : FiltrationData R} {i j : ℕ} {a b : R}
    (ha : HasDegreeAtMost F i a) (hb : HasDegreeAtMost F j b) :
    HasDegreeAtMost F (i + j) (a * b) :=
  F.mul_mem ha hb

end Filtration

section Localization

variable {R : Type u} [Semiring R]
variable {S : Type v} [Semiring S]

/-- A checkpoint certificate for a filtered chart and a single-denominator
power clearing operation.  It is not the paper's full symbol localization.

The map is a ring homomorphism, the denominator is an element of the
original ring, and every *specified* chart element must be right-clearable.
The latter is a hypothesis to be discharged by a source/localization proof;
this structure itself performs no localization and makes no universal S1
claim.
-/
structure FilteredLocalizationCertificate (R : Type u) (S : Type v)
    [Semiring R] [Semiring S] where
  sourceFiltration : FiltrationData R
  chartFiltration : FiltrationData S
  map : R →+* S
  map_filtered : ∀ {n : ℕ} {a : R},
    HasDegreeAtMost sourceFiltration n a →
      HasDegreeAtMost chartFiltration n (map a)
  denominator : R
  denominator_mem : ∃ n : ℕ, HasDegreeAtMost sourceFiltration n denominator
  right_clearable : ∀ x : S,
    SymplecticStafford.Ordered.RightClearable map.toMonoidHom denominator x

theorem map_degreeAtMost
    (C : FilteredLocalizationCertificate R S)
    {n : ℕ} {a : R} (ha : HasDegreeAtMost C.sourceFiltration n a) :
    HasDegreeAtMost C.chartFiltration n (C.map a) :=
  C.map_filtered ha

theorem common_right_clear
    (C : FilteredLocalizationCertificate R S) (xs : List S) :
    (∀ x ∈ xs, SymplecticStafford.Ordered.RightClearable
      C.map.toMonoidHom C.denominator x) →
      ∃ n : ℕ, ∀ x ∈ xs, ∃ y : R,
        x * (C.map C.denominator) ^ n = C.map y := by
  intro h
  exact SymplecticStafford.Ordered.exists_common_right_clear
    C.map.toMonoidHom C.denominator xs h

theorem common_right_clear_from_certificate
    (C : FilteredLocalizationCertificate R S) (xs : List S) :
    ∃ n : ℕ, ∀ x ∈ xs, ∃ y : R,
      x * (C.map C.denominator) ^ n = C.map y := by
  exact common_right_clear C xs (fun x _ => C.right_clearable x)

end Localization

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.degreeAtMost_mul
#print axioms SymplecticStafford.Filtered.common_right_clear
