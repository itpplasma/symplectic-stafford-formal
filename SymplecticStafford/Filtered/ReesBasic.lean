module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Order.Basic
public import SymplecticStafford.Filtered.Localization

@[expose] public section

/-!
# Elementary algebraic Rees terms

This file formalizes the finite, algebraic part of the Rees construction that
is independent of Noetherianity or Ore localization.  A `ReesTerm F` records
an actual element of `R` together with a filtration bound.  The operations
use `max` for addition and addition of bounds for multiplication.  Thus all
claims below are kernel-checked closure and coherence facts; no existence of a
good filtration, a localization, or a source element is hidden in a field.

The quotient identifying a term with its monotone reindexings is deliberately
not introduced here.  It requires an explicit quotient relation and is a
separate M02/M03 interface.
-/

namespace SymplecticStafford.Filtered

universe u

variable {R : Type u} [Semiring R]

/-- An element of the raw (unquotiented) algebraic Rees object. -/
structure ReesTerm (F : FiltrationData R) where
  degree : ℕ
  value : R
  bounded : HasDegreeAtMost F degree value

namespace ReesTerm

variable {F : FiltrationData R}

@[ext]
theorem ext {x y : ReesTerm F} (hdegree : x.degree = y.degree)
    (hvalue : x.value = y.value) : x = y := by
  cases x with
  | mk xd xv xb =>
    cases y with
    | mk yd yv yb =>
      cases hdegree
      cases hvalue
      rfl

/-- Reindex a bounded element at any larger filtration degree. -/
def reindex (x : ReesTerm F) {n : ℕ} (h : x.degree ≤ n) : ReesTerm F where
  degree := n
  value := x.value
  bounded := F.monotone h x.bounded

@[simp] theorem reindex_degree (x : ReesTerm F) {n : ℕ}
    (h : x.degree ≤ n) : (reindex x h).degree = n := rfl

@[simp] theorem reindex_value (x : ReesTerm F) {n : ℕ}
    (h : x.degree ≤ n) : (reindex x h).value = x.value := rfl

theorem reindex_reindex (x : ReesTerm F) {m n : ℕ}
    (hm : x.degree ≤ m) (hn : m ≤ n) :
    reindex (reindex x hm) hn = reindex x (hm.trans hn) := by
  apply ext <;> rfl

theorem exists_value (F : FiltrationData R) (a : R) :
    ∃ x : ReesTerm F, x.value = a := by
  obtain ⟨n, hn⟩ := F.exhaustive a
  exact ⟨⟨n, a, hn⟩, rfl⟩

/-- The zero and one terms in filtration degree zero. -/
def zero : ReesTerm F where
  degree := 0
  value := 0
  bounded := F.zero_mem

def one : ReesTerm F where
  degree := 0
  value := 1
  bounded := F.one_mem

/-- Addition of raw Rees terms. -/
def add (x y : ReesTerm F) : ReesTerm F where
  degree := max x.degree y.degree
  value := x.value + y.value
  bounded := F.add_mem (i := x.degree) (j := y.degree) x.bounded y.bounded

/-- Multiplication of raw Rees terms. -/
def mul (x y : ReesTerm F) : ReesTerm F where
  degree := x.degree + y.degree
  value := x.value * y.value
  bounded := F.mul_mem x.bounded y.bounded

theorem reindex_add (x y : ReesTerm F) {n : ℕ}
    (h : max x.degree y.degree ≤ n)
    (hx : x.degree ≤ n) (hy : y.degree ≤ n) :
    reindex (add x y) h = add (reindex x hx) (reindex y hy) := by
  apply ext
  · change n = max n n
    simp
  · rfl

theorem reindex_mul (x y : ReesTerm F) {m n : ℕ}
    (hx : x.degree ≤ m) (hy : y.degree ≤ n) :
    reindex (mul x y) (Nat.add_le_add hx hy) =
      mul (reindex x hx) (reindex y hy) := by
  apply ext
  · rfl
  · rfl

@[simp] theorem add_degree (x y : ReesTerm F) :
    (add x y).degree = max x.degree y.degree := rfl

@[simp] theorem add_value (x y : ReesTerm F) :
    (add x y).value = x.value + y.value := rfl

@[simp] theorem mul_degree (x y : ReesTerm F) :
    (mul x y).degree = x.degree + y.degree := rfl

@[simp] theorem mul_value (x y : ReesTerm F) :
    (mul x y).value = x.value * y.value := rfl

theorem add_assoc_term (x y z : ReesTerm F) :
    add (add x y) z = add x (add y z) := by
  apply ext
  · simp [max_assoc]
  · exact add_assoc _ _ _

theorem add_comm_term (x y : ReesTerm F) : add x y = add y x := by
  apply ext
  · simp [max_comm]
  · exact add_comm _ _

theorem add_zero_term (x : ReesTerm F) : add x zero = reindex x (Nat.le_refl _) := by
  apply ext
  · simp [zero, Nat.max_eq_left]
  · simp [zero]

theorem zero_add_term (x : ReesTerm F) : add zero x = reindex x (Nat.le_refl _) := by
  apply ext
  · simp [zero, Nat.max_eq_right]
  · simp [zero]

theorem mul_assoc_term (x y z : ReesTerm F) :
    mul (mul x y) z = mul x (mul y z) := by
  apply ext
  · simp [Nat.add_assoc]
  · exact mul_assoc _ _ _

theorem one_mul_term (x : ReesTerm F) : mul one x = reindex x (Nat.le_refl _) := by
  apply ext
  · simp [one]
  · simp [one]

theorem mul_one_term (x : ReesTerm F) : mul x one = reindex x (Nat.le_refl _) := by
  apply ext
  · simp [one]
  · simp [one]

end ReesTerm

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.ReesTerm.reindex_reindex
#print axioms SymplecticStafford.Filtered.ReesTerm.exists_value
#print axioms SymplecticStafford.Filtered.ReesTerm.reindex_add
#print axioms SymplecticStafford.Filtered.ReesTerm.reindex_mul
#print axioms SymplecticStafford.Filtered.ReesTerm.add_assoc_term
#print axioms SymplecticStafford.Filtered.ReesTerm.mul_assoc_term
