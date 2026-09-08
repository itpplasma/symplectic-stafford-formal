import SymplecticStafford.Filtered.ReesBasic

/-!
# The value quotient of raw Rees terms

Two bounded terms are identified when they have the same underlying value in
`R`. Thus every monotone reindexing is identified with its source. The
quotient operations below are defined by `Quotient.liftOn₂`, with
representative independence checked in the kernel.

This is only a finite algebraic interface. It does not construct an
associated graded object, prove filtered Noetherianity, or provide a
symbol/Ore localization. Those remain separate M02--M03 obligations.
-/

namespace SymplecticStafford.Filtered

universe u

variable {R : Type u} [Semiring R]

namespace ReesTerm

variable {F : FiltrationData R}

/-- The reindex-invariant relation on raw terms. -/
def valueRel (x y : ReesTerm F) : Prop := x.value = y.value

theorem valueRel_refl (x : ReesTerm F) : valueRel x x := rfl

theorem valueRel_symm {x y : ReesTerm F} : valueRel x y → valueRel y x := by
  intro h
  exact h.symm

theorem valueRel_trans {x y z : ReesTerm F} :
    valueRel x y → valueRel y z → valueRel x z := by
  intro hxy hyz
  exact hxy.trans hyz

def valueSetoid (F : FiltrationData R) : Setoid (ReesTerm F) where
  r := valueRel
  iseqv := {
    refl := by intro x; exact valueRel_refl x
    symm := by intro x y h; exact valueRel_symm h
    trans := by intro x y z hxy hyz; exact valueRel_trans hxy hyz
  }

theorem valueRel_reindex (x : ReesTerm F) {n : ℕ} (h : x.degree ≤ n) :
    valueRel (reindex x h) x := rfl

theorem valueRel_add {x x' y y' : ReesTerm F}
    (hx : valueRel x x') (hy : valueRel y y') :
    valueRel (add x y) (add x' y') := by
  change x.value + y.value = x'.value + y'.value
  change x.value = x'.value at hx
  change y.value = y'.value at hy
  rw [hx, hy]

theorem valueRel_mul {x x' y y' : ReesTerm F}
    (hx : valueRel x x') (hy : valueRel y y') :
    valueRel (mul x y) (mul x' y') := by
  change x.value * y.value = x'.value * y'.value
  change x.value = x'.value at hx
  change y.value = y'.value at hy
  rw [hx, hy]

end ReesTerm

/-- Raw Rees terms modulo equality of their underlying algebra elements. -/
def ReesQuotient (F : FiltrationData R) := Quotient (ReesTerm.valueSetoid F)

namespace ReesQuotient

variable {F : FiltrationData R}

/-- The quotient class of a raw term. -/
def mk (x : ReesTerm F) : ReesQuotient F :=
  Quotient.mk (ReesTerm.valueSetoid F) x

private theorem quotient_eq {x y : ReesTerm F}
    (h : ReesTerm.valueRel x y) : mk x = mk y := by
  exact @Quotient.sound (ReesTerm F) (ReesTerm.valueSetoid F) x y h

/-- Underlying value, which is well-defined on the quotient. -/
def value : ReesQuotient F → R :=
  Quotient.lift ReesTerm.value (by
    intro x y h
    change x.value = y.value at h
    exact h)

@[simp] theorem value_mk (x : ReesTerm F) : value (mk x) = x.value := by
  simp [value, mk]

theorem eq_of_value_eq {x y : ReesQuotient F} (h : value x = value y) : x = y := by
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y =>
      change x.value = y.value at h
      apply quotient_eq
      exact h

/-- Reindexing a bounded term does not change its quotient class. -/
theorem reindex_mk (x : ReesTerm F) {n : ℕ} (h : x.degree ≤ n) :
    mk (ReesTerm.reindex x h) = mk x :=
  quotient_eq (ReesTerm.valueRel_reindex x h)

/-- Addition on the quotient, defined only after proving representative
independence. -/
def add (x y : ReesQuotient F) : ReesQuotient F :=
  Quotient.liftOn₂ x y
    (fun a b => mk (ReesTerm.add a b))
    (by
      intro a b c d hac hbd
      exact quotient_eq (ReesTerm.valueRel_add hac hbd))

/-- Multiplication on the quotient, defined only after proving representative
independence. -/
def mul (x y : ReesQuotient F) : ReesQuotient F :=
  Quotient.liftOn₂ x y
    (fun a b => mk (ReesTerm.mul a b))
    (by
      intro a b c d hac hbd
      exact quotient_eq (ReesTerm.valueRel_mul hac hbd))

def zero : ReesQuotient F := mk ReesTerm.zero

def one : ReesQuotient F := mk ReesTerm.one

@[simp] theorem value_add (x y : ReesQuotient F) :
    value (add x y) = value x + value y := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  rfl

@[simp] theorem value_mul (x y : ReesQuotient F) :
    value (mul x y) = value x * value y := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  rfl

theorem add_assoc (x y z : ReesQuotient F) :
    add (add x y) z = add x (add y z) := by
  apply eq_of_value_eq
  simp only [value_add]
  exact _root_.add_assoc _ _ _

theorem add_comm (x y : ReesQuotient F) : add x y = add y x := by
  apply eq_of_value_eq
  simp only [value_add]
  exact _root_.add_comm _ _

theorem add_zero (x : ReesQuotient F) : add x zero = x := by
  apply eq_of_value_eq
  simp only [value_add]
  simp [zero, value, mk, ReesTerm.zero]

theorem zero_add (x : ReesQuotient F) : add zero x = x := by
  apply eq_of_value_eq
  simp only [value_add]
  simp [zero, value, mk, ReesTerm.zero]

theorem mul_assoc (x y z : ReesQuotient F) :
    mul (mul x y) z = mul x (mul y z) := by
  apply eq_of_value_eq
  simp only [value_mul]
  exact _root_.mul_assoc _ _ _

theorem one_mul (x : ReesQuotient F) : mul one x = x := by
  apply eq_of_value_eq
  simp only [value_mul]
  simp [one, value, mk, ReesTerm.one]

theorem mul_one (x : ReesQuotient F) : mul x one = x := by
  apply eq_of_value_eq
  simp only [value_mul]
  simp [one, value, mk, ReesTerm.one]

theorem mul_add (x y z : ReesQuotient F) :
    mul x (add y z) = add (mul x y) (mul x z) := by
  apply eq_of_value_eq
  simp only [value_mul, value_add]
  exact _root_.mul_add _ _ _

theorem add_mul (x y z : ReesQuotient F) :
    mul (add x y) z = add (mul x z) (mul y z) := by
  apply eq_of_value_eq
  simp only [value_mul, value_add]
  exact _root_.add_mul _ _ _

end ReesQuotient

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.ReesQuotient.add
#print axioms SymplecticStafford.Filtered.ReesQuotient.mul
#print axioms SymplecticStafford.Filtered.ReesQuotient.add_assoc
#print axioms SymplecticStafford.Filtered.ReesQuotient.mul_add
#print axioms SymplecticStafford.Filtered.ReesQuotient.reindex_mk
