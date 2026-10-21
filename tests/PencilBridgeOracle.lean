module

public import SymplecticStafford.FiniteLength.PencilBridge
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
Concrete independent oracle: in the regular right rational module the pencil
`2 + z * 3` fails to generate exactly at `-2/3`. The exceptional-set computation
uses division and linear arithmetic, independently of the generic finiteness
proof. No finite-length lifting theorem is used.
-/

namespace SymplecticStaffordTest.PencilBridge

open SymplecticStafford.FiniteLength

theorem rational_right_cyclic_iff (x : ℚ) :
    RightCyclic (R := ℚ) x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    obtain ⟨r, hr⟩ := h 1
    subst x
    simp at hr
  · intro hx y
    refine ⟨MulOpposite.op (x⁻¹ * y), ?_⟩
    change x * (x⁻¹ * y) = y
    simp [hx]

def rationalBridge : CyclicTopBridge (R := ℚ) (M := ℚ)
    (D := fun _ : Unit => ℚ) (fun _ => RingHom.id ℚ) where
  top :=
    { toFun := fun x _ => x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_smul := fun _ _ _ => rfl
  reflects_generation := by
    intro x hx
    apply (rational_right_cyclic_iff x).2
    exact (semisimple_top_criterion _).1 hx ()

example : {z : ℚ | ¬ RightCyclic (R := ℚ) (2 + z • (3 : ℚ))} =
    {(-2 / 3 : ℚ)} := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, rational_right_cyclic_iff,
    not_not, smul_eq_mul]
  constructor <;> intro h <;> linarith

example : Set.Finite {z : ℚ | ¬ RightCyclic (R := ℚ) (2 + z • (3 : ℚ))} := by
  apply rationalBridge.finite_nongenerating_scalars
  · intro i a b h
    exact h
  · intro i
    norm_num [rationalBridge]

example : ∃ z : ℚ, z ∉ ({0, 1, -2 / 3} : Set ℚ) ∧
    RightCyclic (R := ℚ) (2 + z • (3 : ℚ)) := by
  apply rationalBridge.exists_generating_scalar_avoiding
  · intro i a b h
    exact h
  · intro i
    norm_num [rationalBridge]
  · exact ((Set.finite_singleton _).insert _).insert _

/-- Independent explicit selected scalar and right-multiplier witness. -/
example : (2 : ℚ) ∉ ({0, 1, -2 / 3} : Set ℚ) ∧
    ∀ y : ℚ, (MulOpposite.op (y / 8)) • (2 + (2 : ℚ) • (3 : ℚ)) = y := by
  constructor
  · norm_num
  · intro y
    change (2 + 2 * 3 : ℚ) * (y / 8) = y
    ring

example : {z : ℚ | ¬ RightCyclic (R := ℚ) (2 + z • (0 : ℚ))} = ∅ := by
  ext z
  simp [rational_right_cyclic_iff]

end SymplecticStaffordTest.PencilBridge
