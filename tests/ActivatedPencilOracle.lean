import SymplecticStafford.FiniteLength.ActivatedPencil
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.NormNum

namespace SymplecticStafford.FiniteLength

/-! A concrete two-local-top replay.  The test exercises the existential
scalar conclusion and the right-cyclic bridge without adding axioms. -/

section ConcreteTop

variable {K : Type*} [Field K] [Infinite K]
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {ι : J → Type*} [∀ j, Fintype (ι j)]
variable [∀ j, DecidableEq (ι j)]
variable {D : (j : J) → ι j → Type*}
variable [∀ j i, DivisionRing (D j i)]
variable (ιmap : (j : J) → (i : ι j) → K →+* D j i)

example (v u : (j : J) → (i : ι j) → D j i)
    (hv : ∀ j i, v j i ≠ 0)
    (hinj : ∀ j i, Function.Injective (ιmap j i))
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K,
      z ∉ forbidden ∧
        ∀ j, TopGenerator (fun i => v j i + ιmap j i z * u j i) := by
  exact exists_simultaneous_top_generator_avoiding
    ιmap v u hv hinj forbidden hforbidden

end ConcreteTop

section ZModReplay

/-! A small finite-index replay over two local tops; the scalar field is still an
infinite field, so the generic-avoidance conclusion is non-vacuous. -/

abbrev K := ℚ
abbrev J := Fin 2
abbrev I (_ : J) := Fin 2
abbrev D (_ : J) (_ : Fin 2) := ℚ

noncomputable def ratMap (j : J) (i : Fin 2) : K →+* D j i := RingHom.id K

example (v u : (j : J) → (i : I j) → D j i)
    (hv : ∀ j i, v j i ≠ 0)
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K,
      z ∉ forbidden ∧
        ∀ j, TopGenerator (fun i => v j i + ratMap j i z * u j i) := by
  apply exists_simultaneous_top_generator_avoiding ratMap v u hv
    (fun _ _ x y h => h) forbidden hforbidden

end ZModReplay

section RightModuleReplay

/-! The same argument is consumed by an actual right cyclic module.  The
coordinate-to-cyclicity implication is proved directly for `ℚ`, rather than
being packaged as data in the generic theorem. -/

def rational_right_cyclic (x : ℚ) : Prop :=
  ∀ y : ℚ, ∃ r : ℚᵐᵒᵖ, r • x = y

theorem rational_right_cyclic_iff (x : ℚ) :
    rational_right_cyclic x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    obtain ⟨r, hr⟩ := h 1
    subst x
    simp at hr
  · intro hx y
    refine ⟨MulOpposite.op (x⁻¹ * y), ?_⟩
    change x * (x⁻¹ * y) = y
    simp [hx]

def rationalTop : ℚ →+ ((j : Unit) → (i : Unit) → ℚ) :=
  { toFun := fun x _ _ => x
    map_zero' := by funext j; funext i; simp
    map_add' := by intro x y; funext j; funext i; simp }

example : ∃ z : ℚ,
    z ∉ ({0, 1, -2 / 3} : Set ℚ) ∧
      rational_right_cyclic (2 + z • (3 : ℚ)) := by
  let ιmap : (j : Unit) → (i : Unit) → ℚ →+* ℚ := fun _ _ => RingHom.id ℚ
  have hgen : ∀ (x : ℚ),
      (∀ (_ : Unit), TopGenerator (fun (_ : Unit) => rationalTop x () ())) →
        rational_right_cyclic x := by
    intro x hx
    apply (rational_right_cyclic_iff x).2
    exact (semisimple_top_criterion _).1 (hx ()) ()
  obtain ⟨z, hz, hcyc⟩ := exists_simultaneous_right_cyclic_avoiding
    (R := ℚ) (M := ℚ) (K := ℚ) (J := Unit)
    (ι := fun _ : Unit => Unit) (D := fun _ _ => ℚ) ιmap rationalTop
    (fun _ _ _ _ => rfl) hgen (2 : ℚ) (3 : ℚ)
    (by intro _ _; norm_num [rationalTop])
    (fun _ _ => by intro x y h; exact h)
    ({0, 1, -2 / 3} : Set ℚ)
    (((Set.finite_singleton _).insert _).insert _)
  exact ⟨z, hz, hcyc⟩

end RightModuleReplay

end SymplecticStafford.FiniteLength
