module

public import SymplecticStafford.FiniteLength.ActivatedPencil
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Tactic.NormNum

@[expose] public section

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

section ActivatedRepeatedMatrixReplay

/-! A repeated 2-by-2 block replay.  The top is a finite family of scalar
blocks, while the cyclic bridge is checked independently in the regular
right rational module.  The final conjunct is the ordered activated relation,
not merely a commutative rearrangement of it. -/

abbrev Block := Matrix (Fin 2) (Fin 2) ℚ

noncomputable def scalarBlockTop : ℚ →+ ((j : Fin 2) → Block) :=
  { toFun := fun x _ => x • (1 : Block)
    map_zero' := by funext j; simp
    map_add' := by intro x y; funext j; simp [add_smul] }

noncomputable def scalarBlockAction (r m : ℚ) : ℚ := m * r

example : ∃ k : ℚ, k ∉ ({0, 1, -2 / 3} : Set ℚ) ∧
    rational_right_cyclic (1 + k • (2 : ℚ)) ∧
    scalarBlockAction 0 (1 + k • (2 : ℚ)) +
        k • scalarBlockAction 3 (1 : ℚ) = k • (3 : ℚ) := by
  let ιmap : (j : Fin 2) → (i : Fin 2) → ℚ →+* ℚ := fun _ _ => RingHom.id ℚ
  have hgen : ∀ (x : ℚ),
      (∀ j : Fin 2, MatrixTopGenerator (scalarBlockTop x j)) →
        rational_right_cyclic x := by
    intro x hx
    apply (rational_right_cyclic_iff x).2
    intro hxzero
    have hdet : Matrix.det (scalarBlockTop x (0 : Fin 2)) ≠ 0 :=
      (matrix_top_generator_iff _).1 (hx 0)
    apply hdet
    simp [scalarBlockTop, hxzero]
  have hdet : ∀ j : Fin 2,
      Matrix.det (scalarBlockTop (1 : ℚ) j) ≠ 0 := by
    intro j
    simp [scalarBlockTop]
  obtain ⟨k, hk, hcyc, hrel⟩ := exists_activated_matrix_right_cyclic_avoiding
    (R := ℚ) (M := ℚ) (K := ℚ) (J := Fin 2) (r := 2)
    scalarBlockTop
    (by intro z m j; simp [scalarBlockTop, smul_smul])
    (by
      intro m hm
      exact hgen m (fun j => by simpa using hm j))
    scalarBlockAction
    (by intro r x y; dsimp [scalarBlockAction]; ring)
    (by intro k m r; dsimp [scalarBlockAction]; ring)
    (1 : ℚ) (2 : ℚ) (3 : ℚ) (3 : ℚ) (0 : ℚ)
    (by norm_num [scalarBlockAction]) (by norm_num [scalarBlockAction])
    hdet ({0, 1, -2 / 3} : Set ℚ)
    (((Set.finite_singleton _).insert _).insert _)
  exact ⟨k, hk, hcyc, hrel⟩

end ActivatedRepeatedMatrixReplay

section ActivatedFiniteTopLiftReplay

/-! The same activated conclusion through the explicit one-step finite
top-lifting certificate, so the cyclicity bridge is not supplied as an opaque
hypothesis. -/

noncomputable def liftRatAction (r m : ℚ) : ℚ := m * r

theorem liftRatAction_add (r x y : ℚ) :
    liftRatAction r (x + y) = liftRatAction r x + liftRatAction r y := by
  dsimp [liftRatAction]
  ring

theorem liftRatCentral (k m r : ℚ) :
    liftRatAction r (k • m) = k • liftRatAction r m := by
  dsimp [liftRatAction]
  ring

noncomputable def oneLevelAt (x : ℚ) (hx : x ≠ 0) :
    FiniteTopLifting ℚ ℚ 1 x where
  level := fun i => if i = 0 then Set.univ else ({0} : Set ℚ)
  top := by simp
  terminal := by simp
  step := by
    intro i hi y hy
    have hi0 : i = 0 := by omega
    subst i
    refine ⟨y, ?_, ?_⟩
    · refine ⟨MulOpposite.op (y / x), ?_⟩
      change x * (y / x) = y
      field_simp [hx]
    · simp

example : ∃ z : ℚ, z ∉ ({0, 1, -2 / 3} : Set ℚ) ∧
    rational_right_cyclic (1 + z • (2 : ℚ)) ∧
    liftRatAction 0 (1 + z • (2 : ℚ)) +
        z • liftRatAction 3 (1 : ℚ) = z • (3 : ℚ) := by
  let ιmap : (j : Unit) → (i : Unit) → ℚ →+* ℚ := fun _ _ => RingHom.id ℚ
  apply exists_activated_right_cyclic_of_finite_top_lifting
    (R := ℚ) (M := ℚ) (K := ℚ) (J := Unit)
    (ι := fun _ : Unit => Unit) (D := fun _ _ => ℚ) ιmap rationalTop
    (fun _ _ _ _ => rfl)
    (by
      intro m hm
      have hm0 : m ≠ 0 := by
        intro hm0
        have htop0 := hm ()
        rw [hm0] at htop0
        exact (semisimple_top_criterion _).1 htop0 () (by simp)
      exact ⟨1, ⟨oneLevelAt m hm0⟩⟩)
    liftRatAction
    (by intro r x y; exact liftRatAction_add r x y)
    (by intro k m r; exact liftRatCentral k m r)
    (1 : ℚ) (2 : ℚ) (3 : ℚ) (3 : ℚ) (0 : ℚ)
    (by norm_num [liftRatAction]) (by norm_num [liftRatAction])
    (by intro _ _; norm_num [rationalTop])
    (by intro _ _ x y h; exact h)
    ({0, 1, -2 / 3} : Set ℚ)
    (((Set.finite_singleton _).insert _).insert _)

end ActivatedFiniteTopLiftReplay

end SymplecticStafford.FiniteLength
