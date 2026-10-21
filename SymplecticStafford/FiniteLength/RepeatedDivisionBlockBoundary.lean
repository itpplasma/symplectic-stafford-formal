module

public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

/-!
# Repeated division-block boundary for pencil finiteness

Finite length (or even finite generation over the endomorphism division ring)
does not make the bad parameters of an arbitrary repeated block pencil finite.
The missing input is an initially independent block, or an equivalent
determinant-free witness certificate.  This file records the obstruction on a
two-copy zero block.  It is valid for arbitrary division rings and therefore
does not hide a commutative determinant argument.
-/

namespace SymplecticStafford.FiniteLength

universe u v

section

variable {K : Type u} {E : Type v}
variable [Field K] [Infinite K] [DivisionRing E]

/-- A two-copy zero block is already a finite `E`-module, but is dependent for
every parameter.  Thus finite generation cannot replace the initial
independence hypothesis in a repeated division-ring pencil theorem. -/
theorem repeated_zero_block_bad_set_not_finite :
    Module.Finite E (E × E) ∧
      ¬ ({z : K | ¬ LinearIndependent E
        (fun _ : Fin 2 => (0 : E × E))}).Finite := by
  constructor
  · infer_instance
  · have hzero : ¬ LinearIndependent E
        (fun _ : Fin 2 => (0 : E × E)) := by
      intro h
      have hz := h.ne_zero (0 : Fin 2)
      exact hz (by simp)
    have hbad : {z : K | ¬ LinearIndependent E
        (fun _ : Fin 2 => (0 : E × E))} = Set.univ := by
      ext z
      simp [hzero]
    rw [hbad, Set.not_finite]
    exact Set.infinite_univ

/-- Even on the finite module `E × E`, no unconditional theorem may assert
that every repeated division-ring pencil has a finite bad set.  The scalar
map is kept explicit so this boundary applies to central embeddings as well.
-/
theorem no_unconditional_repeated_division_pencil_finiteness
    (ιmap : K →+* E) :
    ¬ (∀ (x y : Fin 2 → (E × E)), Set.Finite
      {z : K | ¬ LinearIndependent E
        (fun i => x i + (ιmap z) • y i)}) := by
  intro h
  let x : Fin 2 → (E × E) := fun _ => 0
  let y : Fin 2 → (E × E) := fun _ => 0
  have hbad := h x y
  have hbad0 : Set.Finite ({z : K | ¬ LinearIndependent E
      (fun _ : Fin 2 => (0 : E × E))}) := by
    simpa [x, y] using hbad
  exact (repeated_zero_block_bad_set_not_finite (K := K) (E := E)).2 hbad0

end

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.repeated_zero_block_bad_set_not_finite
#print axioms
  SymplecticStafford.FiniteLength.no_unconditional_repeated_division_pencil_finiteness
