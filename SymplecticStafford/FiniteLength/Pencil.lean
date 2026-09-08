import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.NoncommRing

/-! Finite semisimple tops and central pencils. -/

namespace SymplecticStafford.FiniteLength

section ProductTop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : ι → Type*} [∀ i, DivisionRing (D i)]

/-- Coordinatewise multiplication in the finite semisimple top. -/
def productMul (x y : ∀ i, D i) : ∀ i, D i := fun i => x i * y i

/-- A vector generates the product top if its right multiples contain every
coordinate vector. -/
def TopGenerator (x : ∀ i, D i) : Prop :=
  ∀ y : ∀ i, D i, ∃ z : ∀ i, D i, productMul x z = y

/-- A product-top generator is exactly a vector with nonzero simple
coordinates. -/
theorem semisimple_top_criterion (x : ∀ i, D i) :
    TopGenerator x ↔ ∀ i, x i ≠ 0 := by
  constructor
  · intro hx i hxi
    obtain ⟨z, hz⟩ := hx (fun j => if j = i then 1 else 0)
    have hi := congrFun hz i
    simp [productMul, hxi] at hi
  · intro hx y
    classical
    refine ⟨fun i => (x i)⁻¹ * y i, ?_⟩
    funext i
    simp [productMul, hx i]

end ProductTop

section Pencil

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {D : ι → Type*} [∀ i, DivisionRing (D i)]
variable (ιmap : (i : ι) → K →+* D i)
variable (hι : (i : ι) → Function.Injective (ιmap i))

private lemma root_subsingleton (i : ι) (v u : D i) (hv : v ≠ 0)
    (hinj : Function.Injective (ιmap i)) :
    Set.Subsingleton ({z | v + ιmap i z * u = 0} : Set K) := by
  intro z hz w hw
  by_cases hu : u = 0
  · subst u
    simp [hv] at hz
  · have hmul : (ιmap i z) * u = (ιmap i w) * u := by
      calc
        (ιmap i z) * u = (v + (ιmap i z) * u) - v := by noncomm_ring
        _ = 0 - v := by rw [hz]
        _ = (v + (ιmap i w) * u) - v := by rw [hw]
        _ = (ιmap i w) * u := by noncomm_ring
    have hmap : ιmap i z = ιmap i w :=
      mul_right_cancel₀ hu hmul
    exact hinj hmap

/-- Exceptional central scalars in a finite division-ring pencil form a
finite set. -/
theorem finite_pencil_exceptions (v u : ∀ i, D i)
    (hv : ∀ i, v i ≠ 0)
    (hinj : (i : ι) → Function.Injective (ιmap i)) :
    Set.Finite ({z | ∃ i, v i + ιmap i z * u i = 0} : Set K) := by
  classical
  have hsingle : ∀ i, Set.Finite ({z | v i + ιmap i z * u i = 0} : Set K) := by
    intro i
    by_cases hne :
        ({z | v i + ιmap i z * u i = 0} : Set K).Nonempty
    · obtain ⟨z, hz⟩ := hne
      apply Set.Finite.subset (Set.finite_singleton z)
      intro w hw
      have hzw : w = z := (root_subsingleton ιmap i (v i) (u i) (hv i) (hinj i) hz hw).symm
      simpa [hzw]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
  have hall : Set.Finite (⋃ i : ι, ({z | v i + ιmap i z * u i = 0} : Set K)) :=
    Set.finite_iUnion hsingle
  apply hall.subset
  intro z hz
  rcases hz with ⟨i, hi⟩
  exact Set.mem_iUnion.2 ⟨i, hi⟩

end Pencil

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.semisimple_top_criterion
#print axioms SymplecticStafford.FiniteLength.finite_pencil_exceptions
