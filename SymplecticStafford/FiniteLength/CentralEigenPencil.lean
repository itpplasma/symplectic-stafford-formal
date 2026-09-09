import SymplecticStafford.FiniteLength.FiniteCentralDivisionPencil
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

/-!
# Central eigenvalue separation over a division ring

The activated-pencil argument only needs finite dimension over the
endomorphism division ring.  It does not need that division ring to be finite
over the parameter field.  This file records the division-ring-linear part:
distinct central eigenvalues give independent eigenvectors.  The proof uses
an ordered product of central differences, so no commutative determinant or
finite `K`-dimension is hidden in the statement.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

variable {K : Type u} {E : Type v} {P : Type w}
variable [Field K] [DivisionRing E] [DecidableEq K]
variable [AddCommGroup P] [Module E P]

/-- Left multiplication by a central element, regarded as an `E`-linear map.
The explicit commutation hypothesis is essential for a left module over a
noncommutative division ring. -/
def centralScalarMap (c : E) (hc : ∀ a : E, c * a = a * c) : Module.End E P :=
  { toFun := fun x => c • x
    map_add' := fun x y => smul_add c x y
    map_smul' := fun a x => by
      rw [smul_smul, hc, ← smul_smul]
      rfl }

@[simp] theorem centralScalarMap_apply (c : E)
    (hc : ∀ a : E, c * a = a * c) (x : P) :
    centralScalarMap c hc x = c • x := rfl

variable (ι : K →+* E)
variable (hι : ∀ k : K, ∀ a : E, ι k * a = a * ι k)

/-- The central difference `f - ι(k)`. -/
def centralDifference (ι : K →+* E)
    (hι : ∀ k : K, ∀ a : E, ι k * a = a * ι k)
    (f : Module.End E P) (k : K) : Module.End E P :=
  f - centralScalarMap (ι k) (hι k)

@[simp] theorem centralDifference_apply (f : Module.End E P) (k : K) (x : P) :
    centralDifference ι hι f k x = f x - (ι k) • x := rfl

theorem centralDifference_map_smul (f : Module.End E P) (k : K)
    (a : E) (x : P) :
    centralDifference ι hι f k (a • x) = a • centralDifference ι hι f k x :=
  (centralDifference ι hι f k).map_smul a x

section Products

variable (f : Module.End E P)

/-- Ordered composition avoids the nonexistent commutative multiplication on
endomorphisms of a left module over a noncommutative ring. -/
def centralDifferenceList (ι : K →+* E)
    (hι : ∀ k : K, ∀ a : E, ι k * a = a * ι k)
    (f : Module.End E P) : List K → Module.End E P
  | [] => LinearMap.id
  | k :: ks => (centralDifference ι hι f k).comp
      (centralDifferenceList ι hι f ks)

theorem centralDifference_apply_eigen (k z : K) (x : P)
    (hx : f x = ι z • x) :
    centralDifference ι hι f k x = (ι z - ι k) • x := by
  rw [centralDifference_apply, hx, sub_smul]

theorem centralDifferenceList_apply_eigen_span (ks : List K)
    (z : K) (x : P) (hx : f x = ι z • x) :
    ∃ c : E, centralDifferenceList (ι := ι) (hι := hι) (f := f) ks x = c • x := by
  induction ks with
  | nil => exact ⟨1, by simp [centralDifferenceList]⟩
  | cons k ks ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c * (ι z - ι k), ?_⟩
      rw [centralDifferenceList, LinearMap.comp_apply, hc,
        centralDifference_map_smul,
        centralDifference_apply_eigen ι hι f k z x hx, smul_smul]

theorem centralDifferenceList_apply_eigen_nonzero (ks : List K)
    (z : K) (x : P) (hx0 : x ≠ 0) (hx : f x = ι z • x)
    (hz : ∀ k ∈ ks, ι z - ι k ≠ 0) :
    centralDifferenceList (ι := ι) (hι := hι) (f := f) ks x ≠ 0 := by
  induction ks with
  | nil => simpa [centralDifferenceList] using hx0
  | cons k ks ih =>
      have hzk : ι z - ι k ≠ 0 := hz k (by simp)
      have hzs : ∀ j ∈ ks, ι z - ι j ≠ 0 := by
        intro j hj
        exact hz j (by simp [hj])
      have hinner := ih hzs
      obtain ⟨c, hc⟩ := centralDifferenceList_apply_eigen_span
        ι hι f ks z x hx
      have hcz : c ≠ 0 := by
        intro hc0
        apply hinner
        rw [hc0, zero_smul] at hc
        exact hc
      rw [centralDifferenceList, LinearMap.comp_apply, hc,
        centralDifference_map_smul,
        centralDifference_apply_eigen ι hι f k z x hx, smul_smul]
      exact smul_ne_zero (mul_ne_zero hcz hzk) hx0

theorem centralDifferenceList_apply_eigen_zero_of_mem
    (ks : List K) (z : K) (x : P) (hx : f x = ι z • x)
    (hz : z ∈ ks) :
    centralDifferenceList (ι := ι) (hι := hι) (f := f) ks x = 0 := by
  induction ks with
  | nil => simp at hz
  | cons a ks ih =>
      rw [centralDifferenceList, LinearMap.comp_apply]
      by_cases hza : z = a
      · subst z
        obtain ⟨c, hc⟩ := centralDifferenceList_apply_eigen_span
          ι hι f ks a x hx
        rw [hc, centralDifference_map_smul,
          centralDifference_apply_eigen ι hι f a a x hx]
        simp
      · have hks : z ∈ ks := by simpa [hza] using hz
        rw [ih hks]
        simp

end Products

/- Distinct central eigenvalues admit no nontrivial finite relation. -/
include hι
theorem central_eigenvectors_linearIndependent_list
    (f : Module.End E P) (ks : List K) (x : K → P) (hnodup : ks.Nodup)
    (hx0 : ∀ k ∈ ks, x k ≠ 0)
    (hxeigen : ∀ k ∈ ks, f (x k) = ι k • x k) :
    LinearIndepOn E x (↑ks.toFinset : Set K) := by
  revert hx0 hxeigen
  induction ks with
  | nil =>
      intro _ _
      simp
  | cons a ks ih =>
      intro hx0 hxeigen
      rcases List.nodup_cons.mp hnodup with ⟨ha, htail⟩
      have hx0s : ∀ k ∈ ks, x k ≠ 0 := by
        intro k hk
        exact hx0 k (by simp [hk])
      have hxeigens : ∀ k ∈ ks, f (x k) = ι k • x k := by
        intro k hk
        exact hxeigen k (by simp [hk])
      have hs := ih htail hx0s hxeigens
      have hinsert : LinearIndepOn E x
          (insert a (↑ks.toFinset : Set K)) := by
        apply hs.insert'
        intro c hc
        have hzero : ∀ q : P, q ∈ Submodule.span E (x '' (↑ks.toFinset : Set K)) →
            centralDifferenceList ι hι f ks q = 0 := by
          intro q hq
          refine Submodule.span_induction (p := fun q _ =>
            centralDifferenceList ι hι f ks q = 0) ?_ ?_ ?_ ?_ hq
          · intro q hq
            rcases hq with ⟨k, hk, rfl⟩
            have hk' : k ∈ ks := by simpa using hk
            exact centralDifferenceList_apply_eigen_zero_of_mem
              ι hι f ks k (x k) (hxeigens k hk') hk'
          · simp
          · intro q r hq hr hq' hr'
            rw [map_add, hq', hr']
            simp
          · intro b q hq hq'
            rw [map_smul, hq', smul_zero]
        have hleft : centralDifferenceList ι hι f ks (c • x a) = 0 :=
          hzero _ hc
        obtain ⟨p, hpform⟩ := centralDifferenceList_apply_eigen_span
          ι hι f ks a (x a) (hxeigen a (by simp))
        have hp : p ≠ 0 := by
          have hpout := centralDifferenceList_apply_eigen_nonzero
            ι hι f ks a (x a) (hx0 a (by simp))
            (hxeigen a (by simp))
            (by
              intro k hk hzero'
              have hak : a = k :=
                (RingHom.injective ι) (sub_eq_zero.mp hzero')
              exact ha (by simpa [hak] using hk))
          intro hp0
          apply hpout
          rw [hpform, hp0, zero_smul]
        rw [map_smul, hpform, smul_smul] at hleft
        have hcp : c * p = 0 := by
          rcases smul_eq_zero.mp hleft with h | h
          · exact h
          · exact (hx0 a (by simp) h).elim
        exact (mul_eq_zero.mp hcp).resolve_right hp
      have hset : (↑(a :: ks).toFinset : Set K) =
          insert a (↑ks.toFinset : Set K) := by
        ext k
        simp [List.toFinset_cons]
      rw [hset]
      exact hinsert

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.central_eigenvectors_linearIndependent_list
