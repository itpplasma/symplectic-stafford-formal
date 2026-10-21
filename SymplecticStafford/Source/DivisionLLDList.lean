module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-!
# List-indexed division-coefficient LLD

`DivisionLLD.lean` packages the same finite-root argument with a finite type.
This file gives the paper-shaped list interface used by M06: each local test
keeps its own integer offset, nonzero right tail, and generation predicate.
The only supplied local bridge is that a nonzero pencil passes that test.  The
result therefore constructs one literal multiplier in the original division
ring for the whole list.  It does not construct the local tests or assert that
an admissible filtered algebra has such a list.
-/

namespace SymplecticStafford.Source

universe u v

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

structure AffineDivisionTest (U : Type u) (K : Type v)
    [DivisionRing U] [Field K] where
  vCoeff : U
  uCoeff : U
  vCoeff_ne_zero : vCoeff ≠ 0
  offset : Int
  rightTail : U
  rightTail_ne_zero : rightTail ≠ 0
  passes : U → Int → U → Prop
  passes_of_pencil_ne_zero :
    ∀ (ι : K →+* U) (B a : U) (z : K),
      vCoeff + ι z * uCoeff ≠ 0 →
        passes (B + ι z * a) offset rightTail

namespace AffineDivisionTest

variable (ι : K →+* U)

def exceptional (t : AffineDivisionTest U K) : Set K :=
  {z | t.vCoeff + ι z * t.uCoeff = 0}

theorem left_linear_detection (t : AffineDivisionTest U K) :
    (hι : Function.Injective ι) →
    ∀ ⦃z w : K⦄,
      t.vCoeff + ι z * t.uCoeff = 0 →
      t.vCoeff + ι w * t.uCoeff = 0 → z = w := by
  intro hι
  intro z w hz hw
  by_cases hu : t.uCoeff = 0
  · exfalso
    simpa [hu, t.vCoeff_ne_zero] using hz
  · apply hι
    apply mul_right_cancel₀ hu
    calc
      ι z * t.uCoeff = (t.vCoeff + ι z * t.uCoeff) - t.vCoeff := by
        noncomm_ring
      _ = 0 - t.vCoeff := by rw [hz]
      _ = (t.vCoeff + ι w * t.uCoeff) - t.vCoeff := by rw [hw]
      _ = ι w * t.uCoeff := by noncomm_ring

theorem finite_exceptional (t : AffineDivisionTest U K) :
    (hι : Function.Injective ι) →
    Set.Finite (t.exceptional ι) := by
  intro hι
  by_cases hne : (t.exceptional ι).Nonempty
  · obtain ⟨z, hz⟩ := hne
    apply Set.Finite.subset (Set.finite_singleton z)
    intro w hw
    change t.vCoeff + ι z * t.uCoeff = 0 at hz
    change t.vCoeff + ι w * t.uCoeff = 0 at hw
    have hwz : w = z := (t.left_linear_detection ι hι hz hw).symm
    simpa [hwz]
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

end AffineDivisionTest

/- The finite forbidden set for a list is stated as a set of scalars, rather
than as a finset of tests.  Thus no decidable equality or quotienting of local
test data is hidden in the source-selection theorem. -/
def affineExceptional (ι : K →+* U)
    (tests : List (AffineDivisionTest U K)) : Set K :=
  {z | ∃ t ∈ tests, t.vCoeff + ι z * t.uCoeff = 0}

theorem finite_affineExceptional (ι : K →+* U) (hι : Function.Injective ι)
    (tests : List (AffineDivisionTest U K)) :
    Set.Finite (affineExceptional ι tests) := by
  induction tests with
  | nil =>
      simp [affineExceptional]
  | cons t ts ih =>
      have ht : Set.Finite (t.exceptional ι) :=
        t.finite_exceptional ι hι
      have hsplit : affineExceptional ι (t :: ts) =
          t.exceptional ι ∪ affineExceptional ι ts := by
        ext z
        simp [affineExceptional, AffineDivisionTest.exceptional]
      rw [hsplit]
      exact ht.union ih

theorem exists_scalar_avoiding_affine (ι : K →+* U)
    (hι : Function.Injective ι)
    (tests : List (AffineDivisionTest U K)) :
    ∃ z : K, z ∉ affineExceptional ι tests := by
  obtain ⟨z, -, hz⟩ := Set.infinite_univ.exists_notMem_finite
    (finite_affineExceptional ι hι tests)
  exact ⟨z, hz⟩

/-- The zero members of an affine line with nonzero right tail form at most
one central scalar.  This is the source-level companion to the division
coefficient pencil calculation above.  In particular, the proof does not
commute `ι z` past `a`: cancellation is on the right, in the displayed
order `ι z * a`. -/
theorem finite_affine_source_roots (ι : K →+* U)
    (hι : Function.Injective ι) (B a : U) (ha : a ≠ 0) :
    Set.Finite {z : K | B + ι z * a = 0} := by
  have hsingle : Set.Subsingleton ({z : K | B + ι z * a = 0} : Set K) := by
    intro z hz w hw
    apply hι
    apply mul_right_cancel₀ ha
    calc
      ι z * a = (B + ι z * a) - B := by noncomm_ring
      _ = 0 - B := by rw [hz]
      _ = (B + ι w * a) - B := by rw [hw]
      _ = ι w * a := by noncomm_ring
  by_cases hne : ({z : K | B + ι z * a = 0} : Set K).Nonempty
  · obtain ⟨z, hz⟩ := hne
    apply Set.Finite.subset (Set.finite_singleton z)
    intro w hw
    have hwz : w = z := hsingle hz hw |>.symm
    simpa [hwz]
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

/-- Simultaneous scalar avoidance for all local division pencils, the affine
source-zero set, and any previously accumulated finite exceptional set. -/
theorem exists_scalar_avoiding_affine_and_source
    (ι : K →+* U) (hι : Function.Injective ι)
    (tests : List (AffineDivisionTest U K)) (B a : U) (ha : a ≠ 0)
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧ z ∉ affineExceptional ι tests ∧
      B + ι z * a ≠ 0 := by
  have hsource : Set.Finite {z : K | B + ι z * a = 0} :=
    finite_affine_source_roots ι hι B a ha
  have hpencils : Set.Finite (affineExceptional ι tests) :=
    finite_affineExceptional ι hι tests
  have hall : (forbidden ∪ affineExceptional ι tests ∪
      {z : K | B + ι z * a = 0}).Finite :=
    (hforbidden.union hpencils).union hsource
  obtain ⟨z, hz⟩ := Set.infinite_univ.exists_notMem_finite hall
  refine ⟨z, ?_, ?_, ?_⟩
  · exact fun h => hz.2 (Or.inl (Or.inl h))
  · exact fun h => hz.2 (Or.inl (Or.inr h))
  · exact fun h => hz.2 (Or.inr h)

/-- One original-U affine source simultaneously passes a finite list of
division-coefficient tests and is itself nonzero.  The latter condition is
not inferred from the local predicates: it is enforced by adding the actual
source-zero set to the same finite exceptional set. -/
theorem exists_original_affine_source_of_list_nonzero
    (ι : K →+* U) (hι : Function.Injective ι)
    (tests : List (AffineDivisionTest U K)) (B a : U) (ha : a ≠ 0) :
    ∃ (H source : U),
      source = B + H * a ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests →
        t.passes source t.offset t.rightTail) ∧
      (∀ t, t ∈ tests → t.rightTail ≠ 0) := by
  obtain ⟨z, _hnotzero_forbidden, hnotpencil, hnotzero⟩ :=
    exists_scalar_avoiding_affine_and_source ι hι tests B a ha ∅
      Set.finite_empty
  let H : U := ι z
  let source : U := B + H * a
  have hp : ∀ t, t ∈ tests → t.vCoeff + ι z * t.uCoeff ≠ 0 :=
    fun t ht hp => hnotpencil ⟨t, ht, hp⟩
  refine ⟨H, source, ?_, ?_, ?_, ?_⟩
  · rfl
  · simpa [H, source] using hnotzero
  · intro t ht
    simpa [H, source] using t.passes_of_pencil_ne_zero ι B a z (hp t ht)
  · intro t ht
    exact t.rightTail_ne_zero

theorem selected_pencils_ne_zero (ι : K →+* U)
    {tests : List (AffineDivisionTest U K)} {z : K}
    (hz : z ∉ affineExceptional ι tests) :
    ∀ t, t ∈ tests → t.vCoeff + ι z * t.uCoeff ≠ 0 := by
  intro t ht hp
  apply hz
  exact ⟨t, ht, hp⟩

/-- One source in the original `U`, with every supplied offset and tail
retained in the output test assertions. -/
theorem exists_original_affine_source_of_list
    (ι : K →+* U) (hι : Function.Injective ι)
    (tests : List (AffineDivisionTest U K)) (B a : U) :
    ∃ (H source : U),
      source = B + H * a ∧
      (∀ t, t ∈ tests →
        t.passes source t.offset t.rightTail) ∧
      (∀ t, t ∈ tests → t.rightTail ≠ 0) := by
  obtain ⟨z, hz⟩ := exists_scalar_avoiding_affine ι hι tests
  let H : U := ι z
  let source : U := B + H * a
  have hp : ∀ t, t ∈ tests → t.vCoeff + ι z * t.uCoeff ≠ 0 :=
    selected_pencils_ne_zero ι hz
  refine ⟨H, source, ?_, ?_, ?_⟩
  · rfl
  · intro t ht
    simpa [H, source] using t.passes_of_pencil_ne_zero ι B a z (hp t ht)
  · intro t ht
    exact t.rightTail_ne_zero

end SymplecticStafford.Source

#print axioms SymplecticStafford.Source.AffineDivisionTest.left_linear_detection
#print axioms SymplecticStafford.Source.finite_affineExceptional
#print axioms SymplecticStafford.Source.finite_affine_source_roots
#print axioms SymplecticStafford.Source.exists_original_affine_source_of_list_nonzero
#print axioms SymplecticStafford.Source.exists_original_affine_source_of_list
