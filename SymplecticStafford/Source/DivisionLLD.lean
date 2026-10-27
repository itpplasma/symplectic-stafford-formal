module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic.NoncommRing
public import SymplecticStafford.FiniteLength.Pencil

@[expose] public section

/-!
# Conditional division-coefficient LLD and finite affine tests

This file isolates the finite scalar-selection part of M06.  A finite family
of local tests is indexed by a finite type.  Each test exposes a division-ring
coefficient pencil `v + ι(z) * u`; the left-linear-detection (LLD) condition
is proved from `v ≠ 0` and injectivity of the coefficient embedding.  An
infinite scalar field then supplies one scalar outside all exceptional roots.

The resulting source is literally in the original division ring, in the
ordered form `B + (ι z) * a`.  The module does not construct a localization,
finite-length module, admissible test family, or universal source producer:
those are explicit hypotheses of the test-family structure.  In particular,
this is a finite affine-selection lemma, not the full M06 theorem.
-/

namespace SymplecticStafford.Source

universe u v

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

/-!
The abstract family above deliberately accepts a local generation bridge.  The
following concrete family is the finite test/source result that does not need
that bridge: its tests record the source's nonvanishing together with their
literal offset and right-tail fields.  The source-zero pencil is included in
the forbidden set, so the result also works for an empty test family.
-/

structure NonzeroAffineTestFamily (U : Type u) (K : Type v)
    [DivisionRing U] [Field K] where
  Index : Type*
  fintype : Fintype Index
  ι : K →+* U
  ι_injective : Function.Injective ι
  offset : Index → Int
  rightTail : Index → U
  rightTail_ne_zero : ∀ i, rightTail i ≠ 0

namespace NonzeroAffineTestFamily

variable (T : NonzeroAffineTestFamily U K)

/-- The concrete generation predicate carried by each finite test. -/
def generation (i : T.Index) (source : U) (offset : Int) (rightTail : U) : Prop :=
  source ≠ 0 ∧ offset = T.offset i ∧ rightTail = T.rightTail i

theorem exists_original_affine_source
    (B a : U) (ha : a ≠ 0) :
    ∃ (H source : U),
      source = B + H * a ∧
      (∀ i, T.generation i source (T.offset i) (T.rightTail i)) ∧
      (∀ i, T.rightTail i ≠ 0) := by
  classical
  have hroot : Set.Finite {z : K | B + T.ι z * a = 0} := by
    have hone : ∀ ⦃z w : K⦄,
        B + T.ι z * a = 0 → B + T.ι w * a = 0 → z = w := by
      intro z w hz hw
      apply T.ι_injective
      apply mul_right_cancel₀ ha
      calc
        T.ι z * a = (B + T.ι z * a) - B := by noncomm_ring
        _ = 0 - B := by rw [hz]
        _ = (B + T.ι w * a) - B := by rw [hw]
        _ = T.ι w * a := by noncomm_ring
    by_cases hne : ({z : K | B + T.ι z * a = 0} : Set K).Nonempty
    · obtain ⟨z, hz⟩ := hne
      apply Set.Finite.subset (Set.finite_singleton z)
      intro w hw
      have hwz : w = z := hone hw hz
      simpa [hwz]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
  obtain ⟨z, -, hz⟩ := Set.infinite_univ.exists_notMem_finite hroot
  let H : U := T.ι z
  let source : U := B + H * a
  have hsource : source ≠ 0 := by
    intro hs
    apply hz
    change B + T.ι z * a = 0
    simpa [source, H] using hs
  refine ⟨H, source, ?_, ?_, T.rightTail_ne_zero⟩
  · rfl
  · intro i
    exact ⟨hsource, rfl, rfl⟩

end NonzeroAffineTestFamily

/-- A finite family of already-activated local tests.

`generation` retains the integer offset and the nonzero right tail.  The
field `generation_of_pencil_ne_zero` is the exact local bridge supplied by a
future division-coefficient/finite-length argument; it is not proved from a
syntactic predicate here.
-/
structure DivisionLLDTestFamily (U : Type u) (K : Type v)
    [DivisionRing U] [Field K] where
  Index : Type*
  fintype : Fintype Index
  ι : K →+* U
  ι_injective : Function.Injective ι
  vCoeff : Index → U
  uCoeff : Index → U
  vCoeff_ne_zero : ∀ i, vCoeff i ≠ 0
  offset : Index → Int
  rightTail : Index → U
  rightTail_ne_zero : ∀ i, rightTail i ≠ 0
  generation : Index → U → Int → U → Prop
  generation_of_pencil_ne_zero :
    ∀ (i : Index) (B a : U) (z : K),
      vCoeff i + ι z * uCoeff i ≠ 0 →
        generation i (B + (ι z) * a) (offset i) (rightTail i)

namespace DivisionLLDTestFamily

variable (T : DivisionLLDTestFamily U K)

/-- The exceptional scalar set for one test. -/
def exceptional (i : T.Index) : Set K :=
  {z | T.vCoeff i + T.ι z * T.uCoeff i = 0}

/-- Division cancellation gives the one-root property required by LLD. -/
theorem left_linear_detection (i : T.Index) :
    ∀ ⦃z w : K⦄,
      T.vCoeff i + T.ι z * T.uCoeff i = 0 →
      T.vCoeff i + T.ι w * T.uCoeff i = 0 → z = w := by
  intro z w hz hw
  by_cases hu : T.uCoeff i = 0
  · exfalso
    simpa [hu, T.vCoeff_ne_zero i] using hz
  · apply T.ι_injective
    apply mul_right_cancel₀ hu
    calc
      T.ι z * T.uCoeff i = (T.vCoeff i + T.ι z * T.uCoeff i) - T.vCoeff i := by
        noncomm_ring
      _ = 0 - T.vCoeff i := by rw [hz]
      _ = (T.vCoeff i + T.ι w * T.uCoeff i) - T.vCoeff i := by rw [hw]
      _ = T.ι w * T.uCoeff i := by noncomm_ring

/-- All exceptional scalars in the finite family form a finite set. -/
theorem finite_exceptional :
    Set.Finite (⋃ i : T.Index, T.exceptional i) := by
  classical
  letI := T.fintype
  have hsingle : ∀ i : T.Index, Set.Finite (T.exceptional i) := by
    intro i
    by_cases hne : (T.exceptional i).Nonempty
    · obtain ⟨z, hz⟩ := hne
      apply Set.Finite.subset (Set.finite_singleton z)
      intro w hw
      change T.vCoeff i + T.ι z * T.uCoeff i = 0 at hz
      change T.vCoeff i + T.ι w * T.uCoeff i = 0 at hw
      have hzw : w = z := (T.left_linear_detection i hz hw).symm
      simpa [hzw]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
  exact Set.finite_iUnion hsingle

/-- A scalar can be chosen outside every exceptional pencil root. -/
theorem exists_scalar_avoiding :
    ∃ z : K, z ∉ ⋃ i : T.Index, T.exceptional i := by
  classical
  obtain ⟨z, -, hz⟩ := Set.infinite_univ.exists_notMem_finite T.finite_exceptional
  exact ⟨z, hz⟩

/-- The selected scalar makes every pencil coefficient nonzero. -/
theorem selected_pencils_ne_zero {z : K}
    (hz : z ∉ ⋃ i : T.Index, T.exceptional i) :
    ∀ i, T.vCoeff i + T.ι z * T.uCoeff i ≠ 0 := by
  intro i hi
  apply hz
  exact Set.mem_iUnion.2 ⟨i, hi⟩

end DivisionLLDTestFamily

/-- One original-`U` affine source passing every supplied finite test. -/
theorem exists_original_affine_source
    (T : DivisionLLDTestFamily U K) (B a : U) :
    ∃ (H source : U),
      source = B + H * a ∧
      (∀ i, T.generation i source (T.offset i) (T.rightTail i)) ∧
      (∀ i, T.rightTail i ≠ 0) := by
  obtain ⟨z, hz⟩ := T.exists_scalar_avoiding
  let H : U := T.ι z
  let source : U := B + H * a
  have hp : ∀ i, T.vCoeff i + T.ι z * T.uCoeff i ≠ 0 :=
    T.selected_pencils_ne_zero hz
  refine ⟨H, source, ?_, ?_, ?_⟩
  · rfl
  · intro i
    simpa [H, source] using T.generation_of_pencil_ne_zero i B a z (hp i)
  · exact T.rightTail_ne_zero

end SymplecticStafford.Source

#print axioms SymplecticStafford.Source.DivisionLLDTestFamily.left_linear_detection
#print axioms SymplecticStafford.Source.DivisionLLDTestFamily.finite_exceptional
#print axioms SymplecticStafford.Source.exists_original_affine_source
