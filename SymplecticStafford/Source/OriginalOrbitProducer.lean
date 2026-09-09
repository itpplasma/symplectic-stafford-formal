import SymplecticStafford.FiniteLength.FiniteOrbitPencil
import SymplecticStafford.Source.OriginalDivisionProducer

/-!
# Original-​`U` source selection from finite orbit data

The minimal-prime finite-length bridge does not itself choose an original
source.  This file isolates a weaker, source-facing bridge than a split
finite-dimensional pencil: for each local test one supplies a finite orbit
basis for the cyclic image of the affine background.  The finite-orbit pencil
theorem then gives finitely many bad central scalars, and one scalar is chosen
simultaneously for a finite list and for the source-zero exception.

The source map, its scalar compatibility, and the equivalence between local
passage and actual right cyclicity are inherited from
`ActualOriginalDivisionTest`.  No localization, finite-length theorem, or
source-map surjectivity is inferred here; those are the inputs that a repaired
filtered/Rees construction must provide.  In particular, the result does not
claim a universal M06 producer.
-/

namespace SymplecticStafford.Source

open SymplecticStafford.FiniteLength
open Module

universe u v w x y z q

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

section Test

variable {LocalizationData : Type w} {CyclicModuleData : Type x}
variable {R M I : Type*} {D : I → Type*}
variable [Ring R] [AddCommGroup M]
variable [Module Rᵐᵒᵖ M] [Module K M]
variable [∀ i, DivisionRing (D i)] [Fintype I] [DecidableEq I]
variable {Q : Type q} [AddCommGroup Q] [Module K Q]

/- A local test together with an actual finite orbit description of its
   cyclic image.  The orbit basis is allowed to use the original opposite
   ring as its coefficient family, so no commutative replacement is made. -/
structure OriginalOrbitDivisionTest
    (U : Type u) (K : Type v) (LocalizationData : Type w)
    (CyclicModuleData : Type x) (R M I : Type*) (D : I → Type*)
    (Q : Type q)
    [DivisionRing U] [Field K] [Ring R] [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module K M]
    [∀ i, DivisionRing (D i)] [Fintype I] [DecidableEq I]
    [AddCommGroup Q] [Module K Q]
    (ι : K →+* U) (ιmap : (i : I) → K →+* D i) where
  actual : ActualOriginalDivisionTest U K LocalizationData CyclicModuleData
    R M I D ι ιmap
  top : M →ₗ[K] Q
  act : Rᵐᵒᵖ → Q →ₗ[K] Q
  top_cyclic_iff : ∀ m : M,
    RightCyclic (R := R) m ↔
      OrbitSpanTop act (top m)
  orbit_basis : ∀ m : M, RightCyclic (R := R) m →
    ∃ n : Nat, ∃ b : Basis (Fin n) K Q,
      ∃ c : Fin n → Rᵐᵒᵖ,
        ∀ i, act (c i) (top m) = b i

end Test

section Producer

variable {LocalizationData : Type w} {CyclicModuleData : Type x}
variable {R M I : Type*} {D : I → Type*}
variable [Ring R] [AddCommGroup M]
variable [Module Rᵐᵒᵖ M] [Module K M]
variable [∀ i, DivisionRing (D i)] [Fintype I] [DecidableEq I]
variable {Q : Type q} [AddCommGroup Q] [Module K Q]
variable {ι : K →+* U} {ιmap : (i : I) → K →+* D i}

namespace OriginalOrbitDivisionTest

/-- A finite-orbit top makes the bad scalars of one actual test finite when
the affine background already maps to a cyclic vector.  The source map is
still the literal original-​`U` additive map from `actual`; the orbit theorem
only acts on its image in the local top. -/
theorem finite_bad_scalars
    (t : OriginalOrbitDivisionTest U K LocalizationData CyclicModuleData
      R M I D Q ι ιmap)
    (B a : U)
    (hB : RightCyclic (R := R) (t.actual.sourceMap B)) :
    Set.Finite {z : K |
      ¬ t.actual.localTest.Passes (B + ι z * a)} := by
  have hbad := finite_nongenerating_scalars_of_finite_orbit_basis
    t.top t.act t.top_cyclic_iff t.orbit_basis
    (t.actual.sourceMap B) (t.actual.sourceMap a) hB
  apply hbad.subset
  intro z hz hpass
  apply hz
  apply (t.actual.passes_iff_cyclic _).mpr
  rw [t.actual.sourceMap_affine B a z]
  exact hpass

/- A finite list contributes only a finite union of the preceding bad sets.
   This is kept explicit so no finiteness of the test data is hidden in a
   typeclass or an index set. -/
theorem finite_bad_list
    (tests : List (OriginalOrbitDivisionTest U K LocalizationData
      CyclicModuleData R M I D Q ι ιmap))
    (B a : U)
    (hcyclic : ∀ t, t ∈ tests →
      RightCyclic (R := R) (t.actual.sourceMap B)) :
    Set.Finite {z : K | ∃ t ∈ tests,
      ¬ t.actual.localTest.Passes (B + ι z * a)} := by
  have hbad : ∀ t : OriginalOrbitDivisionTest U K LocalizationData
      CyclicModuleData R M I D Q ι ιmap, t ∈ tests →
      Set.Finite {z : K |
        ¬ t.actual.localTest.Passes (B + ι z * a)} := by
    intro t ht
    exact t.finite_bad_scalars B a (hcyclic t ht)
  have finite_union : ∀ (xs : List (OriginalOrbitDivisionTest U K
      LocalizationData CyclicModuleData R M I D Q ι ιmap)),
      (∀ t, t ∈ xs → Set.Finite {z : K |
        ¬ t.actual.localTest.Passes (B + ι z * a)}) →
      Set.Finite {z : K | ∃ t ∈ xs,
        ¬ t.actual.localTest.Passes (B + ι z * a)} := by
    intro xs
    induction xs with
    | nil => intro _; simp
    | cons t ts ih =>
        intro hfinite
        have ht : Set.Finite {z : K |
            ¬ t.actual.localTest.Passes (B + ι z * a)} :=
          hfinite t (by simp)
        have hts : Set.Finite {z : K | ∃ t' ∈ ts,
            ¬ t'.actual.localTest.Passes (B + ι z * a)} := by
          apply ih
          intro t' ht'
          exact hfinite t' (by simp [ht'])
        have hsplit : {z : K | ∃ t' ∈ t :: ts,
            ¬ t'.actual.localTest.Passes (B + ι z * a)} =
            {z : K | ¬ t.actual.localTest.Passes (B + ι z * a)} ∪
              {z : K | ∃ t' ∈ ts,
                ¬ t'.actual.localTest.Passes (B + ι z * a)} := by
          ext z
          simp
        rw [hsplit]
        exact ht.union hts
  exact finite_union tests hbad

/-!
The source selector is the weakest finite-orbit bridge used in this
workstream.  It requires cyclicity of the image of the affine background for
each test, not a split finite-dimensional pencil or a pre-built source
witness.  It retains the original divisor, offsets, tails, and the exact
ordered affine source `B + H * a`.
-/
theorem exists_original_affine_source_of_finite_orbit_list
    (ι : K →+* U) (hι : Function.Injective ι)
    (tests : List (OriginalOrbitDivisionTest U K LocalizationData
      CyclicModuleData R M I D Q ι ιmap))
    (d B a : U) (ha : a ≠ 0)
    (hadmissible : ∀ t, t ∈ tests → t.actual.localTest.Admissible d)
    (hcyclic : ∀ t, t ∈ tests →
      RightCyclic (R := R) (t.actual.sourceMap B)) :
    ∃ (H source : U),
      source = B + H * a ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests → t.actual.localTest.Admissible d) ∧
      (∀ t, t ∈ tests → t.actual.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.actual.localTest.rightTail ≠ 0) := by
  have hbad := finite_bad_list (ι := ι) tests B a hcyclic
  have hsource : Set.Finite {z : K | B + ι z * a = 0} :=
    finite_affine_source_roots ι hι B a ha
  have hall : ({z : K | ∃ t ∈ tests,
      ¬ t.actual.localTest.Passes (B + ι z * a)} ∪
      {z : K | B + ι z * a = 0}).Finite := hbad.union hsource
  obtain ⟨z, hz⟩ := Set.infinite_univ.exists_notMem_finite hall
  let H : U := ι z
  let source : U := B + H * a
  have hsource_ne : source ≠ 0 := by
    intro hs
    apply hz.2
    right
    change B + ι z * a = 0
    simpa [source, H] using hs
  have hpasses : ∀ t, t ∈ tests →
      t.actual.localTest.Passes source := by
    intro t ht
    by_contra hbad_t
    apply hz.2
    left
    exact ⟨t, ht, by simpa [source, H] using hbad_t⟩
  refine ⟨H, source, ?_, hsource_ne, hadmissible, hpasses, ?_⟩
  · rfl
  · intro t ht
    exact t.actual.localTest.rightTail_nonzero

end OriginalOrbitDivisionTest

end Producer

end SymplecticStafford.Source
