import SymplecticStafford.FiniteLength.CentralFinitePencil
import SymplecticStafford.Source.DivisionLLDList
import SymplecticStafford.Source.OriginalTestContract

/-!
# Finite-dimensional source selection from split pencils

This is a bounded positive M06 interface.  A local test supplies a split
finite-dimensional pencil over the central field.  The caller supplies the
identification of pencil injectivity with passage of the local test at the
chosen affine line.  The determinant argument then makes the bad scalars
finite, and one scalar is selected simultaneously for a finite list of tests
and for the actual source-zero set.

The resulting multiplier is `ι z : U`, so the source remains literally in the
original ring and has the ordered form `B + H * a`.  Offsets and right tails
remain in the `OriginalLocalTest.Passes` assertions and are returned with
their nonzero proofs.  No finite-dimensionality or algebraization of a
filtered quantum chart is inferred here: the split pencil and the local
passes/injectivity equivalences are explicit hypotheses.
-/

namespace SymplecticStafford.Source

universe u v w x y z

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

/- A test has a common finite-dimensional coefficient space `P`, a target
space `V`, and a finite block family indexed by `J`.  The maps may depend on
the affine background and tail; this permits a genuine local top comparison
without pretending that all tests share one pencil. -/
structure FiniteDimensionalDivisionTest
    (U : Type u) (K : Type v) (LocalizationData : Type w)
    (CyclicModuleData : Type x) (P V : Type y) (J : Type z)
    [DivisionRing U] [Field K]
    [AddCommGroup P] [Module K P] [FiniteDimensional K P]
    [AddCommGroup V] [Module K V]
    [Fintype J] [DecidableEq J] where
  localTest : OriginalLocalTest U LocalizationData CyclicModuleData
  block : U → U → K → J → V
  base : U → U → P →ₗ[K] V
  direction : U → U → P →ₗ[K] V
  retract : U → U → V →ₗ[K] P
  split : ∀ (B a : U),
    (retract B a).comp (base B a) = LinearMap.id
  realization : ∀ (B a : U) (z : K),
    LinearIndependent K (block B a z) ↔
      Function.Injective (base B a + z • direction B a)

namespace FiniteDimensionalDivisionTest

variable {LocalizationData : Type w} {CyclicModuleData : Type x}
variable {P V : Type y} {J : Type z}
variable [AddCommGroup P] [Module K P] [FiniteDimensional K P]
variable [AddCommGroup V] [Module K V]
variable [Fintype J] [DecidableEq J]

/-- The finite-dimensional split pencil bounds the scalars at which a local
test can fail, once its local pass predicate is identified with injectivity.
This is the exact finite top bridge consumed by the list selector below. -/
theorem finite_bad_scalars
    (t : FiniteDimensionalDivisionTest U K LocalizationData CyclicModuleData
      P V J)
    (ι : K →+* U) (B a : U)
    (hpasses : ∀ z : K,
      t.localTest.Passes (B + ι z * a) ↔
        Function.Injective (t.base B a + z • t.direction B a)) :
    Set.Finite {z : K | ¬ t.localTest.Passes (B + ι z * a)} := by
  have hdet := SymplecticStafford.FiniteLength.finite_bad_of_split_central_pencil
    (K := K) (E := K) (V := V) (P := P)
    (block := fun z => t.block B a z)
    (base := t.base B a) (direction := t.direction B a)
    (retract := t.retract B a) (t.split B a)
    (t.realization B a)
  apply hdet.subset
  intro z hz
  intro hli
  apply hz
  exact (hpasses z).mpr ((t.realization B a z).mp hli)

end FiniteDimensionalDivisionTest

/-! A finite union helper is kept local to the producer, so no finiteness of
the test data beyond its explicit list is hidden in an instance. -/
theorem finite_bad_list
    {LocalizationData : Type w} {CyclicModuleData : Type x}
    {P V : Type y} {J : Type z}
    [AddCommGroup P] [Module K P] [FiniteDimensional K P]
    [AddCommGroup V] [Module K V]
    [Fintype J] [DecidableEq J]
    (ι : K →+* U) (B a : U)
    (tests : List (FiniteDimensionalDivisionTest U K LocalizationData
      CyclicModuleData P V J))
    (hpasses : ∀ (t : FiniteDimensionalDivisionTest U K
      LocalizationData CyclicModuleData P V J), t ∈ tests → ∀ z : K,
      t.localTest.Passes (B + ι z * a) ↔
        Function.Injective (t.base B a + z • t.direction B a)) :
    Set.Finite {z : K | ∃ t ∈ tests,
      ¬ t.localTest.Passes (B + ι z * a)} := by
  have hbad : ∀ (t : FiniteDimensionalDivisionTest U K
      LocalizationData CyclicModuleData P V J), t ∈ tests →
      Set.Finite {z : K | ¬ t.localTest.Passes (B + ι z * a)} := by
    intro t ht
    exact t.finite_bad_scalars ι B a (hpasses t ht)
  have finite_union : ∀ (xs : List (FiniteDimensionalDivisionTest U K
      LocalizationData CyclicModuleData P V J)),
      (∀ t, t ∈ xs → Set.Finite {z : K |
        ¬ t.localTest.Passes (B + ι z * a)}) →
      Set.Finite {z : K | ∃ t ∈ xs,
        ¬ t.localTest.Passes (B + ι z * a)} := by
    intro xs
    induction xs with
    | nil => intro _; simp
    | cons t ts ih =>
        intro hfinite
        have ht : Set.Finite {z : K |
            ¬ t.localTest.Passes (B + ι z * a)} := hfinite t (by simp)
        have hts : Set.Finite {z : K | ∃ t' ∈ ts,
            ¬ t'.localTest.Passes (B + ι z * a)} := by
          apply ih
          intro t' ht'
          exact hfinite t' (by simp [ht'])
        have hsplit : {z : K | ∃ t' ∈ t :: ts,
            ¬ t'.localTest.Passes (B + ι z * a)} =
            {z : K | ¬ t.localTest.Passes (B + ι z * a)} ∪
              {z : K | ∃ t' ∈ ts,
                ¬ t'.localTest.Passes (B + ι z * a)} := by
          ext z
          simp
        rw [hsplit]
        exact ht.union hts
  exact finite_union tests hbad

/-! The source-zero roots are added to the same forbidden set.  Thus the
conclusion proves a nonzero original-U source even when local pass predicates
themselves do not mention source nonvanishing. -/
theorem exists_original_affine_source_of_finite_dimensional_list
    {LocalizationData : Type w} {CyclicModuleData : Type x}
    {P V : Type y} {J : Type z}
    [AddCommGroup P] [Module K P] [FiniteDimensional K P]
    [AddCommGroup V] [Module K V]
    [Fintype J] [DecidableEq J]
    (ι : K →+* U) (hι : Function.Injective ι)
    (d : U)
    (tests : List (FiniteDimensionalDivisionTest U K LocalizationData
      CyclicModuleData P V J))
    (B a : U) (ha : a ≠ 0)
    (hadmissible : ∀ t, t ∈ tests → t.localTest.Admissible d)
    (hpasses : ∀ (t : FiniteDimensionalDivisionTest U K
      LocalizationData CyclicModuleData P V J), t ∈ tests → ∀ z : K,
      t.localTest.Passes (B + ι z * a) ↔
        Function.Injective (t.base B a + z • t.direction B a)) :
    ∃ (H source : U),
      source = B + H * a ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests → t.localTest.Admissible d) ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.localTest.rightTail ≠ 0) := by
  have hbad := finite_bad_list ι B a tests hpasses
  have hsource : Set.Finite {z : K | B + ι z * a = 0} :=
    finite_affine_source_roots ι hι B a ha
  have hall : ({z : K | ∃ t ∈ tests,
      ¬ t.localTest.Passes (B + ι z * a)} ∪
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
  have hpasses_source : ∀ t, t ∈ tests → t.localTest.Passes source := by
    intro t ht
    by_contra hbad_t
    apply hz.2
    left
    exact ⟨t, ht, by simpa [source, H] using hbad_t⟩
  refine ⟨H, source, ?_, hsource_ne, hadmissible, hpasses_source, ?_⟩
  · rfl
  · intro t ht
    exact t.localTest.rightTail_nonzero

end SymplecticStafford.Source

#print axioms
  SymplecticStafford.Source.FiniteDimensionalDivisionTest.finite_bad_scalars
#print axioms SymplecticStafford.Source.finite_bad_list
#print axioms
  SymplecticStafford.Source.exists_original_affine_source_of_finite_dimensional_list
