import SymplecticStafford.Source.FiniteDimensionalProducer

/-!
# One-way finite-dimensional source selection

The finite split pencil only needs to certify that an injective pencil passes
the local test.  A converse is unnecessary: a local test may also pass at a
singular pencil, and those extra good scalars do not obstruct selection.  The
determinant argument still bounds every failing scalar by the finite singular
set.  This strictly weakens the bridge required by
`FiniteDimensionalProducer` while retaining the original-U source, ordered
offset/right-tail assertions, and source-zero avoidance.
-/

namespace SymplecticStafford.Source

universe u v w x y z

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

namespace FiniteDimensionalDivisionTest

variable {LocalizationData : Type w} {CyclicModuleData : Type x}
variable {P V : Type y} {J : Type z}
variable [AddCommGroup P] [Module K P] [FiniteDimensional K P]
variable [AddCommGroup V] [Module K V]
variable [Fintype J] [DecidableEq J]

/-- A one-way pass bridge suffices for finite bad-scalar control. -/
theorem finite_bad_scalars_of_injective
    (t : FiniteDimensionalDivisionTest U K LocalizationData CyclicModuleData
      P V J)
    (ι : K →+* U) (B a : U)
    (hpasses : ∀ z : K,
      Function.Injective (t.base B a + z • t.direction B a) →
        t.localTest.Passes (B + ι z * a)) :
    Set.Finite {z : K | ¬ t.localTest.Passes (B + ι z * a)} := by
  have hdet := SymplecticStafford.FiniteLength.finite_bad_of_split_central_pencil
    (K := K) (E := K) (V := V) (P := P)
    (block := fun z => t.block B a z)
    (base := t.base B a) (direction := t.direction B a)
    (retract := t.retract B a) (t.split B a)
    (t.realization B a)
  apply hdet.subset
  intro z hz
  intro hpass
  apply hz
  exact hpasses z ((t.realization B a z).mp hpass)

end FiniteDimensionalDivisionTest

theorem finite_bad_list_of_injective
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
      Function.Injective (t.base B a + z • t.direction B a) →
        t.localTest.Passes (B + ι z * a)) :
    Set.Finite {z : K | ∃ t ∈ tests,
      ¬ t.localTest.Passes (B + ι z * a)} := by
  have hbad : ∀ (t : FiniteDimensionalDivisionTest U K
      LocalizationData CyclicModuleData P V J), t ∈ tests →
      Set.Finite {z : K | ¬ t.localTest.Passes (B + ι z * a)} := by
    intro t ht
    exact t.finite_bad_scalars_of_injective ι B a (hpasses t ht)
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

/-! The source theorem intentionally mirrors only the final finite-union and
source-zero steps of the existing selector.  Its local bridge is one-way. -/
theorem exists_original_affine_source_of_finite_dimensional_list_of_injective
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
      Function.Injective (t.base B a + z • t.direction B a) →
        t.localTest.Passes (B + ι z * a)) :
    ∃ (H source : U),
      source = B + H * a ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests → t.localTest.Admissible d) ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.localTest.rightTail ≠ 0) := by
  have hbad := finite_bad_list_of_injective ι B a tests hpasses
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
  SymplecticStafford.Source.FiniteDimensionalDivisionTest.finite_bad_scalars_of_injective
#print axioms SymplecticStafford.Source.finite_bad_list_of_injective
#print axioms
  SymplecticStafford.Source.exists_original_affine_source_of_finite_dimensional_list_of_injective
