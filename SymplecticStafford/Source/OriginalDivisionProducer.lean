module

public import SymplecticStafford.Source.DivisionLLDList
public import SymplecticStafford.Source.OriginalTestContract
public import SymplecticStafford.FiniteLength.PencilBridge

@[expose] public section

/-!
# Original-`U` source production from bridged division tests

`OriginalTestContract` intentionally leaves each local generation predicate
unconstrained.  This file supplies the exact additional M06 input needed by
the finite division-coefficient argument: every local test carries a nonzero
coefficient and a theorem that a nonzero affine pencil passes that test.

The finite-root selector from `DivisionLLDList` then constructs one literal
multiplier `H : U` for the whole finite list.  The output retains the original
local-test predicates, integer offsets, nonzero right tails, and admissibility
at the common divisor.  No source witness is supplied; only the local pencil
bridges are supplied.  The theorem remains conditional on those bridges and
does not claim they follow from finite length or localization metadata.
-/

namespace SymplecticStafford.Source

universe u v w

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

/-!
The preceding `OriginalDivisionTest` interface accepts a local pencil bridge
as a field.  The following data instead exposes the actual finite division
ring top and the original-U map into its module.  This is the strongest
source-selection theorem available without constructing those data from a
filtered quantum algebra.
-/

structure ActualOriginalDivisionTest
    (U : Type u) (K : Type v) (LocalizationData : Type w)
    (CyclicModuleData : Type*) (R M I : Type*) (D : I → Type*)
    [DivisionRing U] [Field K] [Ring R] [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module K M] [∀ i, DivisionRing (D i)]
    (ι : K →+* U) (ιmap : (i : I) → K →+* D i) where
  localTest : OriginalLocalTest U LocalizationData CyclicModuleData
  bridge : SymplecticStafford.FiniteLength.CyclicTopBridge
    (R := R) (M := M) ιmap
  sourceMap : U →+ M
  sourceMap_scalar : ∀ (z : K) (x : U),
    sourceMap (ι z * x) = z • sourceMap x
  passes_iff_cyclic : ∀ source : U,
    localTest.Passes source ↔
      SymplecticStafford.FiniteLength.RightCyclic
        (R := R) (sourceMap source)

/- A finite central-linear combination of original-U directions.  The
coefficient is always on the left of each direction, matching the paper's
right-action convention. -/
def weightedCombination (ι : K →+* U) (directions : List U)
    (coefficients : List K) : U :=
  (directions.zipWith (fun h z => ι z * h) coefficients).sum

namespace ActualOriginalDivisionTest

variable {LocalizationData : Type w} {CyclicModuleData : Type*}
variable {R M I : Type*} {D : I → Type*}
variable [Ring R] [AddCommGroup M]
variable [Module Rᵐᵒᵖ M] [Module K M] [∀ i, DivisionRing (D i)]
variable [Fintype I] [DecidableEq I]
variable {ι : K →+* U} {ιmap : (i : I) → K →+* D i}

theorem sourceMap_affine
    (t : ActualOriginalDivisionTest U K LocalizationData CyclicModuleData
      R M I D ι ιmap) (B a : U) (z : K) :
    t.sourceMap (B + ι z * a) =
      t.sourceMap B + z • t.sourceMap a := by
  rw [map_add, t.sourceMap_scalar]

theorem actual_bad_subset_top_bad
    (t : ActualOriginalDivisionTest U K LocalizationData CyclicModuleData
      R M I D ι ιmap) (B a : U)
    (hinitial : ∀ i, t.bridge.top (t.sourceMap B) i ≠ 0)
    (hιmap : ∀ i, Function.Injective (ιmap i)) :
    Set.Finite {z : K |
      ¬ SymplecticStafford.FiniteLength.RightCyclic
        (R := R) (t.sourceMap (B + ι z * a))} := by
  have htop := t.bridge.finite_nongenerating_scalars
    hιmap (t.sourceMap B) (t.sourceMap a) hinitial
  apply htop.subset
  intro z hz
  change ¬ SymplecticStafford.FiniteLength.RightCyclic
    (R := R) (t.sourceMap (B + ι z * a)) at hz
  change ¬ SymplecticStafford.FiniteLength.RightCyclic
    (R := R) (t.sourceMap B + z • t.sourceMap a)
  rw [t.sourceMap_affine B a z] at hz
  exact hz

end ActualOriginalDivisionTest

/-!
The finite-list assembly below derives the local pencil exceptions from the
actual top bridge.  Unlike `exists_original_affine_source_of_bridged_list`,
its hypotheses contain no `passes_of_pencil_ne_zero` source-selection field.
The only local input is the finite division-ring top comparison together with
the original-U additive map and its central-scalar compatibility.
-/

theorem exists_original_affine_source_of_actual_list
    {LocalizationData : Type w} {CyclicModuleData : Type*}
    {R M I : Type*} {D : I → Type*}
    [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module K M]
    [∀ i, DivisionRing (D i)] [Fintype I] [DecidableEq I]
    (ι : K →+* U) (hι : Function.Injective ι)
    (ιmap : (i : I) → K →+* D i)
    (hιmap : ∀ i, Function.Injective (ιmap i))
    (d : U)
    (tests : List (ActualOriginalDivisionTest U K LocalizationData
      CyclicModuleData R M I D ι ιmap))
    (B a : U) (ha : a ≠ 0)
    (hadmissible : ∀ t, t ∈ tests → t.localTest.Admissible d)
    (hinitial : ∀ t, t ∈ tests →
      ∀ i, t.bridge.top (t.sourceMap B) i ≠ 0) :
    ∃ (H source : U),
      source = B + H * a ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests → t.localTest.Admissible d) ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.localTest.rightTail ≠ 0) := by
  let bad : ActualOriginalDivisionTest U K LocalizationData
      CyclicModuleData R M I D ι ιmap → Set K := fun t =>
    {z | ¬ SymplecticStafford.FiniteLength.RightCyclic
      (R := R) (t.sourceMap (B + ι z * a))}
  have hbad : ∀ (t : ActualOriginalDivisionTest U K LocalizationData
      CyclicModuleData R M I D ι ιmap), t ∈ tests → (bad t).Finite := by
    intro t ht
    exact ActualOriginalDivisionTest.actual_bad_subset_top_bad t B a
      (hinitial t ht) hιmap
  have finite_union : ∀ (xs : List (ActualOriginalDivisionTest U K
      LocalizationData CyclicModuleData R M I D ι ιmap)),
      (∀ t, t ∈ xs → (bad t).Finite) →
        Set.Finite {z : K | ∃ t ∈ xs, z ∈ bad t} := by
    intro xs
    induction xs with
    | nil => intro _; simp
    | cons t ts ih =>
        intro h
        have ht : (bad t).Finite := h t (by simp)
        have hts : Set.Finite {z : K | ∃ t' ∈ ts, z ∈ bad t'} :=
          ih (fun t' ht' => h t' (by simp [ht']))
        have hsplit : {z : K | ∃ t' ∈ t :: ts, z ∈ bad t'} =
            bad t ∪ {z : K | ∃ t' ∈ ts, z ∈ bad t'} := by
          ext z
          simp [bad]
        rw [hsplit]
        exact ht.union hts
  have hbadlist : Set.Finite {z : K | ∃ t ∈ tests, z ∈ bad t} :=
    finite_union tests hbad
  have hsource : Set.Finite {z : K | B + ι z * a = 0} :=
    finite_affine_source_roots ι hι B a ha
  have hall : ({z : K | ∃ t ∈ tests, z ∈ bad t} ∪
      {z : K | B + ι z * a = 0}).Finite := hbadlist.union hsource
  obtain ⟨z, hz⟩ := Set.infinite_univ.exists_notMem_finite hall
  let H : U := ι z
  let source : U := B + H * a
  have hsource_ne : source ≠ 0 := by
    intro hs
    apply hz.2
    right
    change B + ι z * a = 0
    simpa [source, H] using hs
  have hcyclic : ∀ t, t ∈ tests →
      SymplecticStafford.FiniteLength.RightCyclic (R := R)
        (t.sourceMap source) := by
    intro t ht
    by_contra hbad_t
    apply hz.2
    left
    exact ⟨t, ht, hbad_t⟩
  refine ⟨H, source, ?_, hsource_ne, hadmissible, ?_, ?_⟩
  · rfl
  · intro t ht
    apply (t.passes_iff_cyclic source).2
    exact hcyclic t ht
  · intro t ht
    exact t.localTest.rightTail_nonzero

/-!
The one-pencil theorem above is sufficient for a single affine direction.  A
finite direction list is the paper's actual LLD shape: at each stage one
central scalar is selected from the original field, and the resulting
coefficient is an explicit finite sum in `U`.  No source witness is supplied;
only the exposed top coordinates and original-U maps are used.
-/

theorem exists_original_affine_source_of_actual_directions
    {LocalizationData : Type w} {CyclicModuleData : Type*}
    {R M I : Type*} {D : I → Type*}
    [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module K M]
    [∀ i, DivisionRing (D i)] [Fintype I] [DecidableEq I]
    (ι : K →+* U) (hι : Function.Injective ι)
    (ιmap : (i : I) → K →+* D i)
    (hιmap : ∀ i, Function.Injective (ιmap i))
    (d : U)
    (tests : List (ActualOriginalDivisionTest U K LocalizationData
      CyclicModuleData R M I D ι ιmap))
    (directions : List U) (B a : U) (hB : B ≠ 0) (ha : a ≠ 0)
    (hadmissible : ∀ t, t ∈ tests → t.localTest.Admissible d)
    (hinitial : ∀ t, t ∈ tests →
      ∀ i, t.bridge.top (t.sourceMap B) i ≠ 0) :
    ∃ (H source : U) (coefficients : List K),
      source = B + H * a ∧ source ≠ 0 ∧
      coefficients.length = directions.length ∧
      H = weightedCombination ι directions coefficients ∧
      (∀ t, t ∈ tests → t.localTest.Admissible d) ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.localTest.rightTail ≠ 0) := by
  let topGood : U → Prop := fun x =>
    ∀ t, t ∈ tests → ∀ i, t.bridge.top (t.sourceMap x) i ≠ 0
  let topBad : ActualOriginalDivisionTest U K LocalizationData
      CyclicModuleData R M I D ι ιmap → U → U → Set K := fun t x q =>
    {z | ∃ i, t.bridge.top (t.sourceMap x) i +
      ιmap i z * t.bridge.top (t.sourceMap q) i = 0}
  have finite_bad_union : ∀
      (xs : List (ActualOriginalDivisionTest U K LocalizationData
        CyclicModuleData R M I D ι ιmap)) (x q : U),
      (∀ t, t ∈ xs → ∀ i, t.bridge.top (t.sourceMap x) i ≠ 0) →
      Set.Finite {z : K | ∃ t ∈ xs, z ∈ topBad t x q} := by
    intro xs
    induction xs with
    | nil => intro x q _; simp
    | cons t ts ih =>
        intro x q hgood
        have ht : (topBad t x q).Finite := by
          exact SymplecticStafford.FiniteLength.finite_pencil_exceptions
            (fun i => ιmap i)
            (fun i => t.bridge.top (t.sourceMap x) i)
            (fun i => t.bridge.top (t.sourceMap q) i)
            (hgood t (by simp) ) (fun i => hιmap i)
        have hts : Set.Finite {z : K | ∃ t' ∈ ts, z ∈ topBad t' x q} :=
          ih x q (fun t' ht' => hgood t' (by simp [ht']))
        have hsplit : {z : K | ∃ t' ∈ t :: ts, z ∈ topBad t' x q} =
            topBad t x q ∪ {z : K | ∃ t' ∈ ts, z ∈ topBad t' x q} := by
          ext z
          simp [topBad]
        rw [hsplit]
        exact ht.union hts
  have go : ∀ (dirs : List U) (H x : U),
      x = B + H * a → x ≠ 0 → topGood x →
      ∃ (coefficients : List K) (H' x' : U),
        coefficients.length = dirs.length ∧ x' = B + H' * a ∧
        x' ≠ 0 ∧ topGood x' ∧
        H' = H + weightedCombination ι dirs coefficients := by
    intro dirs
    induction dirs with
    | nil =>
        intro H x hx hxne hgood
        refine ⟨[], H, x, by simp, hx, hxne, hgood, ?_⟩
        simp [weightedCombination]
    | cons h hs ih =>
        intro H x hx hxne hgood
        let q : U := h * a
        have htopbad : Set.Finite {z : K | ∃ t ∈ tests, z ∈ topBad t x q} :=
          finite_bad_union tests x q (fun t ht => hgood t ht)
        have hroots : Set.Finite {z : K | x + ι z * q = 0} := by
          by_cases hq : q = 0
          · have hempty : {z : K | x + ι z * q = 0} = (∅ : Set K) := by
              ext z
              simp [hq, hxne]
            rw [hempty]
            exact Set.finite_empty
          · exact finite_affine_source_roots ι hι x q hq
        have hall : ({z : K | ∃ t ∈ tests, z ∈ topBad t x q} ∪
            {z : K | x + ι z * q = 0}).Finite := htopbad.union hroots
        obtain ⟨z, hz⟩ := Set.infinite_univ.exists_notMem_finite hall
        let H1 : U := H + ι z * h
        let x1 : U := x + ι z * q
        have hx1 : x1 = B + H1 * a := by
          dsimp [x1, H1, q]
          rw [hx]
          noncomm_ring
        have hx1ne : x1 ≠ 0 := by
          intro hzero
          apply hz.2
          right
          exact hzero
        have hgood1 : topGood x1 := by
          intro t ht i
          have htop : t.bridge.top (t.sourceMap x1) i =
              t.bridge.top (t.sourceMap x) i +
                ιmap i z * t.bridge.top (t.sourceMap q) i := by
            rw [show t.sourceMap x1 = t.sourceMap x + z • t.sourceMap q by
              dsimp [x1]
              rw [map_add, t.sourceMap_scalar]]
            calc
              t.bridge.top (t.sourceMap x + z • t.sourceMap q) i =
                  (t.bridge.top (t.sourceMap x) +
                    t.bridge.top (z • t.sourceMap q)) i := by rw [map_add]
              _ = t.bridge.top (t.sourceMap x) i +
                    t.bridge.top (z • t.sourceMap q) i := rfl
              _ = t.bridge.top (t.sourceMap x) i +
                    ιmap i z * t.bridge.top (t.sourceMap q) i := by
                rw [t.bridge.map_smul]
          rw [htop]
          intro hzero
          apply hz.2
          left
          exact ⟨t, ht, ⟨i, hzero⟩⟩
        obtain ⟨coefficients, H', x', hlen, hx', hx'ne, hgood', hrel⟩ :=
          ih H1 x1 hx1 hx1ne hgood1
        refine ⟨z :: coefficients, H', x', ?_, hx', hx'ne, hgood', ?_⟩
        · simp [hlen]
        · rw [hrel]
          simp [weightedCombination]
          dsimp [H1]
          abel
  obtain ⟨coefficients, H, source, hlen, hsource, hsourcene, hgood, hrel⟩ :=
    go directions 0 B (by simp) hB (by
      intro t ht
      exact hinitial t ht)
  refine ⟨H, source, coefficients, hsource, hsourcene, hlen, ?_, hadmissible, ?_, ?_⟩
  · simpa using hrel
  · intro t ht
    apply (t.passes_iff_cyclic source).2
    apply t.bridge.reflects_generation
    apply SymplecticStafford.FiniteLength.semisimple_top_criterion _ |>.2
    exact hgood t ht
  · intro t ht
    exact t.localTest.rightTail_nonzero

/-- A local original-`U` test with its division-coefficient pencil bridge.

The bridge is quantified over every coefficient embedding and every affine
background/tail, so the selector may use one common embedding for all tests.
The original test remains a separate field, preserving its localization,
finite-length, canonical-generator, offset, and right-tail data. -/
structure OriginalDivisionTest
    (U : Type u) (K : Type v) (LocalizationData : Type w)
    (CyclicModuleData : Type*) [DivisionRing U] [Field K] where
  localTest : OriginalLocalTest U LocalizationData CyclicModuleData
  vCoeff : U
  uCoeff : U
  vCoeff_ne_zero : vCoeff ≠ 0
  passes_of_pencil_ne_zero :
    ∀ (ι : K →+* U) (B a : U) (z : K),
      vCoeff + ι z * uCoeff ≠ 0 →
        localTest.Passes (B + ι z * a)

namespace OriginalDivisionTest

variable {LocalizationData : Type w} {CyclicModuleData : Type*}

/-- Forgetful list item used by the generic finite-root selector.  The
generation predicate includes literal equality of the supplied offset and
right tail, so neither field is dropped by the adapter. -/
def toAffineDivisionTest
    (t : OriginalDivisionTest U K LocalizationData CyclicModuleData) :
    AffineDivisionTest U K where
  vCoeff := t.vCoeff
  uCoeff := t.uCoeff
  vCoeff_ne_zero := t.vCoeff_ne_zero
  offset := t.localTest.offset
  rightTail := t.localTest.rightTail
  rightTail_ne_zero := t.localTest.rightTail_nonzero
  passes := fun source gotOffset gotTail =>
    t.localTest.Passes source ∧
      gotOffset = t.localTest.offset ∧
      gotTail = t.localTest.rightTail
  passes_of_pencil_ne_zero := by
    intro ι B a z hp
    exact ⟨t.passes_of_pencil_ne_zero ι B a z hp, rfl, rfl⟩

theorem toAffineDivisionTest_passes
    (t : OriginalDivisionTest U K LocalizationData CyclicModuleData)
    (source : U) :
    (toAffineDivisionTest t).passes source
      (toAffineDivisionTest t).offset
      (toAffineDivisionTest t).rightTail ↔
      t.localTest.Passes source := by
  simp [toAffineDivisionTest]

end OriginalDivisionTest

/-!
The producer theorem is stated with the admissibility predicate from the
original contract.  Its arithmetic part is independent of those static
fields, but carrying the hypothesis and returning it makes the common
divisor/finite-list boundary explicit to downstream induction code.
-/
theorem exists_original_affine_source_of_bridged_list
    {LocalizationData : Type w} {CyclicModuleData : Type*}
    (ι : K →+* U) (hι : Function.Injective ι)
    (tests : List (OriginalDivisionTest U K LocalizationData CyclicModuleData))
    (d B a : U) (ha : a ≠ 0)
    (hadmissible : ∀ t, t ∈ tests → t.localTest.Admissible d) :
    ∃ (H source : U),
      source = B + H * a ∧
      (∀ t, t ∈ tests → t.localTest.Admissible d) ∧
      (∀ t, t ∈ tests → t.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.localTest.rightTail ≠ 0) := by
  let affineTests : List (AffineDivisionTest U K) :=
    tests.map OriginalDivisionTest.toAffineDivisionTest
  obtain ⟨H, source, hsource, hpasses, htails⟩ :=
    exists_original_affine_source_of_list ι hι affineTests B a
  refine ⟨H, source, hsource, hadmissible, ?_, ?_⟩
  · intro t ht
    have hmem : OriginalDivisionTest.toAffineDivisionTest t ∈ affineTests := by
      exact List.mem_map_of_mem ht
    have hp := hpasses (OriginalDivisionTest.toAffineDivisionTest t) hmem
    exact (OriginalDivisionTest.toAffineDivisionTest_passes t source).mp hp
  · intro t ht
    have hmem : OriginalDivisionTest.toAffineDivisionTest t ∈ affineTests := by
      exact List.mem_map_of_mem ht
    have htail := htails (OriginalDivisionTest.toAffineDivisionTest t) hmem
    exact htail

/-- Certified original-U source production with the source-zero exception
explicitly removed.  Every list member carries its own admissibility proof,
so callers cannot accidentally pass a test for a different divisor or omit
one of the localization/finite-length/canonical-generator certificates.
The conclusion retains the exact local predicates, offsets and right tails. -/
structure CertifiedOriginalDivisionTest
    (d : U) (LocalizationData : Type w) (CyclicModuleData : Type*)
    [DivisionRing U] [Field K] where
  test : OriginalDivisionTest U K LocalizationData CyclicModuleData
  admissible : test.localTest.Admissible d

theorem exists_original_affine_source_of_certified_list
    {LocalizationData : Type w} {CyclicModuleData : Type*}
    (ι : K →+* U) (hι : Function.Injective ι)
    (d : U)
    (tests : List (CertifiedOriginalDivisionTest
      (U := U) (K := K) d LocalizationData CyclicModuleData))
    (B a : U) (ha : a ≠ 0) :
    ∃ (H source : U),
      source = B + H * a ∧ source ≠ 0 ∧
      (∀ t, t ∈ tests → t.test.localTest.Admissible d) ∧
      (∀ t, t ∈ tests → t.test.localTest.Passes source) ∧
      (∀ t, t ∈ tests → t.test.localTest.rightTail ≠ 0) := by
  let rawTests : List (OriginalDivisionTest U K LocalizationData CyclicModuleData) :=
    tests.map (fun t => t.test)
  obtain ⟨H, source, hsource, hne, hpasses, htails⟩ :=
    exists_original_affine_source_of_list_nonzero ι hι
      (rawTests.map OriginalDivisionTest.toAffineDivisionTest) B a ha
  refine ⟨H, source, hsource, hne, ?_, ?_, ?_⟩
  · intro t ht
    exact t.admissible
  · intro t ht
    have hraw : t.test ∈ rawTests := List.mem_map_of_mem ht
    have hp := hpasses (OriginalDivisionTest.toAffineDivisionTest t.test)
      (List.mem_map_of_mem hraw)
    exact (OriginalDivisionTest.toAffineDivisionTest_passes t.test source).mp hp
  · intro t ht
    have hraw : t.test ∈ rawTests := List.mem_map_of_mem ht
    exact htails (OriginalDivisionTest.toAffineDivisionTest t.test)
      (List.mem_map_of_mem hraw)

end SymplecticStafford.Source

#print axioms
  SymplecticStafford.Source.OriginalDivisionTest.toAffineDivisionTest_passes
#print axioms SymplecticStafford.Source.ActualOriginalDivisionTest.sourceMap_affine
#print axioms SymplecticStafford.Source.ActualOriginalDivisionTest.actual_bad_subset_top_bad
#print axioms SymplecticStafford.Source.exists_original_affine_source_of_actual_list
#print axioms SymplecticStafford.Source.exists_original_affine_source_of_actual_directions
#print axioms SymplecticStafford.Source.exists_original_affine_source_of_bridged_list
#print axioms SymplecticStafford.Source.exists_original_affine_source_of_certified_list
