module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.CharZero.Infinite
public import SymplecticStafford.Source.OriginalOrbitProducer

@[expose] public section

/- Independent behavioral oracle for the original-U finite-orbit selector. -/

namespace SymplecticStafford.Source.OriginalOrbitProducerOracle

open SymplecticStafford.FiniteLength
open SymplecticStafford.Source
open Module

abbrev K := ℚ

noncomputable def ratAct (r : ℚᵐᵒᵖ) : ℚ →ₗ[ℚ] ℚ :=
  { toFun := fun x => r.unop * x
    map_add' := by intro x y; ring
    map_smul' := by intro a x; dsimp; ring }

theorem rat_cyclic_iff_ne_zero (x : ℚ) :
    RightCyclic (R := ℚ) x ↔ x ≠ 0 := by
  constructor
  · intro hx hzero
    obtain ⟨r, hr⟩ := hx 1
    rw [hzero] at hr
    simp at hr
  · intro hx y
    refine ⟨MulOpposite.op (x⁻¹ * y), ?_⟩
    simpa using (show x * (x⁻¹ * y) = y by simp [hx])

theorem rat_orbit_span_iff (x : ℚ) :
    OrbitSpanTop ratAct x ↔ x ≠ 0 := by
  constructor
  · intro hx hzero
    subst x
    have hle : Submodule.span ℚ (Set.range (fun r : ℚᵐᵒᵖ => ratAct r 0)) ≤
        (⊥ : Submodule ℚ ℚ) := by
      apply Submodule.span_le.mpr
      rintro y ⟨r, rfl⟩
      simp [ratAct]
    have htopbot : (⊤ : Submodule ℚ ℚ) ≤ ⊥ := by
      rw [← hx]
      exact hle
    have honebot : (1 : ℚ) ∈ (⊥ : Submodule ℚ ℚ) :=
      htopbot (by simp)
    exact one_ne_zero ((Submodule.mem_bot ℚ).mp honebot)
  · intro hx
    unfold OrbitSpanTop
    apply top_unique
    intro y hy
    have h1 : (1 : ℚ) ∈
        Submodule.span ℚ (Set.range (fun r : ℚᵐᵒᵖ => ratAct r x)) := by
      apply Submodule.subset_span
      refine ⟨MulOpposite.op x⁻¹, ?_⟩
      simp [ratAct, hx]
    simpa using (Submodule.smul_mem
      (Submodule.span ℚ (Set.range (fun r : ℚᵐᵒᵖ => ratAct r x))) y h1)

theorem rat_orbit_basis (x : ℚ)
    (hx : RightCyclic (R := ℚ) x) :
    ∃ n : Nat, ∃ b : Basis (Fin n) ℚ ℚ,
      ∃ c : Fin n → ℚᵐᵒᵖ,
        ∀ i, ratAct (c i) x = b i := by
  have hx0 : x ≠ 0 := (rat_cyclic_iff_ne_zero x).mp hx
  let b : Module.Basis (Fin 1) ℚ ℚ :=
    (Module.Basis.singleton Unit ℚ).reindex (Fintype.equivFin Unit)
  refine ⟨1, b, (fun _ => MulOpposite.op x⁻¹), ?_⟩
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change x⁻¹ * x = b 0
  have he : (Fintype.equivFin Unit).symm (0 : Fin 1) = () :=
    Subsingleton.elim _ _
  rw [show b 0 = 1 by
    change ((Module.Basis.singleton Unit ℚ).reindex
      (Fintype.equivFin Unit)) 0 = 1
    rw [Module.Basis.reindex_apply, he]
    exact Module.Basis.singleton_apply Unit ℚ ()]
  simp [hx0]

noncomputable def test :
    OriginalOrbitDivisionTest ℚ ℚ Unit Unit ℚ ℚ Unit
      (fun _ : Unit => ℚ) ℚ
      (RingHom.id ℚ) (fun _ => RingHom.id ℚ) := by
  let top : ℚ →+ (∀ _ : Unit, ℚ) :=
    { toFun := fun x _ => x
      map_zero' := by funext i; simp
      map_add' := by intro x y; funext i; simp }
  let bridge : CyclicTopBridge
      (R := ℚ) (M := ℚ) (fun _ : Unit => RingHom.id ℚ) :=
    { top := top
      map_smul := by intro z m i; simp [top]
      reflects_generation := by
        intro m hm
        apply (rat_cyclic_iff_ne_zero m).mpr
        intro hmzero
        apply (semisimple_top_criterion (top m)).mp hm ()
        simp [top, hmzero] }
  let localTest : OriginalLocalTest ℚ Unit Unit :=
    { targetDivisor := 1
      localization := ()
      cyclicFiniteModule := ()
      canonicalGenerator := ()
      rightTail := 1
      offset := 0
      localization_spec := True
      localization_spec_proof := trivial
      finite_length_cyclic_spec := True
      finite_length_cyclic_proof := trivial
      canonical_generator_spec := True
      canonical_generator_spec_proof := trivial
      rightTail_nonzero := one_ne_zero
      generation := fun source _ _ => source ≠ 0 }
  refine
    { actual :=
        { localTest := localTest
          bridge := bridge
          sourceMap := AddMonoidHom.id ℚ
          sourceMap_scalar := by intro z x; simp
          passes_iff_cyclic := by
            intro source
            change source ≠ 0 ↔ RightCyclic (R := ℚ) source
            simpa using (rat_cyclic_iff_ne_zero source).symm }
      top := LinearMap.id
      act := ratAct
      top_cyclic_iff := by
        intro m
        exact (rat_cyclic_iff_ne_zero m).trans (rat_orbit_span_iff m).symm
      orbit_basis := rat_orbit_basis }

example : ∃ (H source : ℚ),
    source = 1 + H * 1 ∧ source ≠ 0 ∧
    test.actual.localTest.Passes source := by
  obtain ⟨H, source, hsource, hne, _, hpass, _⟩ :=
    OriginalOrbitDivisionTest.exists_original_affine_source_of_finite_orbit_list
      (ι := RingHom.id ℚ) (by intro x y h; exact h)
      [test] 1 1 1 one_ne_zero
      (by intro t ht; simp only [List.mem_singleton] at ht; subst t
          exact ⟨rfl, trivial, trivial, trivial, one_ne_zero⟩)
      (by intro t ht; simp only [List.mem_singleton] at ht; subst t
          change RightCyclic (R := ℚ) (1 : ℚ)
          exact (rat_cyclic_iff_ne_zero 1).mpr one_ne_zero)
  exact ⟨H, source, hsource, hne, hpass test (by simp)⟩

end SymplecticStafford.Source.OriginalOrbitProducerOracle
