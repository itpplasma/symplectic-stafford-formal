import SymplecticStafford.Paper.ConsequencesGeneration
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.OreLocalization.NonZeroDivisors
import Mathlib.RingTheory.OreLocalization.OreSet
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.NoncommRing

/-!
# Rank, splitting and cancellation (paper §7, part II)

Right modules over the domain `Λ` are modules over `R = Λᵐᵒᵖ`.  The right Ore
condition on `Λ` is exactly the (left) Ore condition on the non-zero-divisors of
`Λᵐᵒᵖ` in Mathlib's sense (`rightOre_iff_nonempty_oreSet`), so we work under the
instance `[OreSet (Λᵐᵒᵖ)⁰]`.  The division ring of fractions is
`QΛ Λ = (Λᵐᵒᵖ)[(Λᵐᵒᵖ)⁰⁻¹]` (its elements are the right fractions `a b⁻¹` of `Λ`,
written as left fractions in `Λᵐᵒᵖ`), the base change of a right module `M` is the
Ore localization `Loc Λ M = M[(Λᵐᵒᵖ)⁰⁻¹]`, and `oreRank Λ M` is its dimension over
`QΛ Λ`.

Main results (paper §7):
* `oreRank_prod`, `oreRank_self`, `oreRank_eq_of_equiv`: additivity, `rank Λ = 1`,
  invariance.
* `exists_generator_retaining`, `combo_injective` (Theorem 7.4): images spanning
  `M ⊗ Q` can be retained and completed by one element; independent images give an
  injective `Λʳ → M`.
* `oreRank_le_card`, `exists_generating_card_le`, `free_of_generating_card_eq`
  (Corollary 7.5): the minimal number of generators is `r` (then `M ≅ Λʳ`) or `r+1`.
* `exists_diagonal_functionals` (Lemma 7.9), `exists_unimodular_of_two_le_oreRank`
  (Theorem 7.10 combined with Lemma 7.9).
* `exists_split_free_of_oreRank`, `exists_split_ideal_of_torsionFree` (Corollary 7.11).
* `unimodular_correction` (Lemma 7.12).
* `cancellation_free`, `cancellation_projective` (Theorem 7.13).
-/

namespace SymplecticStafford.Paper

open MulOpposite Submodule OreLocalization
open scoped nonZeroDivisors

variable {Λ : Type*} [Ring Λ] [IsDomain Λ]

section OreSetBridge

theorem mem_nonZeroDivisors_op_iff (r : Λᵐᵒᵖ) : r ∈ (Λᵐᵒᵖ)⁰ ↔ unop r ≠ 0 := by
  rw [mem_nonZeroDivisors_iff_ne_zero, Ne, Ne, unop_eq_zero_iff]

/-- The right Ore condition of `Λ` is Mathlib's Ore condition for `(Λᵐᵒᵖ)⁰`. -/
theorem rightOre_iff_nonempty_oreSet : RightOre Λ ↔ Nonempty (OreSet (Λᵐᵒᵖ)⁰) := by
  rw [nonempty_oreSet_iff_of_noZeroDivisors]
  constructor
  · intro h r s
    by_cases hr : r = 0
    · exact ⟨0, 1, by simp [hr]⟩
    have hs : unop (s : Λᵐᵒᵖ) ≠ 0 := (mem_nonZeroDivisors_op_iff _).1 s.2
    obtain ⟨u, v, huv, hne⟩ := h (unop r) (unop (s : Λᵐᵒᵖ)) (by simpa using hr) hs
    have hu : u ≠ 0 := fun hu => hne (by rw [hu, mul_zero])
    refine ⟨op v, ⟨op u, (mem_nonZeroDivisors_op_iff _).2 (by simpa using hu)⟩, ?_⟩
    apply unop_injective
    simp [huv]
  · intro h a b ha hb
    obtain ⟨r', s', hrs⟩ := h (op a) ⟨op b, (mem_nonZeroDivisors_op_iff _).2 (by simpa using hb)⟩
    have hs' : unop (s' : Λᵐᵒᵖ) ≠ 0 := (mem_nonZeroDivisors_op_iff _).1 s'.2
    refine ⟨unop (s' : Λᵐᵒᵖ), unop r', ?_, mul_ne_zero ha hs'⟩
    have := congrArg unop hrs
    simpa using this

/-- The Ore set structure on `(Λᵐᵒᵖ)⁰` provided by the right Ore condition. -/
@[instance_reducible]
noncomputable def oreSetOfRightOre (h : RightOre Λ) : OreSet (Λᵐᵒᵖ)⁰ :=
  (rightOre_iff_nonempty_oreSet.1 h).some

theorem rightOre_of_oreSet [OreSet (Λᵐᵒᵖ)⁰] : RightOre Λ :=
  rightOre_iff_nonempty_oreSet.2 ⟨inferInstance⟩

/-- The left Ore condition of `Λ` is the right Ore condition of `Λᵐᵒᵖ`. -/
theorem rightOre_op_of_leftOre (h : LeftOre Λ) : RightOre Λᵐᵒᵖ := by
  intro a b ha hb
  obtain ⟨u, v, huv, hne⟩ := h (unop a) (unop b) (by simpa using ha) (by simpa using hb)
  refine ⟨op u, op v, ?_, ?_⟩
  · apply unop_injective; simpa using huv
  · simpa [and_comm] using hne

/-- The right Ore condition of `Λ` is the left Ore condition of `Λᵐᵒᵖ`. -/
theorem leftOre_op_of_rightOre (h : RightOre Λ) : LeftOre Λᵐᵒᵖ := by
  intro a b ha hb
  obtain ⟨u, v, huv, hne⟩ := h (unop a) (unop b) (by simpa using ha) (by simpa using hb)
  refine ⟨op u, op v, ?_, ?_⟩
  · apply unop_injective; simpa using huv
  · simpa [and_comm] using hne

end OreSetBridge

variable [OreSet (Λᵐᵒᵖ)⁰]

variable (Λ) in
/-- The division ring of fractions `Q(Λ)` (right fractions of `Λ`). -/
abbrev QΛ := OreLocalization (Λᵐᵒᵖ)⁰ Λᵐᵒᵖ

variable (Λ) in
/-- The base change `M ⊗ Q(Λ)` of a right module, as an Ore localization. -/
abbrev Loc (M : Type*) [AddCommGroup M] [Module Λᵐᵒᵖ M] := OreLocalization (Λᵐᵒᵖ)⁰ M

variable (Λ) in
/-- The Ore rank `dim_{Q(Λ)} (M ⊗ Q(Λ))` of a right module. -/
noncomputable def oreRank (M : Type*) [AddCommGroup M] [Module Λᵐᵒᵖ M] : ℕ :=
  Module.finrank (QΛ Λ) (Loc Λ M)

section Loc

variable {M N P : Type*} [AddCommGroup M] [Module Λᵐᵒᵖ M] [AddCommGroup N] [Module Λᵐᵒᵖ N]
  [AddCommGroup P] [Module Λᵐᵒᵖ P]

variable (Λ M) in
/-- The canonical `Λ`-linear map `M → M ⊗ Q(Λ)`, `m ↦ m /ₒ 1`. -/
def toLoc : M →ₗ[Λᵐᵒᵖ] Loc Λ M where
  toFun m := m /ₒ 1
  map_add' _ _ := add_oreDiv.symm
  map_smul' r m := (smul_oreDiv_one r m).symm

omit [IsDomain Λ] in
theorem toLoc_apply (m : M) : toLoc Λ M m = m /ₒ 1 := rfl

omit [IsDomain Λ] in
theorem oreDiv_eq_smul_toLoc (m : M) (s : (Λᵐᵒᵖ)⁰) :
    (m /ₒ s : Loc Λ M) = ((1 : Λᵐᵒᵖ) /ₒ s : QΛ Λ) • toLoc Λ M m := by
  rw [toLoc_apply, OreLocalization.one_div_smul, one_mul]

omit [IsDomain Λ] in
theorem smul_toLoc (r : Λᵐᵒᵖ) (m : M) :
    ((r /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ) • toLoc Λ M m) = toLoc Λ M (r • m) := by
  rw [oreDiv_one_smul, map_smul]

omit [IsDomain Λ] in
theorem span_range_toLoc : span (QΛ Λ) (Set.range (toLoc Λ M)) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  induction z using OreLocalization.ind with
  | c m s =>
    rw [oreDiv_eq_smul_toLoc]
    exact smul_mem _ _ (subset_span ⟨m, rfl⟩)

omit [IsDomain Λ] in
/-- A generating set of `M` localizes to a spanning set of `M ⊗ Q(Λ)`. -/
theorem span_toLoc_image_eq_top {s : Set M} (hs : span Λᵐᵒᵖ s = ⊤) :
    span (QΛ Λ) (toLoc Λ M '' s) = ⊤ := by
  rw [eq_top_iff, ← span_range_toLoc, span_le]
  rintro _ ⟨m, rfl⟩
  have hm : m ∈ span Λᵐᵒᵖ s := hs ▸ mem_top
  have : toLoc Λ M m ∈ span Λᵐᵒᵖ (toLoc Λ M '' s) := by
    rw [← map_span]
    exact mem_map_of_mem hm
  exact span_le_restrictScalars Λᵐᵒᵖ (QΛ Λ) _ this

omit [IsDomain Λ] in
theorem finite_loc [Module.Finite Λᵐᵒᵖ M] : Module.Finite (QΛ Λ) (Loc Λ M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Λᵐᵒᵖ) (M := M)
  refine ⟨⟨s.image (toLoc Λ M), ?_⟩⟩
  rw [Finset.coe_image]
  exact span_toLoc_image_eq_top hs

/-- `toLoc m = 0` exactly when `m` is torsion. -/
theorem toLoc_eq_zero_iff (m : M) : toLoc Λ M m = 0 ↔ IsRightTorsion Λ m := by
  rw [toLoc_apply, ← zero_oreDiv (1 : (Λᵐᵒᵖ)⁰), oreDiv_eq_iff]
  constructor
  · rintro ⟨u, v, h1, h2⟩
    simp only [smul_zero, Submonoid.coe_one, mul_one] at h1 h2
    refine ⟨unop (u : Λᵐᵒᵖ), (mem_nonZeroDivisors_op_iff _).1 u.2, ?_⟩
    rw [op_unop, h2]
    exact h1.symm
  · rintro ⟨c, hc, hcm⟩
    refine ⟨⟨op c, (mem_nonZeroDivisors_op_iff _).2 (by simpa using hc)⟩, op c, ?_, ?_⟩
    · rw [smul_zero]
      exact hcm.symm
    · rfl

/-- The map induced on base changes by a `Λ`-linear map. -/
def locMapFun (f : M →ₗ[Λᵐᵒᵖ] N) : Loc Λ M → Loc Λ N :=
  liftExpand (fun m s => f m /ₒ s) (fun m t s ht => by
    rw [map_smul]
    exact OreLocalization.expand (f m) s t ht)

omit [IsDomain Λ] in
theorem locMapFun_oreDiv (f : M →ₗ[Λᵐᵒᵖ] N) (m : M) (s : (Λᵐᵒᵖ)⁰) :
    locMapFun f (m /ₒ s) = f m /ₒ s := rfl

/-- The `Q(Λ)`-linear map `f ⊗ Q(Λ)`. -/
def locMap (f : M →ₗ[Λᵐᵒᵖ] N) : Loc Λ M →ₗ[QΛ Λ] Loc Λ N where
  toFun := locMapFun f
  map_add' x y := by
    induction x using OreLocalization.ind with
    | c m₁ s₁ =>
    induction y using OreLocalization.ind with
    | c m₂ s₂ =>
    rw [oreDiv_add_oreDiv, locMapFun_oreDiv, locMapFun_oreDiv, locMapFun_oreDiv,
      oreDiv_add_oreDiv]
    simp only [map_add, Submonoid.smul_def, map_smul]
  map_smul' q x := by
    induction q using OreLocalization.ind with
    | c r t =>
    induction x using OreLocalization.ind with
    | c m s =>
    rw [oreDiv_smul_oreDiv, RingHom.id_apply, locMapFun_oreDiv, locMapFun_oreDiv,
      oreDiv_smul_oreDiv, map_smul]

omit [IsDomain Λ] in
theorem locMap_oreDiv (f : M →ₗ[Λᵐᵒᵖ] N) (m : M) (s : (Λᵐᵒᵖ)⁰) :
    locMap f (m /ₒ s) = f m /ₒ s := rfl

omit [IsDomain Λ] in
theorem locMap_toLoc (f : M →ₗ[Λᵐᵒᵖ] N) (m : M) :
    locMap f (toLoc Λ M m) = toLoc Λ N (f m) := rfl

omit [IsDomain Λ] in
theorem locMap_comp (f : M →ₗ[Λᵐᵒᵖ] N) (g : N →ₗ[Λᵐᵒᵖ] P) :
    locMap (g ∘ₗ f) = (locMap g).comp (locMap (Λ := Λ) f) := by
  ext x
  induction x using OreLocalization.ind with
  | c m s => rfl

omit [IsDomain Λ] in
theorem locMap_id : locMap (LinearMap.id : M →ₗ[Λᵐᵒᵖ] M) = LinearMap.id (R := QΛ Λ) := by
  ext x
  induction x using OreLocalization.ind with
  | c m s => rfl

omit [IsDomain Λ] in
theorem locMap_add (f g : M →ₗ[Λᵐᵒᵖ] N) :
    locMap (f + g) = locMap f + locMap (Λ := Λ) g := by
  ext x
  induction x using OreLocalization.ind with
  | c m s =>
    rw [LinearMap.add_apply, locMap_oreDiv, locMap_oreDiv, locMap_oreDiv, LinearMap.add_apply,
      add_oreDiv]

/-- Base change of a linear equivalence. -/
def locEquiv (e : M ≃ₗ[Λᵐᵒᵖ] N) : Loc Λ M ≃ₗ[QΛ Λ] Loc Λ N :=
  LinearEquiv.ofLinearMap (locMap e.toLinearMap) (locMap e.symm.toLinearMap)
    (by rw [← locMap_comp]; simp [locMap_id]) (by rw [← locMap_comp]; simp [locMap_id])

/-- Base change is exact on injections. -/
theorem locMap_injective {f : M →ₗ[Λᵐᵒᵖ] N} (hf : Function.Injective f) :
    Function.Injective (locMap (Λ := Λ) f) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  induction x using OreLocalization.ind with
  | c m s =>
    rw [LinearMap.mem_ker, locMap_oreDiv, oreDiv_eq_smul_toLoc] at hx
    rw [mem_bot, oreDiv_eq_smul_toLoc]
    have h1 : toLoc Λ N (f m) = 0 := by
      have := congrArg (fun z => ((s : Λᵐᵒᵖ) /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ) • z) hx
      simpa [smul_smul, ← OreLocalization.one_def, OreLocalization.mul_inv] using this
    obtain ⟨c, hc, hcm⟩ := (toLoc_eq_zero_iff _).1 h1
    have : toLoc Λ M m = 0 := (toLoc_eq_zero_iff _).2 ⟨c, hc, hf (by rw [map_smul, hcm, map_zero])⟩
    rw [this, smul_zero]

omit [IsDomain Λ] in
/-- The Ore rank is an isomorphism invariant. -/
theorem oreRank_eq_of_equiv (e : M ≃ₗ[Λᵐᵒᵖ] N) : oreRank Λ M = oreRank Λ N :=
  (locEquiv e).finrank_eq

omit [IsDomain Λ] in
theorem locMap_zero : locMap (0 : M →ₗ[Λᵐᵒᵖ] N) = (0 : Loc Λ M →ₗ[QΛ Λ] Loc Λ N) := by
  ext x
  induction x using OreLocalization.ind with
  | c m s => rw [locMap_oreDiv, LinearMap.zero_apply, zero_oreDiv, LinearMap.zero_apply]

omit [IsDomain Λ] in
theorem locMap_comp_apply (f : M →ₗ[Λᵐᵒᵖ] N) (g : N →ₗ[Λᵐᵒᵖ] P) (x : Loc Λ M) :
    locMap g (locMap f x) = locMap (g ∘ₗ f) x := by
  rw [locMap_comp, LinearMap.comp_apply]

/-- Base change commutes with finite products. -/
def locProdEquiv : Loc Λ (M × N) ≃ₗ[QΛ Λ] Loc Λ M × Loc Λ N :=
  LinearEquiv.ofLinearMap
    ((locMap (LinearMap.fst Λᵐᵒᵖ M N)).prod (locMap (LinearMap.snd Λᵐᵒᵖ M N)))
    ((locMap (LinearMap.inl Λᵐᵒᵖ M N)).coprod (locMap (LinearMap.inr Λᵐᵒᵖ M N)))
    (by
      apply LinearMap.ext
      rintro ⟨x, y⟩
      simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply,
        LinearMap.id_apply, Function.prod, map_add, locMap_comp_apply, LinearMap.fst_comp_inl,
        LinearMap.snd_comp_inr, LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, locMap_id,
        locMap_zero, LinearMap.zero_apply, Prod.mk_add_mk, add_zero, zero_add])
    (by
      apply LinearMap.ext
      intro x
      have hid : LinearMap.inl Λᵐᵒᵖ M N ∘ₗ LinearMap.fst Λᵐᵒᵖ M N +
          LinearMap.inr Λᵐᵒᵖ M N ∘ₗ LinearMap.snd Λᵐᵒᵖ M N = LinearMap.id := by
        ext <;> simp
      simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply,
        LinearMap.id_apply, Function.prod, locMap_comp_apply]
      rw [← LinearMap.add_apply, ← locMap_add, hid, locMap_id, LinearMap.id_apply])

/-- Additivity of the Ore rank on finite products. -/
theorem oreRank_prod [Module.Finite Λᵐᵒᵖ M] [Module.Finite Λᵐᵒᵖ N] :
    oreRank Λ (M × N) = oreRank Λ M + oreRank Λ N := by
  have := finite_loc (Λ := Λ) (M := M)
  have := finite_loc (Λ := Λ) (M := N)
  rw [oreRank, (locProdEquiv (Λ := Λ) (M := M) (N := N)).finrank_eq, Module.finrank_prod]
  rfl

end Loc

section RankGeneration

variable {M : Type*} [AddCommGroup M] [Module Λᵐᵒᵖ M]

omit [IsDomain Λ] [OreSet (Λᵐᵒᵖ)⁰] in
variable (Λ) in
/-- `unop : Λᵐᵒᵖ → Λ` identifies `Λᵐᵒᵖ` with `Λ` viewed as a right module over itself. -/
def unopLinear : Λᵐᵒᵖ ≃ₗ[Λᵐᵒᵖ] Λ where
  toFun := unop
  invFun := op
  map_add' _ _ := rfl
  map_smul' r x := by simp
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsDomain Λ] [OreSet (Λᵐᵒᵖ)⁰] in
instance finite_right_self : Module.Finite Λᵐᵒᵖ Λ :=
  Module.Finite.equiv (unopLinear Λ)

/-- The free right module of rank one has Ore rank one. -/
theorem oreRank_self : oreRank Λ Λ = 1 := by
  have h1 : toLoc Λ Λ 1 ≠ 0 := by
    rw [Ne, toLoc_eq_zero_iff]
    rintro ⟨c, hc, h⟩
    rw [op_smul_eq_mul, one_mul] at h
    exact hc h
  have hspan : span (QΛ Λ) {toLoc Λ Λ 1} = ⊤ := by
    rw [eq_top_iff, ← span_range_toLoc, span_le]
    rintro _ ⟨y, rfl⟩
    have : toLoc Λ Λ y = ((op y /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ) • toLoc Λ Λ 1) := by
      rw [smul_toLoc, op_smul_eq_mul, one_mul]
    rw [this]
    exact smul_mem _ _ (mem_span_singleton_self _)
  rw [oreRank, ← finrank_top, ← hspan, finrank_span_singleton h1]

/-- If the images of `x` span `M ⊗ Q(Λ)`, then `M ⧸ ∑ xᵢΛ` is torsion. -/
theorem isRightTorsion_quotient_of_span {ι : Type*} (x : ι → M)
    (hx : span (QΛ Λ) (Set.range (toLoc Λ M ∘ x)) = ⊤)
    (q : M ⧸ span Λᵐᵒᵖ (Set.range x)) : IsRightTorsion Λ q := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hzero : locMap (Λ := Λ) (span Λᵐᵒᵖ (Set.range x)).mkQ = 0 := by
    have : span (QΛ Λ) (Set.range (toLoc Λ M ∘ x)) ≤
        LinearMap.ker (locMap (Λ := Λ) (span Λᵐᵒᵖ (Set.range x)).mkQ) := by
      rw [span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Function.comp_apply, locMap_toLoc,
        Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (subset_span (Set.mem_range_self i)), map_zero]
    rwa [hx, top_le_iff, LinearMap.ker_eq_top] at this
  rw [← toLoc_eq_zero_iff, ← Submodule.mkQ_apply, ← locMap_toLoc, hzero, LinearMap.zero_apply]

/-- **Theorem 7.4 (retention).**  Over a right Ore domain with the same-divisor
property, if `M` is finitely generated and the images of `x` span `M ⊗ Q(Λ)` (for
instance, form a basis), then the `x` can be retained and one further element
generates: `M = ∑ xᵢΛ + zΛ`. -/
theorem exists_generator_retaining (hS : S38 Λ) [Module.Finite Λᵐᵒᵖ M] {ι : Type*} (x : ι → M)
    (hx : span (QΛ Λ) (Set.range (toLoc Λ M ∘ x)) = ⊤) :
    ∃ z : M, span Λᵐᵒᵖ (Set.range x) ⊔ span Λᵐᵒᵖ {z} = ⊤ :=
  exists_sup_span_singleton_eq_top (rightOre_of_oreSet (Λ := Λ)) hS _ (isRightTorsion_quotient_of_span x hx)

omit [IsDomain Λ] [OreSet (Λᵐᵒᵖ)⁰] in
/-- The right-linear map `Λ^ι → M`, `v ↦ ∑ xᵢ vᵢ`. -/
def combo {ι : Type*} [Fintype ι] (x : ι → M) : (ι → Λ) →ₗ[Λᵐᵒᵖ] M where
  toFun v := ∑ i, op (v i) • x i
  map_add' v w := by simp only [Pi.add_apply, op_add, add_smul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, op_mul, op_unop, mul_smul,
      RingHom.id_apply, Finset.smul_sum]

omit [IsDomain Λ] [OreSet (Λᵐᵒᵖ)⁰] in
theorem combo_apply {ι : Type*} [Fintype ι] (x : ι → M) (v : ι → Λ) :
    combo (Λ := Λ) x v = ∑ i, op (v i) • x i := rfl

omit [IsDomain Λ] in
theorem numerator_injective :
    Function.Injective (fun r : Λᵐᵒᵖ => (r /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ)) := by
  intro r r' h
  exact numeratorHom_inj (S := (Λᵐᵒᵖ)⁰) inf_le_left h

omit [IsDomain Λ] in
/-- **Theorem 7.4 (injectivity).**  If the images of `x₁, …, x_r` are linearly
independent over `Q(Λ)`, then `Λ^r → M`, `v ↦ ∑ xᵢ vᵢ`, is injective. -/
theorem combo_injective {ι : Type*} [Fintype ι] (x : ι → M)
    (hx : LinearIndependent (QΛ Λ) (toLoc Λ M ∘ x)) : Function.Injective (combo (Λ := Λ) x) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker, combo_apply] at hv
  have h0 : ∑ i, ((op (v i) /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ)) • (toLoc Λ M ∘ x) i = 0 := by
    simp only [Function.comp_apply, smul_toLoc, ← map_sum, hv, map_zero]
  have := Fintype.linearIndependent_iff.1 hx _ h0
  rw [mem_bot]
  funext i
  have hi : (op (v i) /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ) = ((0 : Λᵐᵒᵖ) /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ) := by
    rw [this i, zero_oreDiv]
  simpa using numerator_injective hi

/-- **Corollary 7.5 (lower bound).**  Every finite generating set has at least
`rank M` elements. -/
theorem oreRank_le_card (s : Finset M) (hs : span Λᵐᵒᵖ (s : Set M) = ⊤) :
    oreRank Λ M ≤ s.card := by
  classical
  calc oreRank Λ M = Module.finrank (QΛ Λ) (span (QΛ Λ) ((s.image (toLoc Λ M) : Finset _) :
        Set (Loc Λ M))) := by
        rw [Finset.coe_image, span_toLoc_image_eq_top hs, finrank_top]; rfl
    _ ≤ (s.image (toLoc Λ M)).card := finrank_span_finset_le_card _
    _ ≤ s.card := Finset.card_image_le

/-- **Theorem 7.4 / Corollary 7.5 (upper bound).**  Over a right Ore domain with
the same-divisor property, a finitely generated right module of Ore rank `r` is
generated by at most `r + 1` elements. -/
theorem exists_generating_card_le (hS : S38 Λ) [Module.Finite Λᵐᵒᵖ M] :
    ∃ s : Finset M, s.card ≤ oreRank Λ M + 1 ∧ span Λᵐᵒᵖ (s : Set M) = ⊤ := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := Λᵐᵒᵖ) (M := M)
  let v : G → Loc Λ M := fun g => toLoc Λ M g
  have hspan : span (QΛ Λ) (Set.range v) = ⊤ := by
    rw [← span_toLoc_image_eq_top hG]
    congr 1
    ext y
    simp [v]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (QΛ Λ) v
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  let b := Module.Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ = oreRank Λ M := (Module.finrank_eq_card_basis b).symm
  obtain ⟨z, hz⟩ := exists_generator_retaining hS (fun k => (a k : M)) (by
    rw [← hspan, ← hsp]
    rfl)
  refine ⟨insert z (Finset.univ.image fun k => (a k : M)), ?_, ?_⟩
  · calc (insert z (Finset.univ.image fun k => (a k : M))).card
        ≤ (Finset.univ.image fun k => (a k : M)).card + 1 := Finset.card_insert_le _ _
      _ ≤ Fintype.card κ + 1 := by
        gcongr
        exact Finset.card_image_le.trans (by rw [Finset.card_univ])
      _ = oreRank Λ M + 1 := by rw [hcard]
  · rw [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ, span_insert,
      sup_comm, hz]

/-- **Corollary 7.5 (free case).**  If `M` is generated by `rank M` elements, then
it is free of that rank. -/
theorem free_of_generating_card_eq [Module.Finite Λᵐᵒᵖ M] (x : Fin (oreRank Λ M) → M)
    (hx : span Λᵐᵒᵖ (Set.range x) = ⊤) :
    Nonempty (M ≃ₗ[Λᵐᵒᵖ] (Fin (oreRank Λ M) → Λ)) := by
  have := finite_loc (Λ := Λ) (M := M)
  have hspan : span (QΛ Λ) (Set.range (toLoc Λ M ∘ x)) = ⊤ := by
    rw [Set.range_comp]
    exact span_toLoc_image_eq_top hx
  have hli : LinearIndependent (QΛ Λ) (toLoc Λ M ∘ x) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (Fintype.card_fin _)
  have hsurj : Function.Surjective (combo (Λ := Λ) x) := by
    intro m
    have hm : m ∈ span Λᵐᵒᵖ (Set.range x) := hx ▸ mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Λᵐᵒᵖ).1 hm
    exact ⟨fun i => unop (c i), by simpa [combo_apply] using hc⟩
  exact ⟨(LinearEquiv.ofBijective (combo (Λ := Λ) x) ⟨combo_injective x hli, hsurj⟩).symm⟩

end RankGeneration

section Functionals

variable {N : Type*} [AddCommGroup N] [Module Λᵐᵒᵖ N]

omit [IsDomain Λ] in
theorem mul_oreDiv_self (s : (Λᵐᵒᵖ)⁰) (y : Λᵐᵒᵖ) :
    (((s : Λᵐᵒᵖ) * y) /ₒ s : QΛ Λ) = y /ₒ (1 : (Λᵐᵒᵖ)⁰) := by
  rw [oreDiv_eq_iff]
  refine ⟨s, 1, ?_, ?_⟩
  · rw [Submonoid.smul_def, smul_eq_mul, one_smul]
  · simp

/-- Clearing one left denominator of `Λ` (a right denominator in `Λᵐᵒᵖ`) uses the
left Ore condition. -/
theorem exists_right_denominator (hL : LeftOre Λ) (q : QΛ Λ) :
    ∃ d : (Λᵐᵒᵖ)⁰, ∃ y : Λᵐᵒᵖ, q * ((d : Λᵐᵒᵖ) /ₒ (1 : (Λᵐᵒᵖ)⁰)) = y /ₒ (1 : (Λᵐᵒᵖ)⁰) := by
  induction q using OreLocalization.ind with
  | c r s =>
    by_cases hr : r = 0
    · refine ⟨1, 0, ?_⟩
      rw [hr, zero_oreDiv', zero_mul, zero_oreDiv']
    have hs : unop (s : Λᵐᵒᵖ) ≠ 0 := (mem_nonZeroDivisors_op_iff _).1 s.2
    obtain ⟨u, v, huv, hne⟩ := hL (unop r) (unop (s : Λᵐᵒᵖ)) (by simpa using hr) hs
    have hu : u ≠ 0 := fun hu => hne (by rw [hu, zero_mul])
    refine ⟨⟨op u, (mem_nonZeroDivisors_op_iff _).2 (by simpa using hu)⟩, op v, ?_⟩
    rw [mul_div_one]
    have : r * op u = (s : Λᵐᵒᵖ) * op v := by
      apply unop_injective
      simpa using huv
    rw [this, mul_oreDiv_self]

/-- A common left denominator for finitely many fractions (left Ore). -/
theorem exists_common_right_denominator (hL : LeftOre Λ) (F : Finset (QΛ Λ)) :
    ∃ d : (Λᵐᵒᵖ)⁰, ∀ q ∈ F, ∃ y : Λᵐᵒᵖ,
      q * ((d : Λᵐᵒᵖ) /ₒ (1 : (Λᵐᵒᵖ)⁰)) = y /ₒ (1 : (Λᵐᵒᵖ)⁰) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, fun q hq => absurd hq (Finset.notMem_empty q)⟩
  | insert q F _ ih =>
    obtain ⟨d₀, hd₀⟩ := ih
    obtain ⟨d₁, y₁, hy₁⟩ := exists_right_denominator hL (q * ((d₀ : Λᵐᵒᵖ) /ₒ (1 : (Λᵐᵒᵖ)⁰)))
    have hsplit : (((d₀ * d₁ : (Λᵐᵒᵖ)⁰) : Λᵐᵒᵖ) /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ) =
        ((d₀ : Λᵐᵒᵖ) /ₒ (1 : (Λᵐᵒᵖ)⁰)) * ((d₁ : Λᵐᵒᵖ) /ₒ (1 : (Λᵐᵒᵖ)⁰)) := by
      rw [mul_div_one, Submonoid.coe_mul]
    refine ⟨d₀ * d₁, fun q' hq' => ?_⟩
    rw [hsplit, ← mul_assoc]
    rcases Finset.mem_insert.1 hq' with rfl | hq'
    · exact ⟨y₁, hy₁⟩
    · obtain ⟨y, hy⟩ := hd₀ q' hq'
      exact ⟨y * d₁, by rw [hy, mul_div_one]⟩

variable (Λ) in
/-- The numerator map `Λᵐᵒᵖ → Q(Λ)` as a linear map. -/
def numLinear : Λᵐᵒᵖ →ₗ[Λᵐᵒᵖ] QΛ Λ := LinearMap.toSpanSingleton Λᵐᵒᵖ (QΛ Λ) 1

omit [IsDomain Λ] in
theorem numLinear_apply (r : Λᵐᵒᵖ) : numLinear Λ r = r /ₒ (1 : (Λᵐᵒᵖ)⁰) := by
  rw [numLinear, LinearMap.toSpanSingleton_apply, ← oreDiv_one_smul, smul_eq_mul, mul_one]

omit [IsDomain Λ] in
theorem numLinear_injective : Function.Injective (numLinear Λ) := by
  intro r r' h
  rw [numLinear_apply, numLinear_apply] at h
  exact numerator_injective h

/-- Right multiplication on `Q(Λ)` is `Λᵐᵒᵖ`-linear. -/
def mulRightLinear (d : QΛ Λ) : QΛ Λ →ₗ[Λᵐᵒᵖ] QΛ Λ where
  toFun q := q * d
  map_add' x y := add_mul x y d
  map_smul' r q := smul_mul_assoc r q d

/-- An integral multiple of a rational functional: for a `Q(Λ)`-linear
`c : N ⊗ Q → Q` on a finitely generated `N`, clearing a common left denominator
`d` (left Ore) gives a right-linear `φ : N → Λ` with `φ n = d · c(n ⊗ 1)`. -/
theorem exists_integral_functional (hL : LeftOre Λ) [Module.Finite Λᵐᵒᵖ N]
    (c : Loc Λ N →ₗ[QΛ Λ] QΛ Λ) :
    ∃ d : Λ, d ≠ 0 ∧ ∃ φ : N →ₗ[Λᵐᵒᵖ] Λ, ∀ n,
      (op (φ n) /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ) = c (toLoc Λ N n) * (op d /ₒ (1 : (Λᵐᵒᵖ)⁰)) := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := Λᵐᵒᵖ) (M := N)
  obtain ⟨d, hd⟩ := exists_common_right_denominator hL (G.image fun n => c (toLoc Λ N n))
  let g : N →ₗ[Λᵐᵒᵖ] QΛ Λ := mulRightLinear ((d : Λᵐᵒᵖ) /ₒ (1 : (Λᵐᵒᵖ)⁰)) ∘ₗ
    (c.restrictScalars Λᵐᵒᵖ) ∘ₗ toLoc Λ N
  have hg : ∀ n, g n ∈ LinearMap.range (numLinear Λ) := by
    have : span Λᵐᵒᵖ (G : Set N) ≤ (LinearMap.range (numLinear Λ)).comap g := by
      rw [span_le]
      intro n hn
      obtain ⟨y, hy⟩ := hd _ (Finset.mem_image_of_mem _ hn)
      exact ⟨y, by rw [numLinear_apply, ← hy]; rfl⟩
    intro n
    rw [hG] at this
    exact this mem_top
  let φR : N →ₗ[Λᵐᵒᵖ] Λᵐᵒᵖ := (LinearEquiv.ofInjective (numLinear Λ) numLinear_injective).symm.toLinearMap
    ∘ₗ g.codRestrict _ hg
  refine ⟨unop (d : Λᵐᵒᵖ), (mem_nonZeroDivisors_op_iff _).1 d.2,
    (unopLinear Λ).toLinearMap ∘ₗ φR, fun n => ?_⟩
  have h1 : numLinear Λ (φR n) = g n := by
    simp only [φR, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  rw [numLinear_apply] at h1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, op_unop]
  exact h1

/-- **Lemma 7.9 (integral diagonal functionals).**  Let `Λ` be a left and right
Ore domain, `N` a finitely generated right module and `M ≤ N` with
`rank M ≥ 2`.  Then there are `x₁, x₂ ∈ M` and right-linear `φ₁, φ₂ : N → Λ`
with `φᵢ(xⱼ) = 0` for `i ≠ j` and `φᵢ(xᵢ) ≠ 0`. -/
theorem exists_diagonal_functionals (hL : LeftOre Λ) [Module.Finite Λᵐᵒᵖ N]
    (M : Submodule Λᵐᵒᵖ N) (hM : 2 ≤ oreRank Λ M) :
    ∃ x₁ ∈ M, ∃ x₂ ∈ M, ∃ φ₁ φ₂ : N →ₗ[Λᵐᵒᵖ] Λ,
      φ₁ x₂ = 0 ∧ φ₂ x₁ = 0 ∧ φ₁ x₁ ≠ 0 ∧ φ₂ x₂ ≠ 0 := by
  classical
  have hfin : Module.Finite (QΛ Λ) (Loc Λ M) := Module.finite_of_finrank_pos (by
    unfold oreRank at hM; omega)
  obtain ⟨κ, a, _, hsp, hli⟩ := exists_linearIndependent' (QΛ Λ) (toLoc Λ M)
  let b := Module.Basis.mk hli (by rw [hsp, span_range_toLoc])
  have : Finite κ := Module.Finite.finite_basis b
  have := Fintype.ofFinite κ
  have hcard : Fintype.card κ = oreRank Λ M := (Module.finrank_eq_card_basis b).symm
  obtain ⟨k₁, k₂, hk⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card κ)
  -- the images in `N ⊗ Q` stay independent
  have hinj : LinearMap.ker (locMap (Λ := Λ) M.subtype) = ⊥ :=
    LinearMap.ker_eq_bot.2 (locMap_injective M.injective_subtype)
  have hw := hli.map' (locMap (Λ := Λ) M.subtype) hinj
  set w := locMap (Λ := Λ) M.subtype ∘ (toLoc Λ M ∘ a) with hwdef
  have hw_apply : ∀ k, w k = toLoc Λ N (a k : N) := fun k => rfl
  have hs := hw.linearIndepOn_id
  let B := Module.Basis.extend hs
  let p : κ → hs.extend (Set.subset_univ _) := fun k =>
    ⟨w k, Module.Basis.subset_extend hs ⟨k, rfl⟩⟩
  have hB : ∀ k, B (p k) = w k := fun k => Module.Basis.extend_apply_self hs (p k)
  have hp : p k₁ ≠ p k₂ := fun h => hk (hw.injective (congrArg Subtype.val h))
  have hcoord : ∀ i j, B.coord (p i) (w j) = if p j = p i then 1 else 0 := by
    intro i j
    rw [← hB j, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  obtain ⟨d₁, hd₁, φ₁, hφ₁⟩ := exists_integral_functional hL (B.coord (p k₁))
  obtain ⟨d₂, hd₂, φ₂, hφ₂⟩ := exists_integral_functional hL (B.coord (p k₂))
  have key : ∀ (φ : N →ₗ[Λᵐᵒᵖ] Λ) (d : Λ) (i j : κ),
      (∀ n, (op (φ n) /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ) =
        B.coord (p i) (toLoc Λ N n) * (op d /ₒ (1 : (Λᵐᵒᵖ)⁰))) →
      φ (a j : N) = if p j = p i then d else 0 := by
    intro φ d i j hφ
    have h := hφ (a j : N)
    rw [← hw_apply, hcoord] at h
    apply op_injective
    apply numerator_injective
    split_ifs at h ⊢
    · simpa using h
    · simpa using h
  refine ⟨(a k₁ : N), (a k₁).2, (a k₂ : N), (a k₂).2, φ₁, φ₂, ?_, ?_, ?_, ?_⟩
  · rw [key φ₁ d₁ k₁ k₂ hφ₁, if_neg hp.symm]
  · rw [key φ₂ d₂ k₂ k₁ hφ₂, if_neg hp]
  · rw [key φ₁ d₁ k₁ k₁ hφ₁, if_pos rfl]; exact hd₁
  · rw [key φ₂ d₂ k₂ k₂ hφ₂, if_pos rfl]; exact hd₂

end Functionals

section Splitting

variable {N : Type*} [AddCommGroup N] [Module Λᵐᵒᵖ N]

/-- **Theorem 7.10 with Lemma 7.9 (rank two supplies a free summand).**  Let `Λ`
be a left and right Ore domain with the same-divisor property, `N` finitely
generated and `M ≤ N` with `rank M ≥ 2`.  Then some `x ∈ M` is unimodular in `N`:
`ψ x = 1` for a right-linear `ψ : N → Λ`, and `N = xΛ ⊕ ker ψ`,
`M = xΛ ⊕ (M ∩ ker ψ)`. -/
theorem exists_unimodular_of_two_le_oreRank (hL : LeftOre Λ) (hS : S38 Λ)
    [Module.Finite Λᵐᵒᵖ N] (M : Submodule Λᵐᵒᵖ N) (hM : 2 ≤ oreRank Λ M) :
    ∃ x ∈ M, ∃ ψ : N →ₗ[Λᵐᵒᵖ] Λ, ψ x = 1 ∧
      IsCompl (span Λᵐᵒᵖ {x}) (LinearMap.ker ψ) ∧
      span Λᵐᵒᵖ {x} ⊔ (M ⊓ LinearMap.ker ψ) = M ∧
      span Λᵐᵒᵖ {x} ⊓ (M ⊓ LinearMap.ker ψ) = ⊥ := by
  obtain ⟨x₁, hx₁, x₂, hx₂, φ₁, φ₂, h₁₂, h₂₁, hd₁, hd₂⟩ := exists_diagonal_functionals hL M hM
  exact residual_splitting (rightOre_of_oreSet (Λ := Λ)) hS M hx₁ hx₂ φ₁ φ₂ h₁₂ h₂₁ hd₁ hd₂

omit [IsDomain Λ] [OreSet (Λᵐᵒᵖ)⁰] in
/-- `r ↦ x r` as a right-linear map `Λ → N`. -/
def smulRightLinear (x : N) : Λ →ₗ[Λᵐᵒᵖ] N where
  toFun r := op r • x
  map_add' a b := by rw [op_add, add_smul]
  map_smul' a r := by
    rw [RingHom.id_apply, MulOpposite.smul_eq_mul_unop, op_mul, op_unop, mul_smul]

omit [IsDomain Λ] [OreSet (Λᵐᵒᵖ)⁰] in
theorem smulRightLinear_apply (x : N) (r : Λ) : smulRightLinear x r = op r • x := rfl

omit [IsDomain Λ] [OreSet (Λᵐᵒᵖ)⁰] in
/-- A unimodular element splits off a free summand: `N ≅ Λ ⊕ ker ψ` when `ψ x = 1`. -/
def splitEquiv (x : N) (ψ : N →ₗ[Λᵐᵒᵖ] Λ) (h : ψ x = 1) : N ≃ₗ[Λᵐᵒᵖ] Λ × LinearMap.ker ψ :=
  LinearEquiv.ofLinearMap
    (ψ.prod ((LinearMap.id - smulRightLinear x ∘ₗ ψ).codRestrict (LinearMap.ker ψ) (fun n => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.comp_apply,
        smulRightLinear_apply, map_smul, h, LinearMap.id_apply, op_smul_eq_mul, one_mul,
        sub_self])))
    ((smulRightLinear x).coprod (LinearMap.ker ψ).subtype)
    (by
      apply LinearMap.ext
      rintro ⟨r, k⟩
      have hk : ψ k = 0 := k.2
      ext
      · simp [smulRightLinear_apply, h, hk]
      · simp [smulRightLinear_apply, h, hk])
    (by
      apply LinearMap.ext
      intro n
      simp)

/-- **Corollary 7.11 (splitting off free summands).**  Over a left and right Ore
domain with the same-divisor property, every finitely generated right module of
rank `r + 1` decomposes as `N ≅ Λ^r ⊕ N₁` with `N₁ ≤ N` finitely generated of rank
one. -/
theorem exists_split_free_of_oreRank (hL : LeftOre Λ) (hS : S38 Λ) (r : ℕ) :
    ∀ (N : Type*) [AddCommGroup N] [Module Λᵐᵒᵖ N] [Module.Finite Λᵐᵒᵖ N],
      oreRank Λ N = r + 1 → ∃ N₁ : Submodule Λᵐᵒᵖ N, Module.Finite Λᵐᵒᵖ N₁ ∧
        oreRank Λ N₁ = 1 ∧ Nonempty (N ≃ₗ[Λᵐᵒᵖ] (Fin r → Λ) × N₁) := by
  induction r with
  | zero =>
    intro N _ _ _ hN
    refine ⟨⊤, inferInstance, ?_, ⟨?_⟩⟩
    · rw [← oreRank_eq_of_equiv (Submodule.topEquiv).symm, hN]
    · exact (Submodule.topEquiv).symm.trans ((LinearEquiv.prodUnique).symm.trans
        (LinearEquiv.prodComm _ _ _))
  | succ r ih =>
    intro N _ _ _ hN
    have hM : 2 ≤ oreRank Λ (⊤ : Submodule Λᵐᵒᵖ N) := by
      rw [oreRank_eq_of_equiv Submodule.topEquiv, hN]; omega
    obtain ⟨x, -, ψ, hψ, -⟩ := exists_unimodular_of_two_le_oreRank hL hS ⊤ hM
    let e := splitEquiv x ψ hψ
    have : Module.Finite Λᵐᵒᵖ (LinearMap.ker ψ) :=
      Module.Finite.of_surjective ((LinearMap.snd _ _ _) ∘ₗ e.toLinearMap)
        (fun k => ⟨e.symm (0, k), by simp⟩)
    have hK : oreRank Λ (LinearMap.ker ψ) = r + 1 := by
      have h1 := oreRank_eq_of_equiv e
      rw [oreRank_prod, oreRank_self, hN] at h1
      omega
    obtain ⟨K₁, hK₁f, hK₁, ⟨f⟩⟩ := ih (LinearMap.ker ψ) hK
    let g := Submodule.equivMapOfInjective _ (LinearMap.ker ψ).injective_subtype K₁
    refine ⟨K₁.map (LinearMap.ker ψ).subtype, Module.Finite.equiv g, ?_, ⟨?_⟩⟩
    · rw [← hK₁]
      exact (oreRank_eq_of_equiv (Λ := Λ) (M := K₁)
        (N := K₁.map (LinearMap.ker ψ).subtype) g).symm
    · exact e.trans ((LinearEquiv.prodCongr (LinearEquiv.refl _ _) (f.trans
        (LinearEquiv.prodCongr (LinearEquiv.refl _ _) g))).trans
        ((LinearEquiv.prodAssoc _ _ _ _).symm.trans (LinearEquiv.prodCongr
          (Fin.consLinearEquiv Λᵐᵒᵖ (fun _ : Fin (r + 1) => Λ)) (LinearEquiv.refl _ _))))

/-- **Corollary 7.11 (torsion-free case).**  A finitely generated torsion-free
right module of rank `r + 1` is `Λ^r ⊕ I` for a nonzero right ideal `I`. -/
theorem exists_split_ideal_of_torsionFree (hL : LeftOre Λ) (hS : S38 Λ) (r : ℕ)
    [Module.Finite Λᵐᵒᵖ N] (hN : oreRank Λ N = r + 1)
    (htf : ∀ n : N, IsRightTorsion Λ n → n = 0) :
    ∃ I : Submodule Λᵐᵒᵖ Λ, I ≠ ⊥ ∧ Nonempty (N ≃ₗ[Λᵐᵒᵖ] (Fin r → Λ) × I) := by
  obtain ⟨N₁, hN₁f, hN₁, ⟨e⟩⟩ := exists_split_free_of_oreRank hL hS r N hN
  have hfin : Module.Finite (QΛ Λ) (Loc Λ N₁) := Module.finite_of_finrank_pos (by
    unfold oreRank at hN₁; omega)
  let c : Loc Λ N₁ ≃ₗ[QΛ Λ] QΛ Λ :=
    LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_self]; exact hN₁)
  obtain ⟨d, hd, φ, hφ⟩ := exists_integral_functional hL c.toLinearMap
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro n hn
    rw [LinearMap.mem_ker] at hn
    have h := hφ n
    rw [hn, op_zero, zero_oreDiv] at h
    have hdQ : (op d /ₒ (1 : (Λᵐᵒᵖ)⁰) : QΛ Λ) ≠ 0 := by
      intro h0
      rw [← zero_oreDiv (1 : (Λᵐᵒᵖ)⁰)] at h0
      exact hd (by simpa using numerator_injective h0)
    have hc : c (toLoc Λ N₁ n) = 0 := by
      rcases mul_eq_zero.1 h.symm with h' | h'
      · exact h'
      · exact absurd h' hdQ
    have hn0 : toLoc Λ N₁ n = 0 := c.injective (by rw [hc, map_zero])
    rw [toLoc_eq_zero_iff] at hn0
    have : (n : N) = 0 := htf n (by
      obtain ⟨c', hc', hcn⟩ := hn0
      exact ⟨c', hc', by rw [← Submodule.coe_smul, hcn, Submodule.coe_zero]⟩)
    rw [mem_bot]
    exact Subtype.ext this
  refine ⟨LinearMap.range φ, ?_, ⟨e.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
    (LinearEquiv.ofInjective φ hinj))⟩⟩
  intro h0
  have : oreRank Λ N₁ = 0 := by
    have hbot : LinearMap.range φ = ⊥ := h0
    have hsub : Subsingleton N₁ := by
      constructor
      intro a b
      apply hinj
      have ha : φ a ∈ LinearMap.range φ := LinearMap.mem_range_self φ a
      have hb : φ b ∈ LinearMap.range φ := LinearMap.mem_range_self φ b
      rw [hbot, mem_bot] at ha hb
      rw [ha, hb]
    have : Subsingleton (Loc Λ N₁) := by
      constructor
      intro u v
      induction u using OreLocalization.ind with
      | c m s =>
      induction v using OreLocalization.ind with
      | c m' s' =>
        rw [Subsingleton.elim m 0, Subsingleton.elim m' 0, zero_oreDiv, zero_oreDiv]
    exact Module.finrank_zero_of_subsingleton
  omega

end Splitting

section Cancellation

variable {M N : Type*} [AddCommGroup M] [Module Λᵐᵒᵖ M] [AddCommGroup N] [Module Λᵐᵒᵖ N]

omit [OreSet (Λᵐᵒᵖ)⁰] in
/-- The left prescribed-tail triple property (Theorem 7.3 for `Λᵐᵒᵖ`): for
`d₁, d₂ ≠ 0` there are `f, g` with `t ∈ Λ(a₁ + d₁ f t) + Λ(a₂ + d₂ g t)`. -/
theorem left_prescribed_tails (hR : RightOre Λ) (hL : LeftOre Λ) (hSop : S38 Λᵐᵒᵖ)
    (a₁ a₂ t : Λ) {d₁ d₂ : Λ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    ∃ f g l₁ l₂ : Λ, t = l₁ * (a₁ + d₁ * f * t) + l₂ * (a₂ + d₂ * g * t) := by
  obtain ⟨f, g, hfg⟩ := triple_prescribed_tails (Λ := Λᵐᵒᵖ) (rightOre_op_of_leftOre hL)
    (leftOre_op_of_rightOre hR) hSop (op a₁) (op a₂) (op t) (t₁ := op d₁) (t₂ := op d₂)
    (by simpa using hd₁) (by simpa using hd₂)
  have ht : op t ∈ span Λᵐᵒᵖᵐᵒᵖ
      {op a₁ + op t * f * op d₁, op a₂ + op t * g * op d₂} := by
    rw [← hfg]
    exact subset_span (by simp)
  obtain ⟨α, β, hαβ⟩ := mem_span_pair.1 ht
  refine ⟨unop f, unop g, unop (unop α), unop (unop β), ?_⟩
  have := congrArg unop hαβ
  simp only [MulOpposite.smul_eq_mul_unop, unop_add, unop_mul, unop_op] at this
  rw [mul_assoc d₁, mul_assoc d₂]
  exact this.symm

/-- **Lemma 7.12 (unimodular correction).**  Let `Λ` be a left and right Ore
domain with `S38 Λᵐᵒᵖ`, `M` finitely generated of rank at least two, and
`(a, t) ∈ M ⊕ Λ` unimodular, witnessed by `χ(a) + q t = 1`.  Then there is
`u ∈ M` such that `a + u t` is unimodular in `M`. -/
theorem unimodular_correction (hL : LeftOre Λ) (hSop : S38 Λᵐᵒᵖ) [Module.Finite Λᵐᵒᵖ M]
    (hM : 2 ≤ oreRank Λ M) (a : M) (t : Λ) (χ : M →ₗ[Λᵐᵒᵖ] Λ) (q : Λ)
    (h : χ a + q * t = 1) :
    ∃ u : M, ∃ ψ : M →ₗ[Λᵐᵒᵖ] Λ, ψ (a + op t • u) = 1 := by
  obtain ⟨x₁, -, x₂, -, φ₁, φ₂, h₁₂, h₂₁, hd₁, hd₂⟩ :=
    exists_diagonal_functionals hL (⊤ : Submodule Λᵐᵒᵖ M)
      (by rwa [oreRank_eq_of_equiv Submodule.topEquiv])
  obtain ⟨f, g, l₁, l₂, hfg⟩ := left_prescribed_tails (rightOre_of_oreSet (Λ := Λ)) hL hSop
    (φ₁ a) (φ₂ a) t hd₁ hd₂
  set u := op f • x₁ + op g • x₂ with hu
  set q' := q - χ u with hq'
  refine ⟨u, χ + lmulLeft (q' * l₁) ∘ₗ φ₁ + lmulLeft (q' * l₂) ∘ₗ φ₂, ?_⟩
  have e₁ : φ₁ (a + op t • u) = φ₁ a + φ₁ x₁ * f * t := by
    simp only [hu, map_add, map_smul, h₁₂, op_smul_eq_mul, zero_mul, add_zero]
  have e₂ : φ₂ (a + op t • u) = φ₂ a + φ₂ x₂ * g * t := by
    simp only [hu, map_add, map_smul, h₂₁, op_smul_eq_mul, zero_mul, zero_add]
  have eχ : χ (a + op t • u) = χ a + χ u * t := by
    rw [map_add, map_smul, op_smul_eq_mul]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, lmulLeft_apply, e₁, e₂, eχ]
  calc χ a + χ u * t + q' * l₁ * (φ₁ a + φ₁ x₁ * f * t) + q' * l₂ * (φ₂ a + φ₂ x₂ * g * t)
      = χ a + χ u * t + q' * (l₁ * (φ₁ a + φ₁ x₁ * f * t) + l₂ * (φ₂ a + φ₂ x₂ * g * t)) := by
        simp only [mul_add, mul_assoc, add_assoc]
    _ = χ a + q * t := by rw [← hfg, hq', sub_mul]; abel
    _ = 1 := h

omit [IsDomain Λ] [OreSet (Λᵐᵒᵖ)⁰] in
/-- An isomorphism `M ⊕ Λ ≅ N ⊕ Λ` fixing the free generator `(0, 1)` induces
`M ≅ N` on the quotients by the free summand. -/
theorem nonempty_equiv_of_prod_fix (e : (M × Λ) ≃ₗ[Λᵐᵒᵖ] (N × Λ)) (h : e (0, 1) = (0, 1)) :
    Nonempty (M ≃ₗ[Λᵐᵒᵖ] N) := by
  have hsm : ∀ r : Λ, ((0 : M), r) = op r • ((0 : M), (1 : Λ)) := fun r => by
    ext <;> simp
  have hsn : ∀ r : Λ, ((0 : N), r) = op r • ((0 : N), (1 : Λ)) := fun r => by
    ext <;> simp
  have he0 : ∀ r : Λ, e (0, r) = (0, r) := fun r => by rw [hsm, map_smul, h, ← hsn]
  have hs0 : ∀ r : Λ, e.symm (0, r) = (0, r) := fun r => by
    rw [LinearEquiv.symm_apply_eq, he0]
  let F : M →ₗ[Λᵐᵒᵖ] N := LinearMap.fst _ _ _ ∘ₗ e.toLinearMap ∘ₗ LinearMap.inl _ _ _
  let G : N →ₗ[Λᵐᵒᵖ] M := LinearMap.fst _ _ _ ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.inl _ _ _
  refine ⟨LinearEquiv.ofLinearMap F G ?_ ?_⟩
  · apply LinearMap.ext
    intro n
    simp only [F, G, LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe,
      LinearMap.fst_apply, LinearMap.id_apply]
    have hsplit : ((e.symm (n, 0)).1, (0 : Λ)) = e.symm (n, 0) - (0, (e.symm (n, 0)).2) := by
      ext <;> simp
    rw [hsplit, map_sub, LinearEquiv.apply_symm_apply, he0]
    simp
  · apply LinearMap.ext
    intro m
    simp only [F, G, LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe,
      LinearMap.fst_apply, LinearMap.id_apply]
    have hsplit : ((e (m, 0)).1, (0 : Λ)) = e (m, 0) - (0, (e (m, 0)).2) := by
      ext <;> simp
    rw [hsplit, map_sub, LinearEquiv.symm_apply_apply, hs0]
    simp

/-- **Theorem 7.13 (cancellation against `Λ`).**  Let `Λ` be a left and right Ore
domain with `S38 Λᵐᵒᵖ`.  If `M` is finitely generated of rank at least two and
`M ⊕ Λ ≅ N ⊕ Λ`, then `M ≅ N`. -/
theorem cancellation_free (hL : LeftOre Λ) (hSop : S38 Λᵐᵒᵖ) [Module.Finite Λᵐᵒᵖ M]
    (hM : 2 ≤ oreRank Λ M) (e : (M × Λ) ≃ₗ[Λᵐᵒᵖ] (N × Λ)) : Nonempty (M ≃ₗ[Λᵐᵒᵖ] N) := by
  set a := (e.symm (0, 1)).1 with ha
  set t := (e.symm (0, 1)).2 with ht
  let χ : M →ₗ[Λᵐᵒᵖ] Λ := LinearMap.snd _ _ _ ∘ₗ e.toLinearMap ∘ₗ LinearMap.inl _ _ _
  have hat : (a, t) = e.symm (0, 1) := rfl
  have hχ : χ a + (e (0, 1)).2 * t = 1 := by
    have h1 : e (a, t) = e (a, 0) + op t • e (0, 1) := by
      rw [← map_smul, ← map_add]
      congr 1
      ext <;> simp
    have h2 := congrArg Prod.snd h1
    rw [hat, LinearEquiv.apply_symm_apply] at h2
    simp only [Prod.snd_add, Prod.smul_snd, op_smul_eq_mul] at h2
    exact h2.symm
  obtain ⟨u, ψ, hψ⟩ := unimodular_correction hL hSop hM a t χ _ hχ
  set a' := a + op t • u with ha'
  -- the four shears
  let A₁ : (M × Λ) →ₗ[Λᵐᵒᵖ] (M × Λ) :=
    LinearMap.inl _ _ _ ∘ₗ smulRightLinear u ∘ₗ LinearMap.snd _ _ _
  let A₂ : (M × Λ) →ₗ[Λᵐᵒᵖ] (M × Λ) :=
    LinearMap.inr _ _ _ ∘ₗ lmulLeft (-t) ∘ₗ ψ ∘ₗ LinearMap.fst _ _ _
  let B₁ : (M × Λ) →ₗ[Λᵐᵒᵖ] (M × Λ) :=
    LinearMap.inl _ _ _ ∘ₗ smulRightLinear a' ∘ₗ LinearMap.snd _ _ _
  let B₂ : (M × Λ) →ₗ[Λᵐᵒᵖ] (M × Λ) :=
    LinearMap.inr _ _ _ ∘ₗ lmulLeft (-1) ∘ₗ ψ ∘ₗ LinearMap.fst _ _ _
  have hA₁ : ∀ x, A₁ (A₁ x) = 0 := fun x => by simp [A₁, smulRightLinear_apply]
  have hA₂ : ∀ x, A₂ (A₂ x) = 0 := fun x => by simp [A₂, lmulLeft_apply]
  have hB₁ : ∀ x, B₁ (B₁ x) = 0 := fun x => by simp [B₁, smulRightLinear_apply]
  have hB₂ : ∀ x, B₂ (B₂ x) = 0 := fun x => by simp [B₂, lmulLeft_apply]
  let S := (shear A₁ hA₁).trans (shear A₂ hA₂)
  let T := (shear B₁ hB₁).trans (shear B₂ hB₂)
  have hS : S (a, t) = (a', 0) := by
    simp only [S, LinearEquiv.trans_apply, shear_apply]
    simp [A₁, A₂, smulRightLinear_apply, lmulLeft_apply, ← ha', hψ]
  have hT : T (0, 1) = (a', 0) := by
    simp only [T, LinearEquiv.trans_apply, shear_apply]
    simp [B₁, B₂, smulRightLinear_apply, lmulLeft_apply, hψ]
  let W := S.trans T.symm
  have hW : W (a, t) = (0, 1) := by
    simp only [W, LinearEquiv.trans_apply, hS]
    rw [LinearEquiv.symm_apply_eq, hT]
  refine nonempty_equiv_of_prod_fix (W.symm.trans e) ?_
  rw [LinearEquiv.trans_apply, (W.symm_apply_eq).2 hW.symm, hat,
    LinearEquiv.apply_symm_apply]

/-- Iterated cancellation against `Λⁿ`. -/
theorem cancellation_free_pow (hL : LeftOre Λ) (hSop : S38 Λᵐᵒᵖ) [Module.Finite Λᵐᵒᵖ M]
    (hM : 2 ≤ oreRank Λ M) (n : ℕ) :
    ((M × (Fin n → Λ)) ≃ₗ[Λᵐᵒᵖ] (N × (Fin n → Λ))) → Nonempty (M ≃ₗ[Λᵐᵒᵖ] N) := by
  induction n with
  | zero =>
    intro e
    exact ⟨LinearEquiv.prodUnique.symm.trans (e.trans LinearEquiv.prodUnique)⟩
  | succ n ih =>
    intro e
    let c : (Fin (n + 1) → Λ) ≃ₗ[Λᵐᵒᵖ] (Fin n → Λ) × Λ :=
      (Fin.consLinearEquiv Λᵐᵒᵖ (fun _ : Fin (n + 1) => Λ)).symm.trans
        (LinearEquiv.prodComm _ _ _)
    let eM : ((M × (Fin n → Λ)) × Λ) ≃ₗ[Λᵐᵒᵖ] (M × (Fin (n + 1) → Λ)) :=
      (LinearEquiv.prodAssoc Λᵐᵒᵖ M (Fin n → Λ) Λ).trans
        (LinearEquiv.prodCongr (LinearEquiv.refl _ _) c.symm)
    let eN : ((N × (Fin n → Λ)) × Λ) ≃ₗ[Λᵐᵒᵖ] (N × (Fin (n + 1) → Λ)) :=
      (LinearEquiv.prodAssoc Λᵐᵒᵖ N (Fin n → Λ) Λ).trans
        (LinearEquiv.prodCongr (LinearEquiv.refl _ _) c.symm)
    have hM' : 2 ≤ oreRank Λ (M × (Fin n → Λ)) := by
      rw [oreRank_prod]; omega
    obtain ⟨f⟩ := cancellation_free hL hSop hM' (eM.trans (e.trans eN.symm))
    exact ih f

/-- **Theorem 7.13 (cancellation against finitely generated projectives).**  Let
`Λ` be a left and right Ore domain with `S38 Λᵐᵒᵖ`.  If `M` is finitely generated
of rank at least two, `P` is finitely generated projective and `M ⊕ P ≅ N ⊕ P`,
then `M ≅ N`. -/
theorem cancellation_projective (hL : LeftOre Λ) (hSop : S38 Λᵐᵒᵖ) [Module.Finite Λᵐᵒᵖ M]
    (hM : 2 ≤ oreRank Λ M) {P : Type*} [AddCommGroup P] [Module Λᵐᵒᵖ P]
    [Module.Finite Λᵐᵒᵖ P] [Module.Projective Λᵐᵒᵖ P] (e : (M × P) ≃ₗ[Λᵐᵒᵖ] (N × P)) :
    Nonempty (M ≃ₗ[Λᵐᵒᵖ] N) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective Λᵐᵒᵖ P
  have hfg' : ∀ p, f (g p) = p := fun p => by rw [← LinearMap.comp_apply, hfg, LinearMap.id_apply]
  let K := LinearMap.ker f
  -- `P ⊕ ker f ≅ Λᵐᵒᵖⁿ`
  let s : (P × K) ≃ₗ[Λᵐᵒᵖ] (Fin n → Λᵐᵒᵖ) :=
    LinearEquiv.ofLinearMap (g.coprod K.subtype)
      (f.prod ((LinearMap.id - g ∘ₗ f).codRestrict K (fun v => by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.comp_apply, hfg',
          LinearMap.id_apply, sub_self])))
      (by
        apply LinearMap.ext
        intro v
        simp)
      (by
        apply LinearMap.ext
        rintro ⟨p, k⟩
        have hk : f k = 0 := k.2
        ext
        · simp [hfg', hk]
        · simp [hfg', hk])
  let u : (Fin n → Λᵐᵒᵖ) ≃ₗ[Λᵐᵒᵖ] (Fin n → Λ) := LinearEquiv.piCongrRight fun _ => unopLinear Λ
  let w : (P × K) ≃ₗ[Λᵐᵒᵖ] (Fin n → Λ) := s.trans u
  let E : (M × (Fin n → Λ)) ≃ₗ[Λᵐᵒᵖ] (N × (Fin n → Λ)) :=
    (LinearEquiv.prodCongr (LinearEquiv.refl _ _) w.symm).trans
      ((LinearEquiv.prodAssoc _ _ _ _).symm.trans
        ((LinearEquiv.prodCongr e (LinearEquiv.refl _ _)).trans
          ((LinearEquiv.prodAssoc _ _ _ _).trans
            (LinearEquiv.prodCongr (LinearEquiv.refl _ _) w))))
  exact cancellation_free_pow hL hSop hM n E

end Cancellation

end SymplecticStafford.Paper
