module

public import SymplecticStafford.Paper.NoFiniteRank
public import SymplecticStafford.Paper.Test
public import Mathlib.RingTheory.FiniteLength

@[expose] public section

/-!
# Source selection (paper Proposition 4.6)

For finitely many admissible tests `(T, V, e, b, z)` over a simple domain `U`
and `a ≠ 0`, `B ∈ U`, there is `H ∈ U` such that `F = B + H a` satisfies every
test: `(z + e F b) T = V`.

The proof has three steps.

1. *One test, no offset* (`exists_generating_multiple`): for `t ≠ 0` some
   `e ι(H t)` generates `V`.  Among the submodules `K` with
   `e ι(H t) T + K = V` for some `H` take a minimal one (`V` is Artinian).  If
   `K` is not contained in a maximal submodule `M`, put `S = V/M` and
   `E = End_T(S)`.  `Hom_T(V, S)` is finite-dimensional over `E`
   (`finite_hom_of_isFiniteLength`), so Corollary 4.4 gives `H₁` for which no
   nonzero `φ : V → S` kills `e ι(H₁ t)`.  The pencil `H + λ H₁` keeps both
   properties for all but finitely many `λ` (Lemma 4.5 and Corollary 4.8), and
   then `K ∩ M` already works (`source_reduction`, via
   `exists_hom_quot_of_inf_le`), contradicting minimality.
2. *Several tests* (`Test.exists_common_multiple`): combine along pencils.
3. *Offsets* (`Test.exists_source`): one more pencil in the central scalar.
-/

namespace SymplecticStafford.Paper

open MulOpposite Module

universe w

section HomFinite

variable {R : Type*} [Ring R] {Q : Type*} [AddCommGroup Q] [Module R Q] [IsSimpleModule R Q]

/-- `Hom_R(V, Q)` is finite-dimensional over the Schur division ring
`End_R(Q)` of a simple module `Q`, when `V` has finite length. -/
theorem finite_hom_of_isFiniteLength {V : Type*} [AddCommGroup V] [Module R V]
    (h : IsFiniteLength R V) : Module.Finite (Module.End R Q) (V →ₗ[R] Q) := by
  classical
  induction h with
  | @of_subsingleton V₀ _ _ _ =>
    have : Subsingleton (V₀ →ₗ[R] Q) :=
      ⟨fun φ ψ => LinearMap.ext fun v => by rw [Subsingleton.elim v 0, map_zero, map_zero]⟩
    infer_instance
  | @of_simple_quotient V _ _ N _ _ ih =>
    let r : (V →ₗ[R] Q) →ₗ[Module.End R Q] (N →ₗ[R] Q) :=
      { toFun := fun φ => φ.comp N.subtype
        map_add' := fun φ ψ => LinearMap.add_comp _ _ _
        map_smul' := fun f φ => by ext; rfl }
    have hker : ∀ φ ∈ LinearMap.ker r, N ≤ LinearMap.ker φ := by
      intro φ hφ n hn
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp hφ) ⟨n, hn⟩
    refine Module.finite_def.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker r ?_ ?_)
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq]
      by_cases hex : ∃ φ₀ ∈ LinearMap.ker r, φ₀ ≠ 0
      · obtain ⟨φ₀, hφ₀, hne⟩ := hex
        let ψ₀ := N.liftQ φ₀ (hker φ₀ hφ₀)
        have hψ₀ : ψ₀ ≠ 0 := by
          intro h
          apply hne
          ext v
          have := LinearMap.congr_fun h (N.mkQ v)
          simpa [ψ₀] using this
        let ε := LinearEquiv.ofBijective ψ₀ (LinearMap.bijective_of_ne_zero hψ₀)
        have hε : ∀ v, ε (N.mkQ v) = φ₀ v := fun v => by simp [ε, ψ₀]
        have heq : LinearMap.ker r = Submodule.span (Module.End R Q) {φ₀} := by
          apply le_antisymm
          · intro φ hφ
            rw [Submodule.mem_span_singleton]
            refine ⟨(N.liftQ φ (hker φ hφ)).comp ε.symm.toLinearMap, ?_⟩
            ext v
            rw [LinearMap.smul_apply, Module.End.smul_def, LinearMap.comp_apply, ← hε,
              LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.mkQ_apply,
              Submodule.liftQ_apply]
          · rw [Submodule.span_le, Set.singleton_subset_iff]
            exact hφ₀
        rw [heq]
        exact Submodule.fg_span_singleton φ₀
      · push Not at hex
        rw [(Submodule.eq_bot_iff _).mpr hex]
        exact Submodule.fg_bot

end HomFinite

section Quotients

variable {R : Type*} [Ring R] {V : Type*} [AddCommGroup V] [Module R V]

lemma sup_eq_top_of_isCoatom {K M : Submodule R V} (hM : IsCoatom M) (hKM : ¬ K ≤ M) :
    K ⊔ M = ⊤ :=
  hM.2 _ (lt_of_le_of_ne le_sup_right fun h => hKM (le_sup_left.trans h.ge))

lemma surjective_mkQ_comp_subtype {K M : Submodule R V} (hM : IsCoatom M) (hKM : ¬ K ≤ M) :
    Function.Surjective (M.mkQ ∘ₗ K.subtype) := by
  intro q
  obtain ⟨v, rfl⟩ := M.mkQ_surjective q
  have hv : v ∈ K ⊔ M := (sup_eq_top_of_isCoatom hM hKM).symm ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  refine ⟨⟨y, hy⟩, ?_⟩
  simp [(Submodule.Quotient.mk_eq_zero M).mpr hz]

/-- If two maximal submodules `M, M'` both fail to contain `K` and
`K ∩ M ⊆ M'`, then `V/M' ≅ V/M`; in particular there is a nonzero map
`V → V/M` vanishing on `M'`. -/
theorem exists_hom_quot_of_inf_le {K M M' : Submodule R V} (hM : IsCoatom M) (hM' : IsCoatom M')
    (hKM : ¬ K ≤ M) (hKM' : ¬ K ≤ M') (hle : K ⊓ M ≤ M') :
    ∃ φ : V →ₗ[R] V ⧸ M, φ ≠ 0 ∧ M' ≤ LinearMap.ker φ := by
  have : IsSimpleModule R (V ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  set f := M.mkQ ∘ₗ K.subtype
  set f' := M'.mkQ ∘ₗ K.subtype
  have hf := surjective_mkQ_comp_subtype hM hKM
  have hf' := surjective_mkQ_comp_subtype hM' hKM'
  have hker : LinearMap.ker f = LinearMap.ker f' := by
    have hc : IsCoatom (LinearMap.ker f) := LinearMap.isCoatom_ker_of_surjective hf
    have hle' : LinearMap.ker f ≤ LinearMap.ker f' := by
      intro x hx
      simp only [f, f', LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply] at hx ⊢
      exact hle ⟨x.2, hx⟩
    rcases hc.le_iff.mp hle' with h | h
    · exfalso
      apply hKM'
      intro x hx
      have : (⟨x, hx⟩ : K) ∈ LinearMap.ker f' := h ▸ Submodule.mem_top
      simpa [f'] using this
    · exact h.symm
  let e₁ := f.quotKerEquivOfSurjective hf
  let e₂ := f'.quotKerEquivOfSurjective hf'
  let e₃ := Submodule.quotEquivOfEq _ _ hker.symm
  refine ⟨(e₁.toLinearMap ∘ₗ e₃.toLinearMap ∘ₗ e₂.symm.toLinearMap) ∘ₗ M'.mkQ, ?_, ?_⟩
  · intro h0
    obtain ⟨v, hv⟩ : ∃ v, v ∉ M' := by
      by_contra hc
      push Not at hc
      exact hM'.1 (eq_top_iff.mpr fun v _ => hc v)
    have := LinearMap.congr_fun h0 v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply,
      LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact hv this
  · intro v hv
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero M').mpr hv, map_zero]

end Quotients

section Pencils

variable {k : Type*} [Field k]

/-- **Reverse pencil.**  If `x` generates an Artinian module, then `y + λ x`
generates for all but finitely many central scalars `λ`. -/
theorem generator_pencil_finite_rev {A : Type*} [Ring A] [Algebra k A] {M : Type*}
    [AddCommGroup M] [Module A M] [IsArtinian A M] {x : M}
    (hx : Submodule.span A {x} = ⊤) (y : M) :
    {l : k | Submodule.span A {y + algebraMap k A l • x} ≠ ⊤}.Finite := by
  refine ((Set.Finite.preimage inv_injective.injOn
    (generator_pencil_finite (k := k) hx y)).union (Set.finite_singleton 0)).subset ?_
  intro l hl
  by_cases hl0 : l = 0
  · exact Or.inr hl0
  left
  show Submodule.span A {x + algebraMap k A l⁻¹ • y} ≠ ⊤
  intro htop
  apply hl
  have hu : IsUnit (algebraMap k A l) := (Ne.isUnit hl0).map _
  have : y + algebraMap k A l • x = algebraMap k A l • (x + algebraMap k A l⁻¹ • y) := by
    rw [smul_add, smul_smul, ← map_mul, mul_inv_cancel₀ hl0, map_one, one_smul, add_comm]
  rw [this, Submodule.span_singleton_smul_eq hu, htop]

variable {U : Type*} [Ring U] [Algebra k U] {T : Type*} [Ring T] [Algebra k T]
variable {V : Type*} [AddCommGroup V] [Module Tᵐᵒᵖ V]

/-- `e ι((F + λ G) t) = e ι(F t) + λ e ι(G t)`. -/
lemma op_pencil_smul (ι : U →ₐ[k] T) (F G t : U) (l : k) (e : V) :
    op (ι ((F + algebraMap k U l * G) * t)) • e =
      op (ι (F * t)) • e + algebraMap k Tᵐᵒᵖ l • op (ι (G * t)) • e := by
  rw [rmul_pencil k ι F G t l e]
  rfl

end Pencils

section SingleTest

variable {k : Type*} [Field k] {U : Type*} [Ring U] [Algebra k U]
variable {T : Type*} [Ring T] [Algebra k T]
variable {V : Type*} [AddCommGroup V] [Module Tᵐᵒᵖ V]

/-- **Reduction step.**  If `e ι(H t) T + K = V` and `K ⊄ M` for a maximal
submodule `M`, then some `e ι(H' t) T + (K ∩ M) = V`. -/
theorem source_reduction [Infinite k] [IsSimpleRing U] [IsSimpleRing T] [IsDomain T]
    (hnd : ∃ τ : T, τ ≠ 0 ∧ ¬ IsUnit τ) (ι : U →ₐ[k] T) {S : Submonoid U}
    (hfrac : IsRightFractions S (ι : U →+* T)) [IsArtinian Tᵐᵒᵖ V] [IsNoetherian Tᵐᵒᵖ V]
    {e : V} (he : Submodule.span Tᵐᵒᵖ {e} = ⊤) {t : U} (ht : t ≠ 0)
    {K M : Submodule Tᵐᵒᵖ V} {H : U}
    (hH : Submodule.span Tᵐᵒᵖ {op (ι (H * t)) • e} ⊔ K = ⊤)
    (hM : IsCoatom M) (hKM : ¬ K ≤ M) :
    ∃ H' : U, Submodule.span Tᵐᵒᵖ {op (ι (H' * t)) • e} ⊔ (K ⊓ M) = ⊤ := by
  classical
  have : IsSimpleModule Tᵐᵒᵖ (V ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  have : Module.Finite (Module.End Tᵐᵒᵖ (V ⧸ M)) (V →ₗ[Tᵐᵒᵖ] V ⧸ M) :=
    finite_hom_of_isFiniteLength
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  let ev : V → ((V →ₗ[Tᵐᵒᵖ] V ⧸ M) →ₗ[Module.End Tᵐᵒᵖ (V ⧸ M)] V ⧸ M) := fun y =>
    { toFun := fun φ => φ y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ y φ, ev y φ = φ y := fun _ _ => rfl
  have hev_e : Function.Injective (ev e) := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    refine LinearMap.ext_on (s := {e}) he ?_
    rintro _ rfl
    exact hφ
  obtain ⟨H₁, hH₁⟩ := exists_injective_rmul hnd ι hfrac (ev e) hev_e ht
  set x := op (ι (H * t)) • e with hxdef
  set x₁ := op (ι (H₁ * t)) • e with hx₁def
  have hinj₁ : Function.Injective (ev x₁) := by
    have : (rmul (ι (H₁ * t))).comp (ev e) = ev x₁ :=
      LinearMap.ext fun φ => (φ.map_smul _ _).symm
    rwa [this] at hH₁
  have hB₁ := pencil_ker_finite (centralEnd (T := T) (M := V ⧸ M) k) (centralEnd_comm k) (ev x₁) (ev x) hinj₁
  have hxK : Submodule.span Tᵐᵒᵖ {K.mkQ x} = ⊤ := by
    rw [← Set.image_singleton, ← Submodule.map_span, Submodule.map_mkQ_eq_top, sup_comm]
    exact hH
  have hB₂ := generator_pencil_finite (k := k) hxK (K.mkQ x₁)
  obtain ⟨l, hl⟩ := (((Set.Finite.preimage inv_injective.injOn hB₁).union hB₂).union
    (Set.finite_singleton 0)).exists_notMem
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    not_or, not_not] at hl
  obtain ⟨⟨hl₁, hl₂⟩, hl₀⟩ := hl
  refine ⟨H + algebraMap k U l * H₁, ?_⟩
  set x' := op (ι ((H + algebraMap k U l * H₁) * t)) • e with hx'def
  have hx' : x' = x + algebraMap k Tᵐᵒᵖ l • x₁ := op_pencil_smul ι H H₁ t l e
  have hgenK : Submodule.span Tᵐᵒᵖ {x'} ⊔ K = ⊤ := by
    rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, Set.image_singleton, hx',
      map_add, map_smul]
    exact hl₂
  have hinj' : Function.Injective (ev x') := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    by_contra hφ0
    apply hl₁
    refine ⟨φ, hφ0, ?_⟩
    have h1 : φ x + centralEnd (T := T) (M := V ⧸ M) k l • φ x₁ = 0 := by
      have : ev x' φ = φ x + centralEnd (T := T) (M := V ⧸ M) k l • φ x₁ := by
        rw [hev, hx', map_add, φ.map_smul (algebraMap k Tᵐᵒᵖ l) x₁]
        rfl
      rw [← this]
      exact hφ
    rw [hev, hev]
    have h2 := congrArg (fun m => centralEnd (T := T) (M := V ⧸ M) k (l⁻¹) • m) h1
    simp only [smul_add, smul_smul, ← map_mul, inv_mul_cancel₀ hl₀, map_one, one_smul,
      smul_zero] at h2
    rw [add_comm]
    exact h2
  by_contra hcon
  obtain ⟨M', hM', hle'⟩ :=
    (eq_top_or_exists_le_coatom (Submodule.span Tᵐᵒᵖ {x'} ⊔ (K ⊓ M))).resolve_left hcon
  have hx'M' : x' ∈ M' := hle' (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x'))
  have hKMM' : K ⊓ M ≤ M' := le_sup_right.trans hle'
  have hKM' : ¬ K ≤ M' := by
    intro h
    apply hM'.1
    rw [eq_top_iff, ← hgenK]
    exact sup_le (le_sup_left.trans hle') h
  obtain ⟨φ, hφ0, hφ⟩ := exists_hom_quot_of_inf_le hM hM' hKM hKM' hKMM'
  apply hφ0
  apply hinj'
  rw [map_zero, hev]
  exact hφ hx'M'

/-- **One test, no offset.**  For `t ≠ 0` there is `H` with `e ι(H t) T = V`. -/
theorem exists_generating_multiple [Infinite k] [IsSimpleRing U] [IsSimpleRing T] [IsDomain T]
    (hnd : ∃ τ : T, τ ≠ 0 ∧ ¬ IsUnit τ) (ι : U →ₐ[k] T) {S : Submonoid U}
    (hfrac : IsRightFractions S (ι : U →+* T)) [IsArtinian Tᵐᵒᵖ V] [IsNoetherian Tᵐᵒᵖ V]
    {e : V} (he : Submodule.span Tᵐᵒᵖ {e} = ⊤) {t : U} (ht : t ≠ 0) :
    ∃ H : U, Submodule.span Tᵐᵒᵖ {op (ι (H * t)) • e} = ⊤ := by
  obtain ⟨K, ⟨H, hH⟩, hmin⟩ := (wellFounded_lt (α := Submodule Tᵐᵒᵖ V)).has_min
    {K | ∃ H : U, Submodule.span Tᵐᵒᵖ {op (ι (H * t)) • e} ⊔ K = ⊤} ⟨⊤, 0, sup_top_eq _⟩
  refine ⟨H, ?_⟩
  by_contra hx
  obtain ⟨M, hM, hxM⟩ := (eq_top_or_exists_le_coatom _).resolve_left hx
  by_cases hKM : K ≤ M
  · apply hM.1
    rw [eq_top_iff, ← hH]
    exact sup_le hxM hKM
  · obtain ⟨H', hH'⟩ := source_reduction hnd ι hfrac he ht hH hM hKM
    exact hmin (K ⊓ M) ⟨H', hH'⟩ (inf_lt_left.mpr hKM)

end SingleTest

namespace Test

variable {k U : Type*} [Field k] [Ring U] [Algebra k U]

/-- **Several tests, no offset.**  For `a ≠ 0` one `H₀` makes every
`e ι(H₀ a b)` a generator. -/
theorem exists_common_multiple [Infinite k] [IsSimpleRing U] [IsDomain U]
    (Ω : List (Test.{w} k U)) (a : U) (ha : a ≠ 0) :
    ∃ H₀ : U, ∀ τ ∈ Ω, Submodule.span τ.Tᵐᵒᵖ {op (τ.ι (H₀ * (a * τ.b))) • τ.e} = ⊤ := by
  induction Ω with
  | nil => exact ⟨0, by simp⟩
  | cons τ Ω ih =>
    obtain ⟨H₁, hH₁⟩ := ih
    have := τ.simple
    have := τ.domain
    have := τ.artinian
    have := τ.noetherian
    obtain ⟨H', hH'⟩ := exists_generating_multiple τ.nondivision τ.ι τ.frac τ.e_gen
      (mul_ne_zero ha τ.b_ne)
    have hfinτ : {l : k | Submodule.span τ.Tᵐᵒᵖ
        {op (τ.ι ((H₁ + algebraMap k U l * H') * (a * τ.b))) • τ.e} ≠ ⊤}.Finite := by
      refine (generator_pencil_finite_rev (k := k) hH'
        (op (τ.ι (H₁ * (a * τ.b))) • τ.e)).subset ?_
      intro l hl
      rwa [Set.mem_ofPred_eq, op_pencil_smul] at hl
    have hfinΩ : (⋃ σ ∈ {σ | σ ∈ Ω}, {l : k | Submodule.span σ.Tᵐᵒᵖ
        {op (σ.ι ((H₁ + algebraMap k U l * H') * (a * σ.b))) • σ.e} ≠ ⊤}).Finite := by
      refine Set.Finite.biUnion (List.finite_toSet Ω) fun σ hσ => ?_
      have := σ.artinian
      refine (generator_pencil_finite (k := k) (hH₁ σ hσ)
        (op (σ.ι (H' * (a * σ.b))) • σ.e)).subset ?_
      intro l hl
      rwa [Set.mem_ofPred_eq, op_pencil_smul] at hl
    obtain ⟨l, hl⟩ := (hfinτ.union hfinΩ).exists_notMem
    refine ⟨H₁ + algebraMap k U l * H', fun σ hσ => ?_⟩
    rcases List.mem_cons.mp hσ with rfl | hσ
    · by_contra h
      exact hl (Or.inl h)
    · by_contra h
      exact hl (Or.inr (Set.mem_biUnion (x := σ) hσ h))

/-- **Proposition 4.6 (source selection).**  For finitely many admissible tests
over a simple domain `U`, and `a ≠ 0`, some source of the form `B + H a`
satisfies all of them. -/
theorem exists_source [Infinite k] [IsSimpleRing U] [IsDomain U] (Ω : List (Test.{w} k U))
    (B a : U) (ha : a ≠ 0) : ∃ H : U, ∀ τ ∈ Ω, τ.Satisfies (B + H * a) := by
  obtain ⟨H₀, hH₀⟩ := exists_common_multiple Ω a ha
  have hfin : (⋃ τ ∈ {τ | τ ∈ Ω},
      {l : k | ¬ τ.Satisfies (B + algebraMap k U l * H₀ * a)}).Finite := by
    refine Set.Finite.biUnion (List.finite_toSet Ω) fun τ hτ => ?_
    have := τ.artinian
    refine (generator_pencil_finite_rev (k := k) (hH₀ τ hτ)
      (τ.z + op (τ.ι (B * τ.b)) • τ.e)).subset ?_
    intro l hl
    have hl' : ¬ Submodule.span τ.Tᵐᵒᵖ
        {τ.z + op (τ.ι ((B + algebraMap k U l * H₀ * a) * τ.b)) • τ.e} = ⊤ := hl
    rw [mul_assoc (algebraMap k U l), op_pencil_smul, ← add_assoc, mul_assoc H₀ a τ.b] at hl'
    exact hl'
  obtain ⟨l, hl⟩ := hfin.exists_notMem
  refine ⟨algebraMap k U l * H₀, fun τ hτ => ?_⟩
  by_contra h
  exact hl (Set.mem_biUnion (x := τ) hτ h)

end Test

end SymplecticStafford.Paper
