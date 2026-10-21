module

public import SymplecticStafford.Paper.Localization
public import SymplecticStafford.Paper.Dimension
public import SymplecticStafford.Paper.Test
public import SymplecticStafford.Paper.SourceSelection
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.FiniteType

@[expose] public section

/-!
# The controlled codimension induction (paper §§5–6)

For `d ≠ 0` and `F` put `I_d(F) = dU + FdU` (`Id d F`) and
`δ(I) = dim (G ⧸ gr I)`.  The statement `Ph h` (paper `P_h`, with the finite
test lists) says: for all `d, a ≠ 0`, `B`, and every finite list of admissible
tests, some `F ∈ B + Ua` satisfies every test and `δ(I_d(F)) + h ≤ dim G`.

* `Ph_zero`: the base, from simultaneous source selection (Proposition 4.6).
* `Ph_succ`: the two-call successor of §6, with the common colon ideal of §5,
  the support union (Lemma 5.1), the old/new split, the activated and
  generating pencils (Proposition 4.7, Corollary 4.8), one scalar choice and
  the strict dimension drop (6.10).
* `targetA`: the affine same-divisor theorem `1 = dR + (B + Ha)dS`.
-/

namespace SymplecticStafford.Paper

open MulOpposite

universe uk u uG

namespace FilteredAlgebraData

variable {k : Type uk} {U : Type u} {G : Type uG} [Field k] [Ring U] [Algebra k U]
  [CommRing G] [Algebra k G]
variable {𝒜 : ℕ → Submodule k G} [GradedAlgebra 𝒜]
variable (D : FilteredAlgebraData k U G 𝒜)

/-! ### The right ideals `I_d(F)` and `J` -/

/-- `I_d(F) = dU + FdU`. -/
def Id (d F : U) : Submodule Uᵐᵒᵖ U := Submodule.span Uᵐᵒᵖ {d, F * d}

lemma mem_Id {d F x : U} : x ∈ Id d F ↔ ∃ r s : U, d * r + F * d * s = x :=
  mem_span_pair_iff

lemma d_mem_Id (d F : U) : d ∈ Id d F := Submodule.subset_span (Set.mem_insert _ _)

lemma Fd_mem_Id (d F : U) : F * d ∈ Id d F :=
  Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

/-- The common colon ideal `J = dU + Fd K`, `K = {s : G₀ d s ∈ dU}` (paper (5.2)). -/
def colonJ (d F G₀ : U) : Submodule Uᵐᵒᵖ U where
  carrier := {x | ∃ y s c : U, G₀ * d * s = d * c ∧ x = d * y + F * d * s}
  add_mem' := by
    rintro _ _ ⟨y, s, c, hc, rfl⟩ ⟨y', s', c', hc', rfl⟩
    exact ⟨y + y', s + s', c + c', by rw [mul_add, mul_add, hc, hc'], by noncomm_ring⟩
  zero_mem' := ⟨0, 0, 0, by simp, by simp⟩
  smul_mem' := by
    rintro r _ ⟨y, s, c, hc, rfl⟩
    refine ⟨y * unop r, s * unop r, c * unop r, by rw [← mul_assoc, hc, mul_assoc], ?_⟩
    rw [smul_eq_mul_unop]; noncomm_ring

lemma d_mem_colonJ (d F G₀ : U) : d ∈ colonJ d F G₀ := ⟨1, 0, 0, by simp, by simp⟩

/-- **Polynomial containment (5.3)–(5.4).**  `J ⊆ I_d(F + λ G₀)` for every
central scalar `λ`. -/
lemma colonJ_le_Id (d F G₀ : U) (l : k) :
    colonJ d F G₀ ≤ Id d (F + algebraMap k U l * G₀) := by
  rintro _ ⟨y, s, c, hc, rfl⟩
  refine mem_Id.mpr ⟨y - algebraMap k U l * c, s, ?_⟩
  have hcomm : d * (algebraMap k U l * c) = algebraMap k U l * (G₀ * d * s) := by
    rw [hc, ← mul_assoc, ← Algebra.commutes, mul_assoc]
  rw [mul_sub, hcomm]; noncomm_ring

lemma colonJ_le_Id_self (d F G₀ : U) : colonJ d F G₀ ≤ Id d F := by
  rintro _ ⟨y, s, c, -, rfl⟩
  exact mem_Id.mpr ⟨y, s, rfl⟩

/-- The extension of `I_d(F)` to a ring of right fractions. -/
lemma extend_Id {T : Type*} [Ring T] {ι : U →+* T} (d F : U) :
    IsRightFractions.extend (ι := ι) (Id d F) = Submodule.span Tᵐᵒᵖ {ι d, ι (F * d)} := by
  apply le_antisymm
  · rw [IsRightFractions.extend, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, s, rfl⟩ := mem_Id.mp hx
    rw [SetLike.mem_coe, Submodule.mem_span_pair]
    exact ⟨op (ι r), op (ι s), by simp [map_add, map_mul, mul_assoc]⟩
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact IsRightFractions.map_mem_extend (d_mem_Id d F)
    · exact IsRightFractions.map_mem_extend (Fd_mem_Id d F)

lemma mem_extend_Id {T : Type*} [Ring T] {ι : U →+* T} {d F : U} {x : T} :
    x ∈ IsRightFractions.extend (ι := ι) (Id d F) ↔ ∃ α β : T, ι d * α + ι (F * d) * β = x := by
  rw [extend_Id, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩; exact ⟨unop a, unop b, h⟩
  · rintro ⟨a, b, h⟩; exact ⟨op a, op b, h⟩

/-- The support dimension `δ(U/I) = dim (G ⧸ gr I)`. -/
noncomputable def δ (I : Submodule Uᵐᵒᵖ U) : WithBot ℕ∞ := ringKrullDim (G ⧸ D.grIdeal I)

variable [IsDomain G] [IsNoetherianRing G]

omit [IsNoetherianRing G] in
/-- `gr I = G` forces `1 ∈ I` (the original bounded-below filtration and `F₀U = k`). -/
lemma one_mem_of_grIdeal_eq_top {I : Submodule Uᵐᵒᵖ U} (h : D.grIdeal I = ⊤) : (1 : U) ∈ I := by
  have h1 : (1 : G) ∈ D.grIdeal I := h ▸ Submodule.mem_top
  obtain ⟨u, huI, huF, hug⟩ := D.exists_of_mem_grIdeal h1 SetLike.GradedOne.one_mem
  have hu0 : u ≠ 0 := by rintro rfl; rw [grAt_zero] at hug; exact zero_ne_one hug
  obtain ⟨c, rfl⟩ := D.mem_F_zero_iff.mp huF
  have hc : c ≠ 0 := by rintro rfl; simp at hu0
  have := I.smul_mem (op (algebraMap k U c⁻¹)) huI
  rwa [op_smul_eq_mul, ← map_mul, mul_inv_cancel₀ hc, map_one] at this

/-! ### The local tests at the old minimal primes -/

section Tests

variable [IsSimpleRing U]

/-- `Tloc 𝔭` is a `k`-algebra through `U`, and the localization map is a
`k`-algebra homomorphism. -/
noncomputable def locAlgHom (p : Ideal G) [p.IsPrime] : U →ₐ[k] D.Tloc p :=
  { D.locMap p with commutes' := fun _ => rfl }

/-- The canonical generator of `T ⧸ I T`. -/
lemma span_mk_one_eq_top {T : Type*} [Ring T] (N : Submodule Tᵐᵒᵖ T) :
    Submodule.span Tᵐᵒᵖ {(Submodule.Quotient.mk (1 : T) : T ⧸ N)} = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective N v
  rw [Submodule.mem_span_singleton]
  exact ⟨op τ, by rw [← Submodule.Quotient.mk_smul, op_smul_eq_mul, one_mul]⟩

/-- The admissible test `(T_𝔭, (U/I_d(F)) ⊗ T_𝔭, 1, d L₀, 0)` at an old
minimal prime `𝔭` (paper (6.2)). -/
noncomputable def oldTest {d F : U} (hd : d ≠ 0) (b : U) (hb : b ≠ 0) (p : Ideal G)
    (hp : p ∈ (D.grIdeal (Id d F)).minimalPrimes) : Test.{u} k U :=
  have : p.IsPrime := hp.1.1
  have := D.isDomain
  have hT := D.isRightFractions p
  { T := D.Tloc p
    ι := D.locAlgHom p
    S := D.denoms p
    frac := hT
    simple := hT.isSimpleRing
    domain := hT.isDomain
    nondivision := ⟨D.locMap p d, fun h => hd (hT.injective (by rw [h, map_zero])),
      not_isUnit_of_le hT hp.1.2 (d_mem_Id d F)⟩
    V := D.Tloc p ⧸ IsRightFractions.extend (ι := D.locMap p) (Id d F)
    artinian := (D.finiteLength hT (Id d F) hp).1
    noetherian := (D.finiteLength hT (Id d F) hp).2
    e := Submodule.Quotient.mk 1
    e_gen := span_mk_one_eq_top _
    b := b
    b_ne := hb
    z := 0 }

end Tests

/-! ### The statement `P_h` -/

/-- `P_h` with finite admissible test lists (paper Target theorem B). -/
def Ph (h : ℕ) : Prop :=
  ∀ (d a : U), d ≠ 0 → a ≠ 0 → ∀ (B : U) (Ω : List (Test.{u} k U)),
    ∃ H : U, (∀ τ ∈ Ω, τ.Satisfies (B + H * a)) ∧
      D.δ (Id d (B + H * a)) + (h : WithBot ℕ∞) ≤ ringKrullDim G

variable [IsSimpleRing U] [Infinite k]

omit [IsNoetherianRing G] in
/-- **Base.**  `P₀` holds: simultaneous source selection (Proposition 4.6) and
the trivial bound `δ ≤ dim G`. -/
theorem Ph_zero : D.Ph 0 := by
  intro d a hd ha B Ω
  have := D.isDomain
  obtain ⟨H, hH⟩ := Test.exists_source Ω B a ha
  refine ⟨H, hH, ?_⟩
  unfold δ
  simpa using ringKrullDim_quotient_le (D.grIdeal (Id d (B + H * a)))

/-- **Remark 5.2 (the ordered identity, constant term).**  A free-ring
identity separating the algebra of (5.8) from the local certificates. -/
theorem remark52_const {R : Type*} [Ring R] (d a₀ v b₀ C₀ z₀ w L₀ : R) :
    d * (a₀ + C₀ * z₀ * w * b₀) + v * (b₀ - L₀ * z₀ * w * b₀) - 1 =
      (d * a₀ + v * b₀ - 1) + (d * C₀ - v * L₀) * z₀ * w * b₀ := by
  noncomm_ring

/-- **Remark 5.2 (the ordered identity, coefficient of `t`).** -/
theorem remark52_coeff {R : Type*} [Ring R] (d c₀ w b₀ L₀ z₀ : R) :
    d * -(c₀ * w * b₀) + w * (b₀ - L₀ * z₀ * w * b₀) =
      -(d * c₀ + w * L₀ * z₀ - 1) * w * b₀ := by
  noncomm_ring

section Successor

variable {D}

omit [IsSimpleRing U] [Infinite k] in
/-- **Lemma 5.1 (support union).**  Every prime containing `gr J` contains
`gr I_d(F)` or `gr I_{dL₀}(G₀)`. -/
theorem support_union {d F G₀ L₀ C₀ : U} (hFd : F * d * L₀ = d * C₀) (q : Ideal G) [q.IsPrime]
    (hq : D.grIdeal (colonJ d F G₀) ≤ q) :
    D.grIdeal (Id d F) ≤ q ∨ D.grIdeal (Id (d * L₀) G₀) ≤ q := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have := D.isDomain
  have hT := D.isRightFractions q
  set ι := D.locMap q
  have e1 := (D.one_mem_extend_iff_not_le hT (Id d F)).mpr h1
  have e2 := (D.one_mem_extend_iff_not_le hT (Id (d * L₀) G₀)).mpr h2
  obtain ⟨a₀, b₀, hab⟩ := mem_extend_Id.mp e1
  obtain ⟨c₀', z₀, hcz⟩ := mem_extend_Id.mp e2
  have hrel : ι (F * d) * ι L₀ = ι d * ι C₀ := by rw [← map_mul, hFd, map_mul]
  have cert2 : ι d * (ι L₀ * c₀') + ι (G₀ * d) * ι L₀ * z₀ = 1 := by
    rw [← hcz]; simp only [map_mul, mul_assoc]
  -- The coefficients (5.7) and the identity (5.8).
  have id0 := remark52_const (ι d) a₀ (ι (F * d)) b₀ (ι C₀) z₀ (ι (G₀ * d)) (ι L₀)
  rw [hab, hrel, sub_self, sub_self, zero_mul, zero_mul, zero_mul, add_zero, sub_eq_zero] at id0
  have id1 := remark52_coeff (ι d) (ι L₀ * c₀') (ι (G₀ * d)) b₀ (ι L₀) z₀
  rw [cert2, sub_self, neg_zero, zero_mul, zero_mul] at id1
  -- One common right denominator.
  obtain ⟨s, hs, hcom⟩ := hT.exists_common ![a₀ + ι C₀ * z₀ * ι (G₀ * d) * b₀,
    -(ι L₀ * c₀' * ι (G₀ * d) * b₀), b₀ - ι L₀ * z₀ * ι (G₀ * d) * b₀]
  obtain ⟨α₀, hα₀⟩ := hcom 0
  obtain ⟨α₁, hα₁⟩ := hcom 1
  obtain ⟨σ₀, hσ₀⟩ := hcom 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hα₀ hα₁ hσ₀
  have hs1 : s = d * α₀ + F * d * σ₀ := by
    apply hT.injective
    have := congrArg (· * ι s) id0
    rw [add_mul, mul_assoc (ι d), mul_assoc (ι (F * d)), one_mul, hα₀, hσ₀] at this
    rw [← this, map_add, map_mul ι d α₀, map_mul ι (F * d) σ₀]
  have hs2 : G₀ * d * σ₀ = d * (-α₁) := by
    apply hT.injective
    have := congrArg (· * ι s) id1
    rw [add_mul, mul_assoc (ι d), mul_assoc (ι (G₀ * d)), zero_mul, hα₁, hσ₀] at this
    rw [map_mul ι (G₀ * d) σ₀, map_mul ι d (-α₁), map_neg]
    exact (eq_neg_of_add_eq_zero_right this).trans (mul_neg (ι d) (ι α₁)).symm
  have hsJ : s ∈ colonJ d F G₀ := ⟨α₀, σ₀, -α₁, hs2, hs1⟩
  exact hs.2 (hq (D.sym_mem_grIdeal hsJ))

end Successor

section

/-- **The successor step** `P_h → P_{h+1}` (paper §6). -/
theorem Ph_succ {h : ℕ} (hP : D.Ph h) : D.Ph (h + 1) := by
  classical
  have := D.isDomain
  intro d a hd ha B Ω
  -- First lower-index call: the old source.
  obtain ⟨H₁, hΩ₁, hδ₁⟩ := hP d a hd ha B Ω
  set F := B + H₁ * a
  set I := Id d F
  -- `F d L₀ = d C₀` from the Ore condition at the zero prime.
  have hd0 : d ∈ D.denoms (⊥ : Ideal G) := ⟨hd, by simpa using D.sym_ne_zero hd⟩
  obtain ⟨L₀, hL₀, C₀, hFd⟩ := D.ore_condition ⊥ (F * d) hd0
  set d₁ := d * L₀
  have hd₁ : d₁ ≠ 0 := D.mul_ne_zero' hd hL₀.1
  -- New tests at the old minimal primes.
  have hPold : (D.grIdeal I).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  let Ωnew : List (Test.{u} k U) :=
    hPold.toFinset.attach.toList.map fun p =>
      D.oldTest hd d₁ hd₁ p.1 ((Set.Finite.mem_toFinset _).mp p.2)
  -- Second lower-index call: the auxiliary divisor.
  obtain ⟨H₂, hΩ₂, hδ₂⟩ := hP d₁ a hd₁ ha 0 Ωnew
  set G₀ := 0 + H₂ * a
  set J := colonJ d F G₀
  -- Support union and `δ(U/J) + h ≤ dim G`.
  have hδJ : D.δ J + (h : WithBot ℕ∞) ≤ ringKrullDim G := by
    have hmax := ringKrullDim_quotient_le_max (J := D.grIdeal J) (J₁ := D.grIdeal I)
      (J₂ := D.grIdeal (Id d₁ G₀)) fun q hq => by
        have : q.IsPrime := hq.1.1
        exact support_union hFd q hq.1.2
    calc D.δ J + (h : WithBot ℕ∞) ≤ max (D.δ I) (D.δ (Id d₁ G₀)) + h :=
          add_le_add_left hmax _
      _ ≤ ringKrullDim G := by
          rcases le_total (D.δ I) (D.δ (Id d₁ G₀)) with hle | hle
          · rw [max_eq_right hle]; exact hδ₂
          · rw [max_eq_left hle]; exact hδ₁
  -- The minimal components of `U/J`.
  have hPJ : (D.grIdeal J).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  -- For each such component, the exceptional scalars are finite.
  let v : ∀ q, q ∈ (D.grIdeal J).minimalPrimes → Set k := fun q hq => by
    have : q.IsPrime := hq.1.1
    exact {l : k | Submodule.span (D.Tloc q)ᵐᵒᵖ
          {(Submodule.Quotient.mk (D.locMap q (F * d)) :
              D.Tloc q ⧸ IsRightFractions.extend (ι := D.locMap q) J) +
            algebraMap k (D.Tloc q)ᵐᵒᵖ l •
              Submodule.Quotient.mk (D.locMap q (G₀ * d))} ≠ ⊤}
  have hbad : ∀ q (hq : q ∈ (D.grIdeal J).minimalPrimes), (v q hq).Finite := by
    intro q hq
    have : q.IsPrime := hq.1.1
    have hT := D.isRightFractions q
    set ι := D.locMap q
    set E := IsRightFractions.extend (ι := ι) J
    have hfin := D.finiteLength hT J hq
    have := hfin.1
    have he : Submodule.span (D.Tloc q)ᵐᵒᵖ {(Submodule.Quotient.mk 1 : D.Tloc q ⧸ E)} = ⊤ :=
      span_mk_one_eq_top E
    have hdE : ι d ∈ E := IsRightFractions.map_mem_extend (d_mem_colonJ d F G₀)
    show {l : k | _}.Finite
    by_cases hold : D.grIdeal I ≤ q
    · -- Old component: `q` is an old minimal prime; use its test.
      have hqold : q ∈ (D.grIdeal I).minimalPrimes := by
        refine ⟨⟨hq.1.1, hold⟩, fun r hr hrq => ?_⟩
        exact hq.2 ⟨hr.1, le_trans (D.grIdeal_mono (colonJ_le_Id_self d F G₀)) hr.2⟩ hrq
      have htest : (D.oldTest hd d₁ hd₁ q hqold).Satisfies (0 + H₂ * a) := by
        apply hΩ₂
        simp only [Ωnew, List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and]
        exact ⟨⟨q, (Set.Finite.mem_toFinset _).mpr hqold⟩, rfl⟩
      -- Unpack the test: `1 = d α + F d β + G₀ d L₀ τ` in `T_q`.
      have htest' : Submodule.span (D.Tloc q)ᵐᵒᵖ
          {(0 : D.Tloc q ⧸ IsRightFractions.extend (ι := ι) I) +
            op (ι (G₀ * d₁)) • Submodule.Quotient.mk 1} = ⊤ := htest
      have hgen : (Submodule.Quotient.mk 1 : D.Tloc q ⧸ IsRightFractions.extend (ι := ι) I) ∈
          Submodule.span (D.Tloc q)ᵐᵒᵖ {0 + op (ι (G₀ * d₁)) • Submodule.Quotient.mk 1} :=
        htest' ▸ Submodule.mem_top
      rw [zero_add, Submodule.mem_span_singleton] at hgen
      obtain ⟨τ', hτ'⟩ := hgen
      have hx : (Submodule.Quotient.mk (ι (G₀ * d₁) * unop τ') :
          D.Tloc q ⧸ IsRightFractions.extend (ι := ι) I) = Submodule.Quotient.mk 1 := by
        rw [← hτ', ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, op_smul_eq_mul,
          one_mul, smul_eq_mul_unop]
      rw [Submodule.Quotient.eq] at hx
      have hx' := Submodule.neg_mem _ hx
      rw [neg_sub] at hx'
      obtain ⟨α, β, hαβ⟩ := mem_extend_Id.mp hx'
      set τ := unop τ'
      refine activated_pencil_finite (k := k) (A := (D.Tloc q)ᵐᵒᵖ) he
        (B := op β) (L := op (ι L₀ * τ)) ?_ ?_
      · rw [← Submodule.Quotient.mk_smul, op_smul_eq_mul, Submodule.Quotient.mk_eq_zero]
        have : ι (F * d) * (ι L₀ * τ) = ι d * (ι C₀ * τ) := by
          rw [← mul_assoc, ← map_mul, hFd, map_mul, mul_assoc]
        rw [this]
        have := E.smul_mem (op (ι C₀ * τ)) hdE
        rwa [op_smul_eq_mul] at this
      · rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
          op_smul_eq_mul, op_smul_eq_mul, ← Submodule.Quotient.mk_add, eq_comm,
          Submodule.Quotient.eq]
        have h2 : ι (G₀ * d₁) = ι (G₀ * d) * ι L₀ := by
          rw [show G₀ * d₁ = G₀ * d * L₀ from (mul_assoc _ _ _).symm, map_mul]
        have hkey : ι (F * d) * β + ι (G₀ * d) * (ι L₀ * τ) - 1 = -(ι d * α) := by
          rw [← mul_assoc, ← h2]
          have : ι (F * d) * β = 1 - ι (G₀ * d₁) * τ - ι d * α := by rw [← hαβ]; abel
          rw [this]; abel
        rw [hkey]
        refine E.neg_mem ?_
        have := E.smul_mem (op α) hdE
        rwa [op_smul_eq_mul] at this
    · -- New component: `v` already generates.
      have h1 := (D.one_mem_extend_iff_not_le hT I).mpr hold
      obtain ⟨α, β, hαβ⟩ := mem_extend_Id.mp h1
      have hv : Submodule.span (D.Tloc q)ᵐᵒᵖ {(Submodule.Quotient.mk (ι (F * d)) :
          D.Tloc q ⧸ E)} = ⊤ := by
        rw [eq_top_iff, ← he, Submodule.span_le, Set.singleton_subset_iff,
          SetLike.mem_coe, Submodule.mem_span_singleton]
        refine ⟨op β, ?_⟩
        rw [← Submodule.Quotient.mk_smul, op_smul_eq_mul, Submodule.Quotient.eq]
        have : ι (F * d) * β - 1 = -(ι d * α) := by rw [← hαβ]; abel
        rw [this]
        refine E.neg_mem ?_
        have := E.smul_mem (op α) hdE
        rwa [op_smul_eq_mul] at this
      exact generator_pencil_finite (k := k) hv _
  -- Carried tests (6.8).
  have hcarried : ∀ τ ∈ Ω, {l : k | ¬ τ.Satisfies (F + algebraMap k U l * G₀)}.Finite :=
    fun τ hτ => τ.satisfies_pencil_finite (hΩ₁ τ hτ) G₀
  -- One scalar avoiding every exceptional set.
  have hfinite : ((⋃ q, ⋃ (hq : q ∈ (D.grIdeal J).minimalPrimes), v q hq) ∪
      ⋃ τ ∈ {τ | τ ∈ Ω}, {l : k | ¬ τ.Satisfies (F + algebraMap k U l * G₀)}).Finite :=
    (hPJ.biUnion' hbad).union ((List.finite_toSet Ω).biUnion hcarried)
  obtain ⟨l, hl⟩ := hfinite.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hl
  obtain ⟨hlJ, hlΩ⟩ := hl
  set F' := F + algebraMap k U l * G₀
  have hF' : B + (H₁ + algebraMap k U l * H₂) * a = F' := by
    simp only [F', F, G₀, zero_add]; noncomm_ring
  refine ⟨H₁ + algebraMap k U l * H₂, ?_, ?_⟩
  · intro τ hτ
    rw [hF']
    by_contra hns
    exact hlΩ τ hτ hns
  -- The strict dimension drop (6.9)–(6.10).
  rw [hF']
  have hJF' : J ≤ Id d F' := colonJ_le_Id d F G₀ l
  have hmiss : ∀ q ∈ (D.grIdeal J).minimalPrimes, ¬ D.grIdeal (Id d F') ≤ q := by
    intro q hq
    have : q.IsPrime := hq.1.1
    have hT := D.isRightFractions q
    set ι := D.locMap q
    have hgen := hlJ q hq
    simp only [v, Set.mem_ofPred_eq, not_not] at hgen
    have hvu : (Submodule.Quotient.mk (ι (F * d)) :
        D.Tloc q ⧸ IsRightFractions.extend (ι := ι) J) +
        algebraMap k (D.Tloc q)ᵐᵒᵖ l • Submodule.Quotient.mk (ι (G₀ * d)) =
        Submodule.Quotient.mk (ι (F' * d)) := by
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
      congr 1
      rw [MulOpposite.algebraMap_apply, op_smul_eq_mul, ← Algebra.commutes]
      simp only [F', add_mul, mul_assoc, map_add, map_mul]
      rw [show D.locMap q (algebraMap k U l) = algebraMap k (D.Tloc q) l from rfl]
    rw [hvu] at hgen
    have h1mem : (Submodule.Quotient.mk (1 : D.Tloc q) :
        D.Tloc q ⧸ IsRightFractions.extend (ι := ι) J) ∈
        Submodule.span (D.Tloc q)ᵐᵒᵖ {Submodule.Quotient.mk (ι (F' * d))} :=
      hgen ▸ Submodule.mem_top
    rw [Submodule.mem_span_singleton] at h1mem
    obtain ⟨τ', hτ'⟩ := h1mem
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul_unop] at hτ'
    have hext : IsRightFractions.extend (ι := ι) J ≤ IsRightFractions.extend (ι := ι) (Id d F') :=
      Submodule.span_mono (Set.image_mono hJF')
    have h1 : (1 : D.Tloc q) ∈ IsRightFractions.extend (ι := ι) (Id d F') := by
      have hA := hext hτ'
      have hB : ι (F' * d) * unop τ' ∈ IsRightFractions.extend (ι := ι) (Id d F') := by
        have := (IsRightFractions.extend (ι := ι) (Id d F')).smul_mem (op (unop τ'))
          (IsRightFractions.map_mem_extend (Fd_mem_Id d F'))
        rwa [op_smul_eq_mul] at this
      have := Submodule.sub_mem _ hB hA
      simpa using this
    exact (D.one_mem_extend_iff_not_le hT (Id d F')).mp h1
  have hdrop := ringKrullDim_quotient_add_one_le (D.grIdeal_mono hJF') hmiss
  calc D.δ (Id d F') + ((h + 1 : ℕ) : WithBot ℕ∞)
      = (D.δ (Id d F') + 1) + (h : WithBot ℕ∞) := by push_cast; ring
    _ ≤ D.δ J + (h : WithBot ℕ∞) := add_le_add_left hdrop _
    _ ≤ ringKrullDim G := hδJ

/-- `P_h` for every `h`. -/
theorem Ph_all (h : ℕ) : D.Ph h := by
  induction h with
  | zero => exact D.Ph_zero
  | succ h ih => exact D.Ph_succ ih

include D in
/-- **Target theorem A (affine same-divisor statement).**  For all nonzero
`d, a` and every `B` there are `H, R, S` with `1 = d R + (B + H a) d S`. -/
theorem targetA (hdim : ringKrullDim G < ⊤) (d a : U) (hd : d ≠ 0) (ha : a ≠ 0) (B : U) :
    ∃ H R S : U, 1 = d * R + (B + H * a) * d * S := by
  have := D.isDomain
  -- `dim G` is a natural number.
  have hne : ringKrullDim G ≠ ⊥ := by
    have := ringKrullDim_nonneg_of_nontrivial (R := G)
    intro h; rw [h] at this; exact absurd this (by simp)
  obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hne
  have hxtop : x ≠ ⊤ := by
    rintro rfl; rw [← hx] at hdim; exact absurd hdim (by simp)
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hxtop
  obtain ⟨H, -, hδ⟩ := D.Ph_all (n + 1) d a hd ha B []
  have hbot : D.δ (Id d (B + H * a)) = ⊥ := by
    rw [← hx] at hδ
    rcases hδv : D.δ (Id d (B + H * a)) with _ | y
    · rfl
    · exfalso
      rw [hδv] at hδ
      have h2 : ((y + ((n + 1 : ℕ) : ℕ∞) : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]; exact hδ
      rw [WithBot.coe_le_coe] at h2
      have h3 : ((n + 1 : ℕ) : ℕ∞) ≤ n := le_trans le_add_self h2
      norm_cast at h3
      omega
  have htop := eq_top_of_ringKrullDim_quotient_eq_bot hbot
  have h1 := D.one_mem_of_grIdeal_eq_top htop
  obtain ⟨R, S, hRS⟩ := mem_Id.mp h1
  exact ⟨H, R, S, hRS.symm⟩

end

end FilteredAlgebraData

end SymplecticStafford.Paper
