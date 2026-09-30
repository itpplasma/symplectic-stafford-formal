import SymplecticStafford.Paper.Setting
import SymplecticStafford.Paper.RightFraction
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The local support package (paper §3; closure note Z1–Z9)

For a prime `𝔭` of `G`, let `S_𝔭 = {s ≠ 0 : σ(s) ∉ 𝔭}`.  This file proves,
from the standing hypotheses alone:

* **Z1** `ore_condition`: `S_𝔭` satisfies the right Ore condition in `U`.  The
  proof compares the quotient and induced filtrations on `(cU + sU)/sU` using
  Artin–Rees in `U` (`artinRees`); commutativity of `G` makes right
  multiplication by `s` lower the induced degree by one.
* The actual localization `Tloc 𝔭 = U S_𝔭⁻¹`, built from Mathlib's Ore
  localization of `Uᵐᵒᵖ`, is a ring of right fractions (`isRightFractions`).
* **Z3** Elements `1 + y` with `deg y < 0` are units with inverse of degree
  `≤ 0` (`unit_of_neg`), stated for fractions `y ι(s) = ι(a)`,
  `deg a < deg s`.  With the Nakayama elimination `nakayama_rows` this gives
  the Zariskian separation used in the survival theorem.
* **Z6/Z8 survival** `survival`: if `I₁ ⊆ I₂` are right ideals, `I₁` is
  `S_𝔭`-saturated and some `σ(s) ∉ 𝔭` multiplies `gr I₂` into `gr I₁`, then
  `I₁ = I₂`.
* **Z8** `finiteLength`: if `𝔭` is minimal over `gr I`, the localized cyclic
  module `T ⧸ I T` has finite length.  Chains of submodules pull back to
  saturated right ideals of `U`, whose graded ideals give a strict chain in
  the Artinian ring `(G ⧸ gr I)_𝔭`.
* **Z7(b)** detection `one_mem_extend_iff_not_le`: `I T = T` iff
  `gr I ⊄ 𝔭`, and **Z9** nondivision of `T` at primes of the support.

Everything is proved for an arbitrary ring of right fractions `(T, ι)` with
denominators `S_𝔭`, and then applied to `Tloc 𝔭`.
-/

namespace SymplecticStafford.Paper

open DirectSum MulOpposite

/-! ### Nakayama elimination for finitely many relations -/

/-- **Nakayama elimination.**  Let `N ⊆ O` be subsets of a ring with `N + N ⊆ N`,
`N O ⊆ N`, and such that each `1 - y` (`y ∈ N`) has a right inverse in `O`.  If
finitely many elements of a right module satisfy `mⱼ = Σᵢ mᵢ yᵢⱼ` with all
`yᵢⱼ ∈ N`, then all `mⱼ = 0`. -/
theorem nakayama_rows {R : Type*} [Ring R] (N O : Set R)
    (hN : ∀ x ∈ N, ∀ y ∈ N, x + y ∈ N) (hNO : ∀ x ∈ N, ∀ y ∈ O, x * y ∈ N)
    (hNsub : N ⊆ O) (hinv : ∀ y ∈ N, ∃ w ∈ O, (1 - y) * w = 1)
    {M : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    ∀ (n : ℕ) (m : Fin n → M) (y : Fin n → Fin n → R), (∀ i j, y i j ∈ N) →
      (∀ j, m j = ∑ i, op (y i j) • m i) → ∀ j, m j = 0 := by
  intro n
  induction n with
  | zero => intro m y _ _ j; exact j.elim0
  | succ n ih =>
    intro m y hy hm
    obtain ⟨w, hwO, hw⟩ := hinv _ (hy (Fin.last n) (Fin.last n))
    -- Solve for `m (Fin.last n)`.
    have hmL : m (Fin.last n) = ∑ i : Fin n, op (y i.castSucc (Fin.last n) * w) • m i.castSucc := by
      have h := hm (Fin.last n)
      rw [Fin.sum_univ_castSucc] at h
      have h2 : op (1 - y (Fin.last n) (Fin.last n)) • m (Fin.last n) = ∑ i : Fin n, op (y i.castSucc (Fin.last n)) • m i.castSucc := by
        rw [op_sub, op_one, sub_smul, one_smul]
        nth_rewrite 1 [h]
        abel
      calc m (Fin.last n) = op w • op (1 - y (Fin.last n) (Fin.last n)) • m (Fin.last n) := by
              rw [← mul_smul, ← op_mul, hw, op_one, one_smul]
        _ = _ := by
              rw [h2, Finset.smul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← mul_smul, ← op_mul]
    -- New relations among the first `n` elements.
    set y' : Fin n → Fin n → R :=
      fun i j => y i.castSucc j.castSucc + y i.castSucc (Fin.last n) * w * y (Fin.last n) j.castSucc
    have hy' : ∀ i j, y' i j ∈ N := fun i j =>
      hN _ (hy _ _) _ (hNO _ (hNO _ (hy _ _) _ hwO) _ (hNsub (hy _ _)))
    have hm' : ∀ j : Fin n, m j.castSucc = ∑ i, op (y' i j) • m i.castSucc := by
      intro j
      have h := hm j.castSucc
      rw [Fin.sum_univ_castSucc, hmL, Finset.smul_sum] at h
      rw [h, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [y', op_add, add_smul, ← mul_smul, ← op_mul, mul_assoc]
    have hzero := ih (fun j => m j.castSucc) y' hy' hm'
    intro j
    refine Fin.lastCases ?_ (fun j => hzero j) j
    rw [hmL]
    simp [hzero]

namespace FilteredAlgebraData

variable {k U G : Type*} [Field k] [Ring U] [Algebra k U] [CommRing G] [Algebra k G]
variable {𝒜 : ℕ → Submodule k G} [GradedAlgebra 𝒜]
variable (D : FilteredAlgebraData k U G 𝒜)

/-! ### Integer-indexed Artin–Rees and the commutator estimate -/

theorem artinReesZ [IsNoetherianRing G] (I : Submodule Uᵐᵒᵖ U) :
    ∃ (m : ℕ) (x : Fin m → U) (kk : Fin m → ℕ), (∀ i, x i ∈ I ∧ x i ∈ D.F (kk i)) ∧
      ∀ (n : ℤ) (u : U), u ∈ I → u ∈ D.Fz n → ∃ v : Fin m → U,
        (∀ i, v i ∈ D.Fz (n - kk i)) ∧ u = ∑ i, x i * v i := by
  obtain ⟨m, x, kk, hx, hdec⟩ := D.artinRees I
  refine ⟨m, x, kk, hx, fun n u hu hun => ?_⟩
  by_cases hn : n < 0
  · rw [D.Fz_of_neg hn, Submodule.mem_bot] at hun
    exact ⟨0, fun i => by simp, by simp [hun]⟩
  · rw [D.Fz_of_nonneg (by omega)] at hun
    obtain ⟨v, hv, hsum⟩ := hdec _ u hu hun
    refine ⟨v, fun i => ?_, hsum⟩
    by_cases hi : n - kk i < 0
    · rw [(hv i).2 (by omega)]; exact Submodule.zero_mem _
    · rw [D.Fz_of_nonneg (by omega)]
      have := (hv i).1
      rwa [show n.toNat - kk i = (n - kk i).toNat by omega] at this

/-- Symbols commute: `r s - s r` has degree below `deg r + deg s`. -/
lemma comm_mem_Fz {a : ℤ} {n : ℕ} {r s : U} (hr : r ∈ D.Fz a) (hs : s ∈ D.F n) :
    r * s - s * r ∈ D.Fz (a + n - 1) := by
  by_cases ha : a < 0
  · rw [D.Fz_of_neg ha, Submodule.mem_bot] at hr; simp [hr]
  rw [D.Fz_of_nonneg (by omega)] at hr
  have hrs : r * s ∈ D.F (a.toNat + n) := D.mul_mem hr hs
  have hsr : s * r ∈ D.F (a.toNat + n) := by
    have := D.mul_mem hs hr; rwa [add_comm] at this
  have h := (D.grAt_eq_grAt_iff hrs hsr).mp (by
    rw [D.grAt_mul hr hs, D.grAt_mul' (add_comm n a.toNat) hs hr, mul_comm])
  rw [D.Flow_eq_Fz] at h
  convert h using 2
  push_cast; omega

/-- A right ideal `span {c, s}` has elements `c w + s v`. -/
lemma mem_span_pair_iff {c s x : U} :
    x ∈ Submodule.span Uᵐᵒᵖ {c, s} ↔ ∃ w v : U, c * w + s * v = x := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩; exact ⟨unop a, unop b, h⟩
  · rintro ⟨w, v, h⟩; exact ⟨op w, op v, h⟩

section Domain

variable [IsDomain G]

/-! ### Z1: the Ore condition for `S_𝔭` -/

/-- **Lemma Z1 (right Ore condition).**  For `s ∈ S_𝔭` and `c ∈ U` there are
`t ∈ S_𝔭` and `b` with `c t = s b`. -/
theorem ore_condition [IsNoetherianRing G] (p : Ideal G) [p.IsPrime] (c : U) {s : U}
    (hs : s ∈ D.denoms p) : ∃ t ∈ D.denoms p, ∃ b : U, c * t = s * b := by
  classical
  set A : Submodule Uᵐᵒᵖ U := Submodule.span Uᵐᵒᵖ {c, s}
  have hcA : c ∈ A := Submodule.subset_span (Set.mem_insert c _)
  have hsA : ∀ v, s * v ∈ A := fun v => by
    have := A.smul_mem (op v) (Submodule.subset_span (Set.mem_insert_of_mem c rfl))
    rwa [op_smul_eq_mul] at this
  set d := D.deg s
  -- The iterated commutator estimate.
  have iter : ∀ N : ℕ, ∃ r ∈ A, r ∈ D.Fz ((D.deg c : ℤ) + N * ((d : ℤ) - 1)) ∧
      ∃ β : U, c * s ^ N = r + s * β := by
    intro N
    induction N with
    | zero => exact ⟨c, hcA, by simpa using D.mem_Fz_deg c, 0, by simp⟩
    | succ N ih =>
      obtain ⟨r, hrA, hrF, β, hβ⟩ := ih
      have hrs : r * s ∈ A := by
        have := A.smul_mem (op s) hrA; rwa [op_smul_eq_mul] at this
      refine ⟨r * s - s * r, A.sub_mem hrs (hsA r), ?_, r + β * s, ?_⟩
      · have := D.comm_mem_Fz hrF (D.mem_F_deg s)
        convert this using 2; push_cast; ring
      · rw [pow_succ, ← mul_assoc, hβ]; noncomm_ring
  -- Artin–Rees for `A` and the expressions of its generators.
  obtain ⟨m, xs, kk, hxs, hdec⟩ := D.artinReesZ A
  have hWV : ∀ i, ∃ w v : U, c * w + s * v = xs i := fun i =>
    (mem_span_pair_iff).mp (hxs i).1
  choose W V hWV using hWV
  set E : ℕ := ∑ i, D.deg (W i)
  have hWE : ∀ i, D.deg (W i) ≤ E := fun i =>
    Finset.single_le_sum (f := fun i => D.deg (W i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  set N : ℕ := D.deg c + E + 1
  obtain ⟨r, hrA, hrF, β, hβ⟩ := iter N
  obtain ⟨v', hv', hr⟩ := hdec _ r hrA hrF
  set w : U := ∑ i, W i * v' i
  set β' : U := ∑ i, V i * v' i
  have hrw : r = c * w + s * β' := by
    rw [hr]
    simp only [w, β', Finset.mul_sum, ← Finset.sum_add_distrib, ← mul_assoc, ← add_mul, hWV]
  -- `w` has degree `< N d`.
  have hwF : w ∈ D.Fz ((N : ℤ) * d - 1) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 := D.Fz_mul_mem (D.mem_Fz_deg (W i)) (hv' i)
    refine D.Fz_mono ?_ h1
    have := hWE i
    push_cast [N]
    nlinarith
  -- The denominator `t = s^N - w`.
  have hsN : s ^ N ∈ D.F (N * d) := by
    have := D.mem_F_deg (s ^ N); rwa [D.deg_pow hs.1] at this
  have hwF' : w ∈ D.Flow (N * d) := by
    rw [D.Flow_eq_Fz]; push_cast; exact hwF
  have hwN : w ∈ D.F (N * d) := D.Flow_le _ hwF'
  have hgt : D.grAt (N * d) (s ^ N - w) = D.sym s ^ N := by
    rw [D.grAt_sub hsN hwN, (D.grAt_eq_zero_iff hwN).mpr hwF', sub_zero,
      ← D.sym_pow, ← D.deg_pow hs.1]
    rfl
  have hne : D.sym s ^ N ≠ 0 := pow_ne_zero _ (D.sym_ne_zero hs.1)
  have hsym : D.sym (s ^ N - w) = D.sym s ^ N := by
    rw [← D.grAt_eq_sym (Submodule.sub_mem _ hsN hwN) (by rw [hgt]; exact hne), hgt]
  refine ⟨s ^ N - w, ⟨?_, ?_⟩, β' + β, ?_⟩
  · intro h0; apply hne; rw [← hsym, h0, D.sym_zero]
  · rw [hsym]; exact fun h => hs.2 (‹p.IsPrime›.mem_of_pow_mem _ h)
  · rw [mul_sub, hβ, hrw]; noncomm_ring

/-- Both Ore factors can be taken in `S_𝔭` when both inputs are. -/
theorem ore_both [IsNoetherianRing G] (p : Ideal G) [p.IsPrime] {c s : U}
    (hc : c ∈ D.denoms p) (hs : s ∈ D.denoms p) :
    ∃ t ∈ D.denoms p, ∃ b ∈ D.denoms p, c * t = s * b := by
  obtain ⟨t, ht, b, hcb⟩ := D.ore_condition p c hs
  refine ⟨t, ht, b, ⟨?_, ?_⟩, hcb⟩
  · rintro rfl
    rw [mul_zero] at hcb
    exact D.mul_ne_zero' hc.1 ht.1 hcb
  · intro hb
    have := congrArg D.sym hcb
    rw [D.sym_mul, D.sym_mul] at this
    have hmem : D.sym s * D.sym b ∈ p := p.mul_mem_left _ hb
    rw [← this] at hmem
    rcases ‹p.IsPrime›.mem_or_mem hmem with h | h
    · exact hc.2 h
    · exact ht.2 h

/-! ### The localization `T_𝔭` -/

variable [IsNoetherianRing G]

/-- The left Ore set `S_𝔭ᵐᵒᵖ` of `Uᵐᵒᵖ` (the right Ore condition of Z1). -/
noncomputable instance oreSet (p : Ideal G) [p.IsPrime] :
    OreLocalization.OreSet (D.denoms p).op := by
  classical
  have h : ∀ (r : Uᵐᵒᵖ) (s : (D.denoms p).op),
      ∃ (r' : Uᵐᵒᵖ) (s' : (D.denoms p).op), (s' : Uᵐᵒᵖ) * r = r' * s := by
    intro r s
    obtain ⟨t, ht, b, hcb⟩ := D.ore_condition p r.unop (Submonoid.mem_op.mp s.2)
    refine ⟨op b, ⟨op t, Submonoid.mem_op.mpr ht⟩, ?_⟩
    apply MulOpposite.unop_injective
    simp [hcb]
  choose r' s' hrs using h
  haveI := D.noZeroDivisors
  exact OreLocalization.oreSetOfNoZeroDivisors r' s' hrs

/-- The actual localization `T_𝔭 = U S_𝔭⁻¹` (paper (3.3)). -/
abbrev Tloc (p : Ideal G) [p.IsPrime] : Type _ :=
  (OreLocalization (D.denoms p).op Uᵐᵒᵖ)ᵐᵒᵖ

/-- The localization map `U → T_𝔭`. -/
noncomputable def locMap (p : Ideal G) [p.IsPrime] : U →+* D.Tloc p :=
  (RingHom.op (OreLocalization.numeratorRingHom (R := Uᵐᵒᵖ) (S := (D.denoms p).op))).comp
    (RingEquiv.opOp U).toRingHom

lemma locMap_apply (p : Ideal G) [p.IsPrime] (u : U) :
    D.locMap p u = op (OreLocalization.numeratorRingHom (op u)) := rfl

/-- `T_𝔭` is a ring of right fractions of `U` with denominators `S_𝔭`. -/
theorem isRightFractions (p : Ideal G) [p.IsPrime] :
    IsRightFractions (D.denoms p) (D.locMap p) where
  injective := by
    haveI := D.noZeroDivisors
    intro a b h
    rw [locMap_apply, locMap_apply] at h
    have h' := MulOpposite.op_injective h
    have := OreLocalization.numeratorHom_inj (R := Uᵐᵒᵖ) (S := (D.denoms p).op) ?_ h'
    · exact MulOpposite.op_injective this
    · intro s hs y hy
      have hs' : unop s ≠ 0 := (Submonoid.mem_op.mp hs).1
      have : unop y * unop s = 0 := by rw [← unop_mul, hy, unop_zero]
      rcases mul_eq_zero.mp this with h0 | h0
      · exact MulOpposite.unop_injective h0
      · exact absurd h0 hs'
  isUnit := by
    intro s hs
    have := OreLocalization.numerator_isUnit (R := Uᵐᵒᵖ) (⟨op s, Submonoid.mem_op.mpr hs⟩ :
      (D.denoms p).op)
    rw [locMap_apply]
    exact this.op
  surj := by
    intro τ
    induction τ using MulOpposite.rec' with
    | _ x =>
    induction x using OreLocalization.ind with
    | _ r s =>
    refine ⟨unop r, unop (s : Uᵐᵒᵖ), Submonoid.mem_op.mp s.2, ?_⟩
    rw [locMap_apply, locMap_apply, op_unop, op_unop, ← op_mul]
    congr 1
    exact OreLocalization.mul_cancel

variable {T : Type*} [Ring T] {ι : U →+* T} {p : Ideal G} [p.IsPrime]

/-! ### Degree sets in `T` and the unit property Z3 -/

/-- Fractions of degree `≤ m`: `y ι(s) = ι(a)` with `deg a ≤ deg s + m`. -/
def degLE (ι : U →+* T) (p : Ideal G) [p.IsPrime] (m : ℤ) : Set T :=
  {y | ∃ a s, s ∈ D.denoms p ∧ y * ι s = ι a ∧ a ∈ D.Fz (D.deg s + m)}

variable {D}

lemma zero_mem_degLE (m : ℤ) : (0 : T) ∈ D.degLE ι p m :=
  ⟨0, 1, (D.denoms p).one_mem, by simp, Submodule.zero_mem _⟩

lemma degLE_mono {m n : ℤ} (h : m ≤ n) : D.degLE ι p m ⊆ D.degLE ι p n := by
  rintro y ⟨a, s, hs, hy, ha⟩
  exact ⟨a, s, hs, hy, D.Fz_mono (by omega) ha⟩

lemma add_mem_degLE (hT : IsRightFractions (D.denoms p) ι) {m : ℤ} {y₁ y₂ : T}
    (h₁ : y₁ ∈ D.degLE ι p m) (h₂ : y₂ ∈ D.degLE ι p m) : y₁ + y₂ ∈ D.degLE ι p m := by
  obtain ⟨a₁, s₁, hs₁, hy₁, ha₁⟩ := h₁
  obtain ⟨a₂, s₂, hs₂, hy₂, ha₂⟩ := h₂
  obtain ⟨u, hu, v, hv, huv⟩ := D.ore_both p hs₁ hs₂
  refine ⟨a₁ * u + a₂ * v, s₁ * u, (D.denoms p).mul_mem hs₁ hu, ?_, ?_⟩
  · have e1 : y₁ * ι (s₁ * u) = ι (a₁ * u) := by rw [map_mul, ← mul_assoc, hy₁, map_mul]
    have e2 : y₂ * ι (s₁ * u) = ι (a₂ * v) := by rw [huv, map_mul, ← mul_assoc, hy₂, map_mul]
    rw [add_mul, e1, e2, map_add]
  · have hdu : (D.deg (s₁ * u) : ℤ) = D.deg s₁ + D.deg u := by
      rw [D.deg_mul hs₁.1 hu.1]; push_cast; ring
    have hdv : (D.deg (s₁ * u) : ℤ) = D.deg s₂ + D.deg v := by
      rw [huv, D.deg_mul hs₂.1 hv.1]; push_cast; ring
    refine Submodule.add_mem _ ?_ ?_
    · refine D.Fz_mono ?_ (D.Fz_mul_mem ha₁ (D.mem_Fz_deg u)); omega
    · refine D.Fz_mono ?_ (D.Fz_mul_mem ha₂ (D.mem_Fz_deg v)); omega

lemma mul_mem_degLE (hT : IsRightFractions (D.denoms p) ι) {m n : ℤ} {y z : T}
    (hy : y ∈ D.degLE ι p m) (hz : z ∈ D.degLE ι p n) : y * z ∈ D.degLE ι p (m + n) := by
  obtain ⟨a, s, hs, hya, ha⟩ := hy
  obtain ⟨b, t, ht, hzb, hb⟩ := hz
  by_cases hb0 : b = 0
  · have : z = 0 := hT.eq_zero_of_mul_unit ht (by rw [hzb, hb0, map_zero])
    rw [this, mul_zero]; exact zero_mem_degLE _
  obtain ⟨s', hs', b', hbb'⟩ := D.ore_condition p b hs
  have hb'0 : b' ≠ 0 := by
    rintro rfl; rw [mul_zero] at hbb'; exact D.mul_ne_zero' hb0 hs'.1 hbb'
  refine ⟨a * b', t * s', (D.denoms p).mul_mem ht hs', ?_, ?_⟩
  · rw [map_mul, ← mul_assoc, mul_assoc y, hzb, mul_assoc, ← map_mul, hbb', map_mul,
      ← mul_assoc, hya, map_mul]
  · have hdeg : D.deg b + D.deg s' = D.deg s + D.deg b' := by
      rw [← D.deg_mul hb0 hs'.1, ← D.deg_mul hs.1 hb'0, hbb']
    have hbt : (D.deg b : ℤ) ≤ D.deg t + n := by
      rcases D.mem_Fz_iff.mp hb with h | h
      · exact absurd h hb0
      · exact h
    have hts : (D.deg (t * s') : ℤ) = D.deg t + D.deg s' := by
      rw [D.deg_mul ht.1 hs'.1]; push_cast; ring
    refine D.Fz_mono ?_ (D.Fz_mul_mem ha (D.mem_Fz_deg b'))
    have : (D.deg b : ℤ) + D.deg s' = D.deg s + D.deg b' := by exact_mod_cast hdeg
    omega

/-- **Lemma Z3(b).**  If `deg y < 0` then `1 - y` has a right inverse of degree
`≤ 0` (indeed it is a unit). -/
lemma unit_of_neg (hT : IsRightFractions (D.denoms p) ι) {y : T} (hy : y ∈ D.degLE ι p (-1)) :
    ∃ w ∈ D.degLE ι p 0, (1 - y) * w = 1 := by
  obtain ⟨a, s, hs, hya, ha⟩ := hy
  have haF : a ∈ D.Flow (D.deg s) := by rw [D.Flow_eq_Fz]; simpa [sub_eq_add_neg] using ha
  have hsF := D.mem_F_deg s
  have haF' := D.Flow_le _ haF
  have hg : D.grAt (D.deg s) (s - a) = D.sym s := by
    rw [D.grAt_sub hsF haF', (D.grAt_eq_zero_iff haF').mpr haF, sub_zero]; rfl
  have hsa : s - a ∈ D.denoms p := by
    have hne : D.grAt (D.deg s) (s - a) ≠ 0 := by rw [hg]; exact D.sym_ne_zero hs.1
    have hsym := D.grAt_eq_sym (Submodule.sub_mem _ hsF haF') hne
    refine ⟨fun h0 => ?_, ?_⟩
    · rw [h0, grAt_zero] at hne; exact hne rfl
    · rw [← hsym, hg]; exact hs.2
  have hdeg : D.deg (s - a) = D.deg s :=
    D.deg_eq_of_grAt_ne_zero (Submodule.sub_mem _ hsF haF') (by rw [hg]; exact D.sym_ne_zero hs.1)
  obtain ⟨u, hu⟩ := hT.isUnit _ hsa
  refine ⟨ι s * ↑u⁻¹, ⟨s, s - a, hsa, by simp [← hu], ?_⟩, ?_⟩
  · rw [hdeg, add_zero]; exact D.mem_Fz_deg s
  · have h1 : (1 - y) * ι s = ι (s - a) := by rw [sub_mul, one_mul, hya, map_sub]
    rw [← mul_assoc, h1, ← hu, Units.mul_inv]

/-! ### Z6/Z8: survival of strict inclusions -/

/-- **Survival.**  Let `I₁ ⊆ I₂` be right ideals with `I₁` saturated for `S_𝔭`.
If `σ(s) · gr I₂ ⊆ gr I₁` for some `s ∈ S_𝔭`, then `I₁ = I₂`.  This is the
separatedness statement Z6 applied to `I₂ / I₁`, proved with Artin–Rees in
`U`, the unit property Z3 and Nakayama elimination in `T_𝔭`. -/
theorem survival (hT : IsRightFractions (D.denoms p) ι) {I₁ I₂ : Submodule Uᵐᵒᵖ U}
    (h12 : I₁ ≤ I₂) (hsat : ∀ a, ∀ s ∈ D.denoms p, a * s ∈ I₁ → a ∈ I₁)
    {s : U} (hs : s ∈ D.denoms p)
    (hkill : ∀ g ∈ D.grIdeal I₂, D.sym s * g ∈ D.grIdeal I₁) : I₂ ≤ I₁ := by
  classical
  set d := D.deg s
  -- One step: right multiplication by `s` lowers the relative degree.
  have step : ∀ (m : ℤ) (x : U), x ∈ I₂ → x ∈ D.Fz m →
      ∃ y ∈ I₁, x * s - y ∈ I₂ ∧ x * s - y ∈ D.Fz (m + d - 1) := by
    intro m x hx hxm
    by_cases hm : m < 0
    · rw [D.Fz_of_neg hm, Submodule.mem_bot] at hxm
      exact ⟨0, I₁.zero_mem, by simp [hxm], by simp [hxm]⟩
    rw [D.Fz_of_nonneg (by omega)] at hxm
    set n := m.toNat
    have hg := D.grAt_mem_grIdeal hx hxm
    have hk := hkill _ hg
    have hhom : D.sym s * D.grAt n x ∈ 𝒜 (d + n) :=
      SetLike.GradedMul.mul_mem (D.sym_mem s) (D.grAt_mem n x)
    obtain ⟨y, hyI, hyF, hyg⟩ := D.exists_of_mem_grIdeal hk hhom
    have hxs : x * s ∈ D.F (d + n) := by
      have := D.mul_mem hxm (D.mem_F_deg s); rwa [add_comm] at this
    refine ⟨y, hyI, I₂.sub_mem ?_ (h12 hyI), ?_⟩
    · have := I₂.smul_mem (op s) hx; rwa [op_smul_eq_mul] at this
    · have h := (D.grAt_eq_grAt_iff hxs hyF).mp (by
        rw [hyg, D.grAt_mul' (add_comm n d) hxm (D.mem_F_deg s), mul_comm]; rfl)
      rw [D.Flow_eq_Fz] at h
      convert h using 2
      push_cast; omega
  -- Iteration.
  have iter : ∀ (N : ℕ) (m : ℤ) (x : U), x ∈ I₂ → x ∈ D.Fz m →
      ∃ y ∈ I₁, x * s ^ N - y ∈ I₂ ∧ x * s ^ N - y ∈ D.Fz (m + N * ((d : ℤ) - 1)) := by
    intro N
    induction N with
    | zero => intro m x hx hxm; exact ⟨0, I₁.zero_mem, by simpa using hx, by simpa using hxm⟩
    | succ N ih =>
      intro m x hx hxm
      obtain ⟨y, hyI, hr2, hrF⟩ := ih m x hx hxm
      obtain ⟨y', hy'I, hr2', hrF'⟩ := step _ _ hr2 hrF
      refine ⟨y * s + y', I₁.add_mem ?_ hy'I, ?_, ?_⟩
      · have := I₁.smul_mem (op s) hyI; rwa [op_smul_eq_mul] at this
      · convert hr2' using 1; rw [pow_succ]; noncomm_ring
      · have e1 : x * s ^ (N + 1) - (y * s + y') = (x * s ^ N - y) * s - y' := by
          rw [pow_succ]; noncomm_ring
        have e2 : m + ((N + 1 : ℕ) : ℤ) * ((d : ℤ) - 1) = m + N * ((d : ℤ) - 1) + d - 1 := by
          push_cast; ring
        rw [e1, e2]; exact hrF'
  -- Artin–Rees for `I₂`.
  obtain ⟨M0, xs, kk, hxs, hdec⟩ := D.artinReesZ I₂
  set K : ℕ := ∑ i, kk i
  have hkK : ∀ i, kk i ≤ K := fun i =>
    Finset.single_le_sum (f := kk) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set N : ℕ := K + 1
  have hsN : s ^ N ∈ D.denoms p := (D.denoms p).pow_mem hs N
  have hdegN : D.deg (s ^ N) = N * d := D.deg_pow hs.1 N
  have hrel : ∀ j, ∃ y ∈ I₁, ∃ v : Fin M0 → U, (∀ i, v i ∈ D.Fz ((D.deg (s ^ N) : ℤ) - 1)) ∧
      xs j * s ^ N = y + ∑ i, xs i * v i := by
    intro j
    obtain ⟨y, hyI, hr2, hrF⟩ := iter N (kk j) (xs j) (hxs j).1 (by simpa using (hxs j).2)
    obtain ⟨v, hv, hsum⟩ := hdec _ _ hr2 hrF
    refine ⟨y, hyI, v, fun i => D.Fz_mono ?_ (hv i), ?_⟩
    · rw [hdegN]; have := hkK j; push_cast [N]; nlinarith
    · rw [← hsum]; abel
  choose y hyI v hv hxv using hrel
  obtain ⟨uN, huN⟩ := hT.isUnit _ hsN
  -- Relations in the right module `T ⧸ I₁ T`.
  set Q := IsRightFractions.extend (ι := ι) I₁
  let mk := Q.mkQ
  set z : Fin M0 → Fin M0 → T := fun i j => ι (v j i) * ↑uN⁻¹
  have hz : ∀ i j, z i j ∈ D.degLE ι p (-1) := by
    intro i j
    refine ⟨v j i, s ^ N, hsN, ?_, ?_⟩
    · simp [z, ← huN]
    · simpa [sub_eq_add_neg] using hv j i
  have hm : ∀ j, mk (ι (xs j)) = ∑ i, op (z i j) • mk (ι (xs i)) := by
    intro j
    have h1 : ι (xs j) = ι (y j) * ↑uN⁻¹ + ∑ i, ι (xs i) * z i j := by
      have := congrArg (fun x => ι x * (↑uN⁻¹ : T)) (hxv j)
      simp only [map_mul, map_add, map_sum, Finset.sum_mul, add_mul] at this
      rw [← huN, mul_assoc, Units.mul_inv, mul_one] at this
      rw [this]
      simp [z, mul_assoc]
    rw [h1, map_add, map_sum]
    have hQ : mk (ι (y j) * ↑uN⁻¹) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have := Q.smul_mem (op (↑uN⁻¹ : T)) (IsRightFractions.map_mem_extend (hyI j))
      rwa [op_smul_eq_mul] at this
    rw [hQ, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← LinearMap.map_smul, op_smul_eq_mul]
  have hzero := nakayama_rows (D.degLE ι p (-1)) (D.degLE ι p 0)
    (fun _ h₁ _ h₂ => add_mem_degLE hT h₁ h₂)
    (fun _ h₁ _ h₂ => by simpa using mul_mem_degLE hT h₁ h₂)
    (degLE_mono (by norm_num)) (fun _ h => unit_of_neg hT h)
    M0 (fun j => mk (ι (xs j))) z hz hm
  -- Hence every generator lies in `I₁`.
  have hgen : ∀ j, xs j ∈ I₁ := by
    intro j
    have h0 := hzero j
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨t, ht, hxt⟩ := hT.saturate h0
    exact hsat _ t ht hxt
  intro u hu
  obtain ⟨w, -, hw⟩ := hdec (D.deg u) u hu (D.mem_Fz_deg u)
  rw [hw]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := I₁.smul_mem (op (w i)) (hgen i)
  rwa [op_smul_eq_mul] at this

/-! ### Detection (Z7(b)) and nondivision (Z9) -/

/-- A homogeneous ideal not contained in `𝔭` contains a homogeneous element
outside `𝔭`. -/
lemma exists_homogeneous_not_mem {J : Ideal G} (hJ : J.IsHomogeneous 𝒜) (h : ¬ J ≤ p) :
    ∃ n g, g ∈ J ∧ g ∈ 𝒜 n ∧ g ∉ p := by
  classical
  obtain ⟨g, hgJ, hgp⟩ := Set.not_subset.mp h
  by_contra hc
  push_neg at hc
  apply hgp
  rw [← sum_support_decompose 𝒜 g]
  exact Ideal.sum_mem _ fun n _ => hc n _ (hJ n hgJ) (decompose 𝒜 g n).2

variable (D) in
/-- `1 ∈ I T_𝔭` iff `𝔭 ∉ Z(U/I) = V(gr I)` (support detection, Z7(b)). -/
theorem one_mem_extend_iff_not_le (hT : IsRightFractions (D.denoms p) ι)
    (I : Submodule Uᵐᵒᵖ U) :
    (1 : T) ∈ IsRightFractions.extend (ι := ι) I ↔ ¬ D.grIdeal I ≤ p := by
  rw [hT.one_mem_extend_iff]
  constructor
  · rintro ⟨s, hs, hsI⟩ hle
    exact hs.2 (hle (D.sym_mem_grIdeal hsI))
  · intro h
    obtain ⟨n, g, hgJ, hgn, hgp⟩ := exists_homogeneous_not_mem (D.grIdeal_isHomogeneous I) h
    obtain ⟨u, huI, huF, hug⟩ := D.exists_of_mem_grIdeal hgJ hgn
    have hne : D.grAt n u ≠ 0 := by rw [hug]; rintro rfl; exact hgp p.zero_mem
    refine ⟨u, ⟨fun h0 => ?_, ?_⟩, huI⟩
    · rw [h0, grAt_zero] at hne; exact hne rfl
    · rw [← D.grAt_eq_sym huF hne, hug]; exact hgp

/-- **Nondivision (Z9).**  If `d ∈ I` is nonzero and `gr I ⊆ 𝔭`, then `ι d` is
not a unit of `T_𝔭`. -/
theorem not_isUnit_of_le (hT : IsRightFractions (D.denoms p) ι) {I : Submodule Uᵐᵒᵖ U}
    (hle : D.grIdeal I ≤ p) {d : U} (hdI : d ∈ I) : ¬ IsUnit (ι d) := by
  rintro ⟨u, hu⟩
  obtain ⟨a, s, hs, has⟩ := hT.surj (↑u⁻¹)
  have : ι s = ι (d * a) := by rw [map_mul, ← has, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have hsd := hT.injective this
  apply hs.2
  rw [hsd, D.sym_mul]
  exact p.mul_mem_right _ (hle (D.sym_mem_grIdeal hdI))

/-! ### Z8: finite length at minimal primes -/

/-- Pull back a submodule of `T ⧸ I T` to a right ideal of `U`. -/
def pull (ι : U →+* T) (I : Submodule Uᵐᵒᵖ U)
    (W : Submodule Tᵐᵒᵖ (T ⧸ IsRightFractions.extend (ι := ι) I)) : Submodule Uᵐᵒᵖ U where
  carrier := {a | Submodule.Quotient.mk (ι a) ∈ W}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add, Submodule.Quotient.mk_add] at ha hb ⊢
    exact W.add_mem ha hb
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := W.smul_mem (op (ι (unop c))) ha
    rwa [← Submodule.Quotient.mk_smul, op_smul_eq_mul, ← map_mul, ← smul_eq_mul_unop] at this

theorem finiteLength (hT : IsRightFractions (D.denoms p) ι) (I : Submodule Uᵐᵒᵖ U)
    (hp : p ∈ (D.grIdeal I).minimalPrimes) :
    IsArtinian Tᵐᵒᵖ (T ⧸ IsRightFractions.extend (ι := ι) I) ∧
      IsNoetherian Tᵐᵒᵖ (T ⧸ IsRightFractions.extend (ι := ι) I) := by
  classical
  set E := IsRightFractions.extend (ι := ι) I
  set J := D.grIdeal I
  -- The Artinian ring `A = (G ⧸ J)_P`.
  obtain ⟨P, hP, hPp⟩ : ∃ P ∈ minimalPrimes (G ⧸ J), P.comap (Ideal.Quotient.mk J) = p := by
    rw [Ideal.minimalPrimes_eq_comap] at hp
    obtain ⟨P, hP, rfl⟩ := hp
    exact ⟨P, hP, rfl⟩
  haveI : P.IsPrime := hP.1.1
  let A := Localization.AtPrime P
  haveI : Ring.KrullDimLE 0 A := Ring.KrullDimLE.of_isLocalization P hP A
  haveI : IsArtinianRing A :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr
      ⟨(inferInstance : IsNoetherianRing (Localization P.primeCompl)), inferInstance⟩
  let f : G →+* A := (algebraMap (G ⧸ J) A).comp (Ideal.Quotient.mk J)
  let Φ : Submodule Tᵐᵒᵖ (T ⧸ E) → Ideal A := fun W => Ideal.map f (D.grIdeal (pull ι I W))
  -- Basic properties of `pull`.
  have pull_mono : Monotone (pull ι I) := fun W W' h a ha => h ha
  have pull_sat : ∀ W a, ∀ s ∈ D.denoms p, a * s ∈ pull ι I W → a ∈ pull ι I W := by
    intro W a s hs has
    obtain ⟨u, hu⟩ := hT.isUnit s hs
    change Submodule.Quotient.mk (ι a) ∈ W
    have := W.smul_mem (op (↑u⁻¹ : T)) has
    rwa [← Submodule.Quotient.mk_smul, op_smul_eq_mul, map_mul, ← hu, mul_assoc,
      Units.mul_inv, mul_one] at this
  have pull_strict : StrictMono (pull ι I) := by
    refine pull_mono.strictMono_of_injective fun W W' h => ?_
    ext v
    obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective E v
    obtain ⟨a, s, hs, hτ⟩ := hT.surj τ
    obtain ⟨u, hu⟩ := hT.isUnit s hs
    have key : ∀ W : Submodule Tᵐᵒᵖ (T ⧸ E),
        Submodule.Quotient.mk τ ∈ W ↔ a ∈ pull ι I W := by
      intro W
      change _ ↔ Submodule.Quotient.mk (ι a) ∈ W
      constructor
      · intro hτW
        have := W.smul_mem (op (ι s)) hτW
        rwa [← Submodule.Quotient.mk_smul, op_smul_eq_mul, hτ] at this
      · intro haW
        have := W.smul_mem (op (↑u⁻¹ : T)) haW
        rwa [← Submodule.Quotient.mk_smul, op_smul_eq_mul, ← hτ, ← hu, mul_assoc,
          Units.mul_inv, mul_one] at this
    rw [key W, key W', h]
  have I_le_pull : ∀ W, I ≤ pull ι I W := by
    intro W a ha
    change Submodule.Quotient.mk (ι a) ∈ W
    rw [(Submodule.Quotient.mk_eq_zero E).mpr (IsRightFractions.map_mem_extend ha)]
    exact W.zero_mem
  -- `Φ` is strictly monotone.
  have Φ_strict : StrictMono Φ := by
    intro W W' hWW'
    have hlt := pull_strict hWW'
    refine lt_of_le_of_ne (Ideal.map_mono (D.grIdeal_mono hlt.le)) fun heq => ?_
    apply hlt.ne'
    apply le_antisymm _ hlt.le
    -- Find `c ∉ 𝔭` with `c · gr(pull W') ⊆ gr(pull W)`.
    set L := D.grIdeal (pull ι I W)
    set L' := D.grIdeal (pull ι I W')
    have hJL : J ≤ L := D.grIdeal_mono (I_le_pull W)
    have hloc : ∀ g ∈ L', ∃ c, c ∉ p ∧ c * g ∈ L := by
      intro g hg
      have hmem : f g ∈ Ideal.map f L :=
        (show Ideal.map f L' = Ideal.map f L from heq.symm) ▸ Ideal.mem_map_of_mem f hg
      rw [show f = (algebraMap (G ⧸ J) A).comp (Ideal.Quotient.mk J) from rfl,
        ← Ideal.map_map] at hmem
      obtain ⟨⟨⟨a, ha⟩, ⟨m, hm⟩⟩, hx⟩ :=
        (IsLocalization.mem_map_algebraMap_iff P.primeCompl A).mp hmem
      simp only [RingHom.comp_apply, ← map_mul] at hx
      obtain ⟨⟨c, hc⟩, hceq⟩ := (IsLocalization.eq_iff_exists P.primeCompl A).mp hx
      obtain ⟨a₁, ha₁, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp ha
      obtain ⟨m₁, rfl⟩ := Ideal.Quotient.mk_surjective m
      obtain ⟨c₁, rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨c₁ * m₁, ?_, ?_⟩
      · intro hcm
        have : Ideal.Quotient.mk J (c₁ * m₁) ∈ P := by
          rw [← hPp] at hcm; exact hcm
        rw [map_mul] at this
        rcases hP.1.1.mem_or_mem this with h | h
        · exact hc h
        · exact hm h
      · have h0 : Ideal.Quotient.mk J (c₁ * m₁ * g - c₁ * a₁) = 0 := by
          rw [map_sub, map_mul, map_mul, map_mul]
          rw [mul_comm (Ideal.Quotient.mk J g)] at hceq
          rw [sub_eq_zero, mul_assoc, hceq]
        rw [Ideal.Quotient.eq_zero_iff_mem] at h0
        have := L.add_mem (hJL h0) (L.mul_mem_left c₁ ha₁)
        simpa using this
    -- A single denominator for a finite generating set.
    obtain ⟨s₀, hs₀⟩ := (IsNoetherian.noetherian L' : L'.FG)
    have hc₀ : ∀ g : s₀, ∃ c, c ∉ p ∧ c * g ∈ L := fun g =>
      hloc g (hs₀ ▸ Submodule.subset_span g.2)
    choose cg hcgp hcgL using hc₀
    set c : G := ∏ g : s₀, cg g
    have hcp : c ∉ p := by
      rw [Ideal.IsPrime.prod_mem_iff]
      push_neg
      exact fun g _ => hcgp g
    have hcL : L' ≤ Submodule.comap (LinearMap.mulLeft G c) L := by
      rw [← hs₀, Submodule.span_le]
      intro g hg
      change c * g ∈ L
      rw [show c = (∏ g' ∈ Finset.univ.erase ⟨g, hg⟩, cg g') * cg ⟨g, hg⟩ from
        (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm, mul_assoc]
      exact L.mul_mem_left _ (hcgL _)
    -- Pass to a homogeneous component of `c`.
    obtain ⟨i, hi⟩ : ∃ i, (decompose 𝒜 c i : G) ∉ p := by
      by_contra hc'
      push_neg at hc'
      apply hcp
      rw [← sum_support_decompose 𝒜 c]
      exact Ideal.sum_mem _ fun i _ => hc' i
    set ci : G := ((decompose 𝒜 c i : 𝒜 i) : G)
    have hLhom := D.grIdeal_isHomogeneous (pull ι I W)
    have hL'hom := D.grIdeal_isHomogeneous (pull ι I W')
    have hkill_hom : ∀ e g, g ∈ L' → g ∈ 𝒜 e → ci * g ∈ L := by
      intro e g hg hge
      have hcg : c * g ∈ L := hcL hg
      have := hLhom (i + e) hcg
      rwa [coe_decompose_mul_of_right_mem_of_le 𝒜 hge (by omega), Nat.add_sub_cancel] at this
    have hkill : ∀ g ∈ L', ci * g ∈ L := by
      intro g hg
      rw [← sum_support_decompose 𝒜 g, Finset.mul_sum]
      exact Ideal.sum_mem _ fun e _ => hkill_hom e _ (hL'hom e hg) (decompose 𝒜 g e).2
    obtain ⟨s, hsF, hsg⟩ := D.exists_grAt_eq (decompose 𝒜 c i).2
    have hne : D.grAt i s ≠ 0 := by rw [hsg]; intro h; apply hi; change ((decompose 𝒜 c i : 𝒜 i) : G) ∈ p; rw [h]; exact p.zero_mem
    have hsym : D.sym s = ci := by rw [← D.grAt_eq_sym hsF hne, hsg]
    have hsS : s ∈ D.denoms p := ⟨fun h0 => by rw [h0, grAt_zero] at hne; exact hne rfl,
      by rw [hsym]; exact hi⟩
    exact survival hT hlt.le (pull_sat W) hsS (fun g hg => by rw [hsym]; exact hkill g hg)
  haveI : WellFoundedLT (Ideal A) := inferInstance
  haveI : WellFoundedGT (Ideal A) := inferInstance
  exact ⟨Φ_strict.wellFoundedLT, isNoetherian_iff'.mpr Φ_strict.wellFoundedGT⟩

end Domain

end FilteredAlgebraData

end SymplecticStafford.Paper
