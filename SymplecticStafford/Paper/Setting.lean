import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Algebra.Opposite

/-!
# The standing filtered setting (paper §1.1 and §2)

`FilteredAlgebraData k U G 𝒜` records the standing hypotheses of the
manuscript: an exhaustive, nonnegative, multiplicative filtration `F` of the
`k`-algebra `U` with `F₀U = k` and finite-dimensional pieces, together with an
identification of its associated graded ring with the commutative `ℕ`-graded
`k`-algebra `G = ⨁ 𝒜 n`.  The identification is given by `k`-linear maps
`gr n : F n → 𝒜 n` that are surjective, have kernel `F (n-1)` (and kernel `0`
for `n = 0`), and are multiplicative.  These are exactly the statements
`F n / F (n-1) ≃ 𝒜 n` and `gr U ≃ G` as graded rings.

From these data this file constructs the degree `deg u`, the principal symbol
`sym u`, the symbol-denominator submonoid attached to a prime of `G`, and
the graded ideal `grIdeal I = gr I` of a right ideal `I`.  It then proves the
positive filtered facts of §2 used later: additivity of degrees, the domain
property, and the Artin–Rees/goodness statement for right ideals (the lifting
argument of Lemma 2.1).

Right ideals of `U` are `Submodule Uᵐᵒᵖ U`.
-/

namespace SymplecticStafford.Paper

open DirectSum MulOpposite

/-- The standing filtered-algebra hypotheses of the manuscript, with the
associated graded ring identified with `G = ⨁ 𝒜 n`. -/
structure FilteredAlgebraData (k U G : Type*) [Field k] [Ring U] [Algebra k U]
    [CommRing G] [Algebra k G] (𝒜 : ℕ → Submodule k G) [GradedAlgebra 𝒜] where
  /-- The filtration pieces `F n = Fₙ U`. -/
  F : ℕ → Submodule k U
  mono : Monotone F
  exhaustive : ∀ u : U, ∃ n, u ∈ F n
  /-- `F₀U = k`. -/
  zero_piece : F 0 = LinearMap.range (Algebra.linearMap k U)
  finiteDimensional : ∀ n, FiniteDimensional k (F n)
  mul_mem : ∀ {i j : ℕ} {u v : U}, u ∈ F i → v ∈ F j → u * v ∈ F (i + j)
  /-- The symbol maps `Fₙ U → Fₙ U / Fₙ₋₁ U ≃ 𝒜 n`. -/
  gr : ∀ n, F n →ₗ[k] 𝒜 n
  gr_surjective : ∀ n, Function.Surjective (gr n)
  gr_zero_eq_zero_iff : ∀ x : F 0, gr 0 x = 0 ↔ x = 0
  gr_succ_eq_zero_iff : ∀ n (x : F (n + 1)), gr (n + 1) x = 0 ↔ (x : U) ∈ F n
  gr_mul : ∀ {i j : ℕ} (x : F i) (y : F j),
    ((gr (i + j) ⟨x * y, mul_mem x.2 y.2⟩ : 𝒜 (i + j)) : G) = (gr i x : G) * (gr j y : G)

namespace FilteredAlgebraData

variable {k U G : Type*} [Field k] [Ring U] [Algebra k U] [CommRing G] [Algebra k G]
variable {𝒜 : ℕ → Submodule k G} [GradedAlgebra 𝒜]
variable (D : FilteredAlgebraData k U G 𝒜)

/-! ### Pieces and the degree-`n` symbol -/

/-- The strictly lower piece `Fₙ₋₁ U` (with `F₋₁ U = 0`). -/
def Flow : ℕ → Submodule k U
  | 0 => ⊥
  | n + 1 => D.F n

@[simp] lemma Flow_zero : D.Flow 0 = ⊥ := rfl
@[simp] lemma Flow_succ (n : ℕ) : D.Flow (n + 1) = D.F n := rfl

lemma Flow_le (n : ℕ) : D.Flow n ≤ D.F n := by
  cases n with
  | zero => exact bot_le
  | succ n => exact D.mono (Nat.le_succ n)

/-- The degree-`n` symbol of `u`, extended by zero outside `Fₙ U`. -/
noncomputable def grAt (n : ℕ) (u : U) : G := by
  classical exact if h : u ∈ D.F n then ((D.gr n ⟨u, h⟩ : 𝒜 n) : G) else 0

lemma grAt_of_mem {n : ℕ} {u : U} (h : u ∈ D.F n) :
    D.grAt n u = ((D.gr n ⟨u, h⟩ : 𝒜 n) : G) := by
  simp [grAt, h]

lemma grAt_mem (n : ℕ) (u : U) : D.grAt n u ∈ 𝒜 n := by
  unfold grAt
  split_ifs
  · exact (D.gr n _).2
  · exact Submodule.zero_mem _

@[simp] lemma grAt_zero (n : ℕ) : D.grAt n 0 = 0 := by
  rw [D.grAt_of_mem (Submodule.zero_mem _)]
  have : (⟨0, Submodule.zero_mem _⟩ : D.F n) = 0 := rfl
  rw [this, map_zero]; rfl

lemma grAt_add {n : ℕ} {u v : U} (hu : u ∈ D.F n) (hv : v ∈ D.F n) :
    D.grAt n (u + v) = D.grAt n u + D.grAt n v := by
  rw [D.grAt_of_mem hu, D.grAt_of_mem hv, D.grAt_of_mem (Submodule.add_mem _ hu hv)]
  have : (⟨u + v, Submodule.add_mem _ hu hv⟩ : D.F n) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
  rw [this, map_add]; rfl

lemma grAt_neg {n : ℕ} {u : U} (hu : u ∈ D.F n) : D.grAt n (-u) = -D.grAt n u := by
  rw [D.grAt_of_mem hu, D.grAt_of_mem (Submodule.neg_mem _ hu)]
  have : (⟨-u, Submodule.neg_mem _ hu⟩ : D.F n) = -⟨u, hu⟩ := rfl
  rw [this, map_neg]; rfl

lemma grAt_sub {n : ℕ} {u v : U} (hu : u ∈ D.F n) (hv : v ∈ D.F n) :
    D.grAt n (u - v) = D.grAt n u - D.grAt n v := by
  rw [sub_eq_add_neg, D.grAt_add hu (Submodule.neg_mem _ hv), D.grAt_neg hv, sub_eq_add_neg]

lemma grAt_smul {n : ℕ} (c : k) {u : U} (hu : u ∈ D.F n) :
    D.grAt n (c • u) = c • D.grAt n u := by
  rw [D.grAt_of_mem hu, D.grAt_of_mem (Submodule.smul_mem _ c hu)]
  have : (⟨c • u, Submodule.smul_mem _ c hu⟩ : D.F n) = c • ⟨u, hu⟩ := rfl
  rw [this, map_smul]; rfl

lemma grAt_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → U) (hf : ∀ i ∈ s, f i ∈ D.F n) :
    D.grAt n (∑ i ∈ s, f i) = ∑ i ∈ s, D.grAt n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      D.grAt_add (hf a (Finset.mem_insert_self a s))
        (Submodule.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

lemma grAt_eq_zero_iff {n : ℕ} {u : U} (hu : u ∈ D.F n) :
    D.grAt n u = 0 ↔ u ∈ D.Flow n := by
  rw [D.grAt_of_mem hu]
  cases n with
  | zero =>
    rw [Submodule.coe_eq_zero, D.gr_zero_eq_zero_iff, Flow_zero, Submodule.mem_bot]
    exact Subtype.ext_iff
  | succ n =>
    rw [Submodule.coe_eq_zero, D.gr_succ_eq_zero_iff, Flow_succ]

lemma grAt_eq_grAt_iff {n : ℕ} {u v : U} (hu : u ∈ D.F n) (hv : v ∈ D.F n) :
    D.grAt n u = D.grAt n v ↔ u - v ∈ D.Flow n := by
  rw [← D.grAt_eq_zero_iff (Submodule.sub_mem _ hu hv), D.grAt_sub hu hv, sub_eq_zero]

lemma grAt_mul {i j : ℕ} {u v : U} (hu : u ∈ D.F i) (hv : v ∈ D.F j) :
    D.grAt (i + j) (u * v) = D.grAt i u * D.grAt j v := by
  rw [D.grAt_of_mem hu, D.grAt_of_mem hv, D.grAt_of_mem (D.mul_mem hu hv)]
  exact D.gr_mul ⟨u, hu⟩ ⟨v, hv⟩

lemma grAt_mul' {i j n : ℕ} (h : i + j = n) {u v : U} (hu : u ∈ D.F i) (hv : v ∈ D.F j) :
    D.grAt n (u * v) = D.grAt i u * D.grAt j v := by
  subst h; exact D.grAt_mul hu hv

lemma exists_grAt_eq {n : ℕ} {g : G} (hg : g ∈ 𝒜 n) : ∃ u ∈ D.F n, D.grAt n u = g := by
  obtain ⟨x, hx⟩ := D.gr_surjective n ⟨g, hg⟩
  refine ⟨x, x.2, ?_⟩
  rw [D.grAt_of_mem x.2]
  simp [hx]

lemma mem_F_of_le {m n : ℕ} (h : m ≤ n) {u : U} (hu : u ∈ D.F m) : u ∈ D.F n :=
  D.mono h hu

/-! ### Degree and principal symbol -/

/-- The least filtration degree. -/
noncomputable def deg (u : U) : ℕ := by
  classical exact Nat.find (D.exhaustive u)

lemma mem_F_deg (u : U) : u ∈ D.F (D.deg u) := by
  classical
  unfold deg
  exact Nat.find_spec (D.exhaustive u)

lemma mem_F_iff {u : U} {n : ℕ} : u ∈ D.F n ↔ D.deg u ≤ n := by
  classical
  constructor
  · intro h
    unfold deg
    exact Nat.find_min' _ h
  · intro h
    exact D.mono h (D.mem_F_deg u)

/-- The principal symbol `σ(u)`. -/
noncomputable def sym (u : U) : G := D.grAt (D.deg u) u

lemma sym_mem (u : U) : D.sym u ∈ 𝒜 (D.deg u) := D.grAt_mem _ _

@[simp] lemma sym_zero : D.sym 0 = 0 := D.grAt_zero _

lemma not_mem_Flow_deg {u : U} (hu : u ≠ 0) : u ∉ D.Flow (D.deg u) := by
  intro h
  rcases hn : D.deg u with _ | n
  · rw [hn, Flow_zero, Submodule.mem_bot] at h
    exact hu h
  · rw [hn, Flow_succ] at h
    have := D.mem_F_iff.mp h
    omega

lemma sym_ne_zero {u : U} (hu : u ≠ 0) : D.sym u ≠ 0 := by
  intro h
  exact D.not_mem_Flow_deg hu ((D.grAt_eq_zero_iff (D.mem_F_deg u)).mp h)

lemma sym_eq_zero_iff {u : U} : D.sym u = 0 ↔ u = 0 :=
  ⟨fun h => by_contra fun hu => D.sym_ne_zero hu h, fun h => h ▸ D.sym_zero⟩

/-- If `u ∈ Fₙ` has nonzero degree-`n` symbol then `deg u = n`. -/
lemma deg_eq_of_grAt_ne_zero {n : ℕ} {u : U} (hu : u ∈ D.F n) (h : D.grAt n u ≠ 0) :
    D.deg u = n := by
  have hle := D.mem_F_iff.mp hu
  by_contra hne
  apply h
  rw [D.grAt_eq_zero_iff hu]
  cases n with
  | zero => omega
  | succ n => exact D.mem_F_iff.mpr (by omega)

lemma grAt_eq_sym {n : ℕ} {u : U} (hu : u ∈ D.F n) (h : D.grAt n u ≠ 0) :
    D.grAt n u = D.sym u := by
  unfold sym; rw [D.deg_eq_of_grAt_ne_zero hu h]

lemma grAt_deg_lt {n : ℕ} {u : U} (h : D.deg u < n) : D.grAt n u = 0 := by
  rw [D.grAt_eq_zero_iff (D.mem_F_iff.mpr h.le)]
  cases n with
  | zero => omega
  | succ n => exact D.mem_F_iff.mpr (by omega)

/-- The filtration extended by zero to integer indices. -/
noncomputable def Fz (m : ℤ) : Submodule k U := by
  classical exact if m < 0 then ⊥ else D.F m.toNat

lemma Fz_of_nonneg {m : ℤ} (h : 0 ≤ m) : D.Fz m = D.F m.toNat := by
  simp [Fz, not_lt.mpr h]

lemma Fz_of_neg {m : ℤ} (h : m < 0) : D.Fz m = ⊥ := by
  simp [Fz, h]

@[simp] lemma Fz_natCast (n : ℕ) : D.Fz n = D.F n := by
  rw [D.Fz_of_nonneg (Int.natCast_nonneg n), Int.toNat_natCast]

lemma Fz_mono : Monotone D.Fz := by
  intro a b hab
  by_cases ha : a < 0
  · rw [D.Fz_of_neg ha]; exact bot_le
  · rw [D.Fz_of_nonneg (by omega), D.Fz_of_nonneg (by omega)]
    exact D.mono (by omega)

lemma Fz_mul_mem {i j : ℤ} {u v : U} (hu : u ∈ D.Fz i) (hv : v ∈ D.Fz j) :
    u * v ∈ D.Fz (i + j) := by
  by_cases hi : i < 0
  · rw [D.Fz_of_neg hi, Submodule.mem_bot] at hu; simp [hu]
  by_cases hj : j < 0
  · rw [D.Fz_of_neg hj, Submodule.mem_bot] at hv; simp [hv]
  rw [D.Fz_of_nonneg (show 0 ≤ i by omega)] at hu
  rw [D.Fz_of_nonneg (show 0 ≤ j by omega)] at hv
  rw [D.Fz_of_nonneg (show 0 ≤ i + j by omega)]
  have := D.mul_mem hu hv
  rwa [show i.toNat + j.toNat = (i + j).toNat by omega] at this

lemma Flow_eq_Fz (n : ℕ) : D.Flow n = D.Fz ((n : ℤ) - 1) := by
  cases n with
  | zero => rw [Flow_zero, D.Fz_of_neg (by omega)]
  | succ n => rw [Flow_succ, D.Fz_of_nonneg (by omega)]; congr 1; omega

lemma mem_Fz_iff {m : ℤ} {u : U} : u ∈ D.Fz m ↔ u = 0 ∨ (D.deg u : ℤ) ≤ m := by
  by_cases hm : m < 0
  · rw [D.Fz_of_neg hm, Submodule.mem_bot]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · omega
  · rw [D.Fz_of_nonneg (by omega)]
    constructor
    · intro h; right; have := D.mem_F_iff.mp h; omega
    · rintro (h | h)
      · subst h; exact Submodule.zero_mem _
      · exact D.mem_F_iff.mpr (by omega)

lemma mem_Fz_deg (u : U) : u ∈ D.Fz (D.deg u) := by
  rw [Fz_natCast]; exact D.mem_F_deg u

/-! ### Degree zero -/

lemma mem_F_zero_iff {u : U} : u ∈ D.F 0 ↔ ∃ c : k, algebraMap k U c = u := by
  rw [D.zero_piece]; simp [Algebra.linearMap_apply]

lemma isUnit_of_mem_F_zero {u : U} (hu : u ∈ D.F 0) (h0 : u ≠ 0) : IsUnit u := by
  obtain ⟨c, rfl⟩ := D.mem_F_zero_iff.mp hu
  have hc : c ≠ 0 := by rintro rfl; simp at h0
  exact (isUnit_iff_ne_zero.mpr hc).map (algebraMap k U)

lemma one_mem_F (n : ℕ) : (1 : U) ∈ D.F n :=
  D.mono (Nat.zero_le n) (D.mem_F_zero_iff.mpr ⟨1, map_one _⟩)

lemma algebraMap_mem_F (n : ℕ) (c : k) : algebraMap k U c ∈ D.F n :=
  D.mono (Nat.zero_le n) (D.mem_F_zero_iff.mpr ⟨c, rfl⟩)

section Domain

variable [IsDomain G]

lemma grAt_zero_one : D.grAt 0 1 = 1 := by
  have h1 : D.grAt 0 1 ≠ 0 := by
    rw [Ne, D.grAt_eq_zero_iff (D.one_mem_F 0), Flow_zero, Submodule.mem_bot]
    intro h
    obtain ⟨x, hx⟩ := D.gr_surjective 0 ⟨1, SetLike.GradedOne.one_mem⟩
    have hx0 : (x : U) = 0 := by
      have : (x : U) = x * 1 := (mul_one _).symm
      rw [this, h, mul_zero]
    have : x = 0 := Subtype.ext hx0
    rw [this, map_zero] at hx
    exact one_ne_zero (congrArg Subtype.val hx).symm
  have hsq : D.grAt 0 1 * D.grAt 0 1 = D.grAt 0 1 * 1 := by
    rw [mul_one, ← D.grAt_mul (D.one_mem_F 0) (D.one_mem_F 0), mul_one]
  exact mul_left_cancel₀ h1 hsq

include D in
lemma nontrivial : Nontrivial U := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := D.grAt_zero_one
  rw [h, grAt_zero] at this
  exact zero_ne_one this

lemma deg_one : D.deg (1 : U) = 0 := by
  have := D.mem_F_iff.mp (D.one_mem_F 0); omega

lemma sym_one : D.sym (1 : U) = 1 := by
  unfold sym; rw [D.deg_one, D.grAt_zero_one]

lemma grAt_mul_deg {u v : U} :
    D.grAt (D.deg u + D.deg v) (u * v) = D.sym u * D.sym v :=
  D.grAt_mul (D.mem_F_deg u) (D.mem_F_deg v)

include D in
lemma mul_ne_zero' {u v : U} (hu : u ≠ 0) (hv : v ≠ 0) : u * v ≠ 0 := by
  intro h
  have := D.grAt_mul_deg (u := u) (v := v)
  rw [h, grAt_zero] at this
  exact mul_ne_zero (D.sym_ne_zero hu) (D.sym_ne_zero hv) this.symm

lemma deg_mul {u v : U} (hu : u ≠ 0) (hv : v ≠ 0) : D.deg (u * v) = D.deg u + D.deg v := by
  apply D.deg_eq_of_grAt_ne_zero (D.mul_mem (D.mem_F_deg u) (D.mem_F_deg v))
  rw [D.grAt_mul_deg]
  exact mul_ne_zero (D.sym_ne_zero hu) (D.sym_ne_zero hv)

lemma sym_mul (u v : U) : D.sym (u * v) = D.sym u * D.sym v := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  unfold sym
  rw [D.deg_mul hu hv]
  exact D.grAt_mul_deg

include D in
lemma noZeroDivisors : NoZeroDivisors U where
  eq_zero_or_eq_zero_of_mul_eq_zero {u v} h := by
    by_contra hc
    push_neg at hc
    exact D.mul_ne_zero' hc.1 hc.2 h

include D in
lemma isDomain : IsDomain U :=
  haveI := D.nontrivial
  haveI := D.noZeroDivisors
  NoZeroDivisors.to_isDomain U

lemma sym_pow (u : U) (N : ℕ) : D.sym (u ^ N) = D.sym u ^ N := by
  induction N with
  | zero => simp [D.sym_one]
  | succ N ih => rw [pow_succ, D.sym_mul, ih, pow_succ]

lemma deg_pow {u : U} (hu : u ≠ 0) (N : ℕ) : D.deg (u ^ N) = N * D.deg u := by
  haveI := D.noZeroDivisors
  induction N with
  | zero => simp [D.deg_one]
  | succ N ih => rw [pow_succ, D.deg_mul (pow_ne_zero _ hu) hu, ih]; ring

/-! ### The symbol-denominator submonoid `S_𝔭` (paper (3.2)) -/

/-- `S_𝔭 = {s ≠ 0 : σ(s) ∉ 𝔭}`. -/
def denoms (p : Ideal G) [p.IsPrime] : Submonoid U where
  carrier := {s | s ≠ 0 ∧ D.sym s ∉ p}
  one_mem' := ⟨haveI := D.nontrivial; one_ne_zero, by
    rw [D.sym_one]; exact Ideal.IsPrime.one_notMem ‹_›⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨D.mul_ne_zero' ha hb, ?_⟩
    rw [D.sym_mul]
    exact fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ha' hb'

lemma mem_denoms {p : Ideal G} [p.IsPrime] {s : U} :
    s ∈ D.denoms p ↔ s ≠ 0 ∧ D.sym s ∉ p := Iff.rfl

end Domain

/-! ### The graded ideal of a right ideal -/

/-- The degree-`n` symbols of elements of the right ideal `I`. -/
def grPiece (I : Submodule Uᵐᵒᵖ U) (n : ℕ) : AddSubgroup G where
  carrier := {g | ∃ u, u ∈ I ∧ u ∈ D.F n ∧ D.grAt n u = g}
  add_mem' := by
    rintro _ _ ⟨u, hu, hu', rfl⟩ ⟨v, hv, hv', rfl⟩
    exact ⟨u + v, I.add_mem hu hv, Submodule.add_mem _ hu' hv', D.grAt_add hu' hv'⟩
  zero_mem' := ⟨0, I.zero_mem, Submodule.zero_mem _, D.grAt_zero n⟩
  neg_mem' := by
    rintro _ ⟨u, hu, hu', rfl⟩
    exact ⟨-u, I.neg_mem hu, Submodule.neg_mem _ hu', D.grAt_neg hu'⟩

lemma mem_grPiece {I : Submodule Uᵐᵒᵖ U} {n : ℕ} {g : G} :
    g ∈ D.grPiece I n ↔ ∃ u, u ∈ I ∧ u ∈ D.F n ∧ D.grAt n u = g := Iff.rfl

lemma grAt_mem_grPiece {I : Submodule Uᵐᵒᵖ U} {n : ℕ} {u : U} (hu : u ∈ I) (hn : u ∈ D.F n) :
    D.grAt n u ∈ D.grPiece I n := ⟨u, hu, hn, rfl⟩

/-- Homogeneous multiples of pieces stay in pieces (right-ideal property plus
commutativity of `G`). -/
lemma mul_mem_grPiece {I : Submodule Uᵐᵒᵖ U} {i m : ℕ} {r g : G} (hr : r ∈ 𝒜 i)
    (hg : g ∈ D.grPiece I m) : r * g ∈ D.grPiece I (m + i) := by
  obtain ⟨u, hu, hu', rfl⟩ := hg
  obtain ⟨v, hv, rfl⟩ := D.exists_grAt_eq hr
  refine ⟨u * v, ?_, D.mul_mem hu' hv, ?_⟩
  · have := I.smul_mem (op v) hu
    rwa [op_smul_eq_mul] at this
  · rw [D.grAt_mul hu' hv, mul_comm]

open Classical in
/-- `gr I`, the homogeneous ideal of symbols of the right ideal `I`. -/
noncomputable def grIdeal (I : Submodule Uᵐᵒᵖ U) : Ideal G where
  carrier := {g | ∀ n, (decompose 𝒜 g n : G) ∈ D.grPiece I n}
  add_mem' := by
    intro a b ha hb n
    rw [decompose_add, add_apply, Submodule.coe_add]
    exact AddSubgroup.add_mem _ (ha n) (hb n)
  zero_mem' := by
    intro n
    rw [decompose_zero, zero_apply, Submodule.coe_zero]
    exact AddSubgroup.zero_mem _
  smul_mem' := by
    intro r g hg n
    rw [smul_eq_mul, show r * g = ∑ i ∈ (decompose 𝒜 r).support, (decompose 𝒜 r i : G) * g by
      rw [← Finset.sum_mul, sum_support_decompose]]
    rw [decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [coe_decompose_mul_of_left_mem 𝒜 n (decompose 𝒜 r i).2]
    split_ifs with hin
    · have := D.mul_mem_grPiece (decompose 𝒜 r i).2 (hg (n - i))
      rwa [Nat.sub_add_cancel hin] at this
    · exact AddSubgroup.zero_mem _

lemma mem_grIdeal {I : Submodule Uᵐᵒᵖ U} {g : G} :
    g ∈ D.grIdeal I ↔ ∀ n, (decompose 𝒜 g n : G) ∈ D.grPiece I n := Iff.rfl

lemma mem_grIdeal_of_mem {I : Submodule Uᵐᵒᵖ U} {n : ℕ} {g : G} (hg : g ∈ 𝒜 n)
    (hp : g ∈ D.grPiece I n) : g ∈ D.grIdeal I := by
  classical
  intro m
  by_cases hmn : m = n
  · subst hmn; rw [decompose_of_mem_same 𝒜 hg]; exact hp
  · rw [decompose_of_mem_ne 𝒜 hg (Ne.symm hmn)]; exact AddSubgroup.zero_mem _

lemma grAt_mem_grIdeal {I : Submodule Uᵐᵒᵖ U} {n : ℕ} {u : U} (hu : u ∈ I)
    (hn : u ∈ D.F n) : D.grAt n u ∈ D.grIdeal I :=
  D.mem_grIdeal_of_mem (D.grAt_mem n u) (D.grAt_mem_grPiece hu hn)

lemma sym_mem_grIdeal {I : Submodule Uᵐᵒᵖ U} {u : U} (hu : u ∈ I) : D.sym u ∈ D.grIdeal I :=
  D.grAt_mem_grIdeal hu (D.mem_F_deg u)

/-- A homogeneous element of `gr I` of degree `n` is the degree-`n` symbol of an
element of `I ∩ Fₙ`. -/
lemma exists_of_mem_grIdeal {I : Submodule Uᵐᵒᵖ U} {n : ℕ} {g : G} (hg : g ∈ D.grIdeal I)
    (hgn : g ∈ 𝒜 n) : ∃ u, u ∈ I ∧ u ∈ D.F n ∧ D.grAt n u = g := by
  have := hg n
  rwa [decompose_of_mem_same 𝒜 hgn] at this

lemma grIdeal_isHomogeneous (I : Submodule Uᵐᵒᵖ U) : (D.grIdeal I).IsHomogeneous 𝒜 := by
  intro i g hg
  exact D.mem_grIdeal_of_mem (decompose 𝒜 g i).2 (hg i)

lemma grIdeal_mono {I J : Submodule Uᵐᵒᵖ U} (h : I ≤ J) : D.grIdeal I ≤ D.grIdeal J := by
  intro g hg n
  obtain ⟨u, hu, hu', hg'⟩ := hg n
  exact ⟨u, h hu, hu', hg'⟩

/-- The homogeneous symbols of `I` span `gr I`. -/
lemma grIdeal_le_span (I : Submodule Uᵐᵒᵖ U) :
    D.grIdeal I ≤ Ideal.span {g | ∃ n u, u ∈ I ∧ u ∈ D.F n ∧ D.grAt n u = g} := by
  classical
  intro g hg
  rw [← sum_support_decompose 𝒜 g]
  refine Ideal.sum_mem _ fun n _ => Ideal.subset_span ?_
  obtain ⟨u, hu, hu', he⟩ := hg n
  exact ⟨n, u, hu, hu', he⟩

lemma span_le_grIdeal (I : Submodule Uᵐᵒᵖ U) :
    Ideal.span {g | ∃ n u, u ∈ I ∧ u ∈ D.F n ∧ D.grAt n u = g} ≤ D.grIdeal I := by
  rw [Ideal.span_le]
  rintro _ ⟨n, u, hu, hu', rfl⟩
  exact D.grAt_mem_grIdeal hu hu'

/-! ### Artin–Rees for right ideals (the lifting argument of Lemma 2.1) -/

/-- Descent: if finitely many elements `x i ∈ I ∩ F (kk i)` have symbols
generating every symbol of `I`, then they give a good filtration of `I`. -/
theorem descent {I : Submodule Uᵐᵒᵖ U} {ι : Type*} [Fintype ι] (x : ι → U) (kk : ι → ℕ)
    (hx : ∀ i, x i ∈ I ∧ x i ∈ D.F (kk i))
    (hgen : ∀ n u, u ∈ I → u ∈ D.F n →
      D.grAt n u ∈ Ideal.span (Set.range fun i => D.grAt (kk i) (x i))) :
    ∀ n u, u ∈ I → u ∈ D.F n → ∃ v : ι → U,
      (∀ i, v i ∈ D.F (n - kk i) ∧ (n < kk i → v i = 0)) ∧ u = ∑ i, x i * v i := by
  classical
  -- One reduction step: remove the degree-`n` symbol.
  have step : ∀ n u, u ∈ I → u ∈ D.F n → ∃ v : ι → U,
      (∀ i, v i ∈ D.F (n - kk i) ∧ (n < kk i → v i = 0)) ∧
        u - ∑ i, x i * v i ∈ D.Flow n ∧ u - ∑ i, x i * v i ∈ I := by
    intro n u hu hun
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun G).mp (hgen n u hu hun)
    have hy : ∀ i, D.grAt (kk i) (x i) ∈ 𝒜 (kk i) := fun i => D.grAt_mem _ _
    have hw : ∀ i, ∃ w ∈ D.F (n - kk i),
        D.grAt (n - kk i) w = (decompose 𝒜 (c i) (n - kk i) : G) :=
      fun i => D.exists_grAt_eq (decompose 𝒜 (c i) (n - kk i)).2
    choose w hwF hwg using hw
    let v : ι → U := fun i => if kk i ≤ n then w i else 0
    have hvF : ∀ i, v i ∈ D.F (n - kk i) := by
      intro i; simp only [v]; split_ifs
      · exact hwF i
      · exact Submodule.zero_mem _
    have hterm : ∀ i, x i * v i ∈ D.F n := by
      intro i
      simp only [v]
      split_ifs with h
      · have := D.mul_mem (hx i).2 (hwF i)
        rwa [Nat.add_sub_cancel' h] at this
      · rw [mul_zero]; exact Submodule.zero_mem _
    refine ⟨v, fun i => ⟨hvF i, fun h => by simp [v, Nat.not_le.mpr h]⟩, ?_, ?_⟩
    · rw [← D.grAt_eq_grAt_iff hun (Submodule.sum_mem _ fun i _ => hterm i),
        D.grAt_sum _ _ fun i _ => hterm i]
      have hg : D.grAt n u = (decompose 𝒜 (D.grAt n u) n : G) :=
        (decompose_of_mem_same 𝒜 (D.grAt_mem n u)).symm
      rw [hg, ← hc, decompose_sum, DFinsupp.finset_sum_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, coe_decompose_mul_of_right_mem 𝒜 n (hy i)]
      simp only [v]
      split_ifs with h
      · rw [D.grAt_mul' (Nat.add_sub_cancel' h) (hx i).2 (hwF i), hwg i, mul_comm]
      · rw [mul_zero, grAt_zero]
    · refine I.sub_mem hu (Submodule.sum_mem _ fun i _ => ?_)
      have := I.smul_mem (op (v i)) (hx i).1
      rwa [op_smul_eq_mul] at this
  intro n
  induction n with
  | zero =>
    intro u hu hun
    obtain ⟨v, hv, hlow, -⟩ := step 0 u hu hun
    refine ⟨v, hv, ?_⟩
    rw [Flow_zero, Submodule.mem_bot, sub_eq_zero] at hlow
    exact hlow
  | succ m ih =>
    intro u hu hun
    obtain ⟨v, hv, hlow, hI⟩ := step (m + 1) u hu hun
    rw [Flow_succ] at hlow
    obtain ⟨v', hv', hsum⟩ := ih _ hI hlow
    refine ⟨v + v', fun i => ⟨?_, fun h => ?_⟩, ?_⟩
    · exact Submodule.add_mem _ (hv i).1 (D.mono (by omega) (hv' i).1)
    · simp [(hv i).2 h, (hv' i).2 (by omega)]
    · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [← hsum]; abel

/-- **Artin–Rees in `U`.**  Every right ideal has a finite family of elements
whose induced filtration is good: `I ∩ Fₙ = Σ xᵢ Fₙ₋ₖᵢ`.  This is the lifting
argument of Lemma 2.1, using Noetherianity of `G`. -/
theorem artinRees [IsNoetherianRing G] (I : Submodule Uᵐᵒᵖ U) :
    ∃ (m : ℕ) (x : Fin m → U) (kk : Fin m → ℕ), (∀ i, x i ∈ I ∧ x i ∈ D.F (kk i)) ∧
      ∀ n u, u ∈ I → u ∈ D.F n → ∃ v : Fin m → U,
        (∀ i, v i ∈ D.F (n - kk i) ∧ (n < kk i → v i = 0)) ∧ u = ∑ i, x i * v i := by
  classical
  set Sg : Set G := {g | ∃ n u, u ∈ I ∧ u ∈ D.F n ∧ D.grAt n u = g}
  have hfg : (Ideal.span Sg).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsS, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset Sg).mp hfg
  have hw : ∀ y : s, ∃ p : ℕ × U, p.2 ∈ I ∧ p.2 ∈ D.F p.1 ∧ D.grAt p.1 p.2 = y := by
    intro y
    obtain ⟨n, u, hu, hu', he⟩ := hsS y.2
    exact ⟨(n, u), hu, hu', he⟩
  choose p hpI hpF hpg using hw
  let e := s.equivFin
  refine ⟨s.card, fun i => (p (e.symm i)).2, fun i => (p (e.symm i)).1,
    fun i => ⟨hpI _, hpF _⟩, ?_⟩
  apply D.descent
  · exact fun i => ⟨hpI _, hpF _⟩
  intro n u hu hun
  have hmem : D.grAt n u ∈ Submodule.span G Sg := Submodule.subset_span ⟨n, u, hu, hun, rfl⟩
  rw [hspan] at hmem
  refine (Ideal.span_mono ?_) hmem
  intro y hy
  refine ⟨e ⟨y, hy⟩, ?_⟩
  simp [hpg]

end FilteredAlgebraData

end SymplecticStafford.Paper
