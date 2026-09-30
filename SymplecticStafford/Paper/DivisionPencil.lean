import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Central pencils over a division ring (paper Lemma 4.5)

Let `E` be a division ring and `κ : k →+* E` a field embedding with central
image.  If `v₁, …, vₙ` are `E`-linearly independent in a left `E`-module and
`w₁, …, wₙ` are arbitrary, then `vᵢ + κ(c) wᵢ` stay independent for all but
finitely many `c ∈ k`.

No determinants are used (they do not exist over a noncommutative `E`).  A
bad `c ≠ 0` produces an eigenvector of the `E`-linear map `π ∘ W` for the
central eigenvalue `-κ(c)⁻¹`, where `π` is a left inverse of the injective map
`P`.  Eigenvectors for distinct central eigenvalues are independent (this is
where centrality is used), so only finitely many bad values exist.

We prove the statement in the form of a pair of linear maps `P, W : D → Z`
with `D` finite-dimensional and `P` injective (`pencil_ker_finite`), and in the
form of families (`division_pencil_finite`).
-/

namespace SymplecticStafford.Paper

variable {k : Type*} [Field k] {E : Type*} [DivisionRing E]

section Eigen

variable {D : Type*} [AddCommGroup D] [Module E D]

/-- Eigenvectors of an `E`-linear endomorphism for pairwise distinct central
eigenvalues are `E`-linearly independent. -/
theorem central_eigenvectors_linearIndependent {ι : Type*} (A : D →ₗ[E] D) (μ : ι → E)
    (hμ : Function.Injective μ) (hc : ∀ i (a : E), μ i * a = a * μ i)
    (x : ι → D) (hx0 : ∀ i, x i ≠ 0) (hA : ∀ i, A (x i) = μ i • x i) :
    LinearIndependent E x := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    intro g hg
    have key : ∀ i, A (g i • x i) - μ j • (g i • x i) = (g i * (μ i - μ j)) • x i := by
      intro i
      rw [map_smul, hA, smul_smul, smul_smul, hc j, mul_sub, sub_smul]
    have h1 : ∑ i ∈ s, (g i * (μ i - μ j)) • x i = 0 := by
      have h2 : A (∑ i ∈ insert j s, g i • x i) - μ j • (∑ i ∈ insert j s, g i • x i) = 0 := by
        rw [hg, map_zero, smul_zero, sub_zero]
      rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib] at h2
      simp only [key] at h2
      rw [Finset.sum_insert hj, sub_self, mul_zero, zero_smul, zero_add] at h2
      exact h2
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have h3 := ih (fun i => g i * (μ i - μ j)) h1 i hi
      have hne : μ i - μ j ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        exact hj (hμ h ▸ hi)
      exact (mul_eq_zero.mp h3).resolve_right hne
    have hgs : ∑ i ∈ s, g i • x i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_smul]
    rw [Finset.sum_insert hj, hgs, add_zero] at hg
    have hgj : g j = 0 := (smul_eq_zero.mp hg).resolve_right (hx0 j)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hgj
    · exact hs i hi

end Eigen

variable (κ : k →+* E) (hκ : ∀ (c : k) (a : E), κ c * a = a * κ c)
include hκ

/-- **Lemma 4.5, linear-map form.**  If `P : D → Z` is injective and `D` is
finite-dimensional, then `P + κ(c) W` has a nonzero kernel for only finitely
many `c`. -/
theorem pencil_ker_finite {D Z : Type*} [AddCommGroup D] [Module E D] [Module.Finite E D]
    [AddCommGroup Z] [Module E Z] (P W : D →ₗ[E] Z) (hP : Function.Injective P) :
    {c : k | ∃ d : D, d ≠ 0 ∧ P d + κ c • W d = 0}.Finite := by
  classical
  obtain ⟨π, hπ⟩ := P.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hP)
  have hπP : ∀ d, π (P d) = d := fun d => LinearMap.congr_fun hπ d
  set A : D →ₗ[E] D := π.comp W
  set Bad : Set k := {c : k | c ≠ 0 ∧ ∃ d : D, d ≠ 0 ∧ P d + κ c • W d = 0}
  have hsub : {c : k | ∃ d : D, d ≠ 0 ∧ P d + κ c • W d = 0} ⊆ Bad := by
    rintro c ⟨d, hd, hPd⟩
    refine ⟨?_, d, hd, hPd⟩
    rintro rfl
    apply hd
    apply hP
    rw [map_zero]
    simpa using hPd
  refine Set.Finite.subset ?_ hsub
  let x : Bad → D := fun c => c.2.2.choose
  have hx0 : ∀ c, x c ≠ 0 := fun c => c.2.2.choose_spec.1
  have hxP : ∀ c : Bad, P (x c) + κ c • W (x c) = 0 := fun c => c.2.2.choose_spec.2
  let μ : Bad → E := fun c => κ (-(c : k)⁻¹)
  have hμ : Function.Injective μ := by
    intro c c' h
    apply Subtype.ext
    have := κ.injective h
    simpa using this
  have hA : ∀ c : Bad, A (x c) = μ c • x c := by
    intro c
    have h1 : x c + κ c • A (x c) = 0 := by
      have := congrArg π (hxP c)
      rwa [map_add, map_smul, hπP, map_zero] at this
    have hc0 : (c : k) ≠ 0 := c.2.1
    have h2 : A (x c) = κ ((c : k)⁻¹) • (κ c • A (x c)) := by
      rw [smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
    rw [h2, eq_neg_of_add_eq_zero_right h1, smul_neg, ← neg_smul, ← map_neg]
  have hli : LinearIndependent E x :=
    central_eigenvectors_linearIndependent A μ hμ (fun c a => hκ _ a) x hx0 hA
  have : Finite Bad := hli.finite_of_isNoetherian
  exact Set.toFinite Bad

/-- **Lemma 4.5 (central pencils over a division ring).**  If `v` is
`E`-linearly independent and `w` is arbitrary, then `v + κ(c) w` is
`E`-linearly independent for all but finitely many `c ∈ k`. -/
theorem division_pencil_finite {Z : Type*} [AddCommGroup Z] [Module E Z]
    {ι : Type*} [Finite ι] (v w : ι → Z) (hv : LinearIndependent E v) :
    {c : k | ¬ LinearIndependent E (fun i => v i + κ c • w i)}.Finite := by
  refine (pencil_ker_finite κ hκ (Finsupp.linearCombination E v)
    (Finsupp.linearCombination E w) hv).subset ?_
  intro c hc
  simp only [Set.mem_ofPred_eq, linearIndependent_iff, not_forall] at hc
  obtain ⟨l, hl, hl0⟩ := hc
  refine ⟨l, hl0, ?_⟩
  rw [← hl, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.smul_sum, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [smul_add, smul_smul, smul_smul, hκ]

end SymplecticStafford.Paper
