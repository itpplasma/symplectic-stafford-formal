module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Central-parameter pencils in Artinian modules (paper §4.5)

This file proves the pencil statements of the manuscript (Corollary 4.8 and
Proposition 4.7) for an arbitrary Artinian left module over an algebra `A`
over a field `k`.  Right modules over a ring `T` are the case `A = Tᵐᵒᵖ`.

The single engine is `chain_bad_finite`: if for infinitely many central
scalars `λ` a submodule `N λ` contains `(1 + λ c) • x` but not `x`, then the
finite intersections of these submodules form an infinite strictly
decreasing chain.  The separating elements are `p(c) • x` for the ordered
products `p = ∏ (1 + λᵢ X)`, evaluated in the commutative subalgebra `k[c]`.

This replaces the isotypic top-block reduction of the manuscript by a direct
Artinian chain argument; the statements are unchanged.
-/

namespace SymplecticStafford.Paper

open Polynomial

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- The evaluation of the polynomial `1 + λ X` at `c`. -/
theorem aeval_one_add_C_mul_X (c : A) (l : k) :
    aeval c (1 + C l * X) = 1 + algebraMap k A l * c := by
  simp [aeval_C]

/-- **Chain lemma.**  In an Artinian module, only finitely many central
scalars `λ` admit a submodule `N λ` containing `(1 + λ c) • x` but not `x`. -/
theorem chain_bad_finite [IsArtinian A M] (x : M) (c : A) (N : k → Submodule A M) :
    {l : k | (1 + algebraMap k A l * c) • x ∈ N l ∧ x ∉ N l}.Finite := by
  classical
  by_contra hinf
  set L := {l : k | (1 + algebraMap k A l * c) • x ∈ N l ∧ x ∉ N l} with hL
  let e : ℕ ↪ L := Set.Infinite.natEmbedding L hinf
  let lam : ℕ → k := fun i => (e i : k)
  have lam_inj : Function.Injective lam := fun i j h => e.injective (Subtype.ext h)
  have lam_mem : ∀ i, (1 + algebraMap k A (lam i) * c) • x ∈ N (lam i) := fun i => (e i).2.1
  have lam_not : ∀ i, x ∉ N (lam i) := fun i => (e i).2.2
  have lam_ne : ∀ i, lam i ≠ 0 := by
    intro i hi
    apply lam_not i
    simpa [hi] using lam_mem i
  -- The polynomials `P m = ∏_{i<m} (1 + λᵢ X)`.
  let P : ℕ → k[X] := fun m => ∏ i ∈ Finset.range m, (1 + C (lam i) * X)
  let K : ℕ → Submodule A M := fun m => ⨅ i ∈ Finset.range m, N (lam i)
  -- `P m (c) • x` lies in every `N (λ i)` with `i < m`.
  have hmemK : ∀ m, aeval c (P m) • x ∈ K m := by
    intro m
    simp only [K, Submodule.mem_iInf]
    intro i hi
    have hsplit : P m = (∏ j ∈ (Finset.range m).erase i, (1 + C (lam j) * X)) *
        (1 + C (lam i) * X) := by
      simp only [P]
      rw [mul_comm]
      exact (Finset.mul_prod_erase _ (fun j => 1 + C (lam j) * X) hi).symm
    rw [hsplit, map_mul, aeval_one_add_C_mul_X, mul_smul]
    exact Submodule.smul_mem _ _ (lam_mem i)
  -- but not in `N (λ m)`.
  have hnotN : ∀ m, aeval c (P m) • x ∉ N (lam m) := by
    intro m hm
    set a : k := -(lam m)⁻¹
    set r : k := eval a (P m)
    have hr : r ≠ 0 := by
      simp only [r, P, eval_prod]
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have hi' : i ≠ m := (Finset.mem_range.mp hi).ne
      simp only [eval_add, eval_one, eval_mul, eval_C, eval_X, a]
      intro h0
      apply hi'
      apply lam_inj
      have hm0 := lam_ne m
      field_simp at h0
      linear_combination -h0
    have hroot : IsRoot (P m - C r) a := by
      simp [IsRoot, r]
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := P m - C r) (a := a)).mpr hroot
    set q := (P m - C r) /ₘ (X - C a)
    have hPm : P m = q * (X - C a) + C r := by
      rw [mul_comm]; rw [hdiv]; ring
    -- `(c - a) • x ∈ N (λ m)`.
    have hlin : (aeval c (X - C a)) • x ∈ N (lam m) := by
      have : aeval c (X - C a) = algebraMap k A (lam m)⁻¹ *
          (1 + algebraMap k A (lam m) * c) := by
        simp only [map_sub, aeval_X, aeval_C, a, map_neg, mul_add, mul_one, ← mul_assoc,
          ← map_mul, inv_mul_cancel₀ (lam_ne m), map_one, one_mul]
        abel
      rw [this, mul_smul]
      exact Submodule.smul_mem _ _ (lam_mem m)
    have hq : (aeval c (q * (X - C a))) • x ∈ N (lam m) := by
      rw [map_mul, mul_smul]
      exact Submodule.smul_mem _ _ hlin
    have hrx : (algebraMap k A r) • x ∈ N (lam m) := by
      have h2 : aeval c (P m) • x - (aeval c (q * (X - C a))) • x = (algebraMap k A r) • x := by
        rw [← sub_smul, hPm, map_add, aeval_C]
        abel_nf
      rw [← h2]
      exact Submodule.sub_mem _ hm hq
    apply lam_not m
    have := Submodule.smul_mem (N (lam m)) (algebraMap k A r⁻¹) hrx
    rwa [← mul_smul, ← map_mul, inv_mul_cancel₀ hr, map_one, one_smul] at this
  -- Hence `K` is strictly decreasing.
  have hanti : StrictAnti K := by
    apply strictAnti_nat_of_succ_lt
    intro m
    refine lt_of_le_of_ne ?_ ?_
    · simp only [K]
      exact iInf₂_mono' fun i hi => ⟨i, Finset.mem_range.mpr
        (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)), le_rfl⟩
    · intro heq
      apply hnotN m
      have h := hmemK m
      rw [← heq] at h
      simp only [K, Submodule.mem_iInf] at h
      exact h m (Finset.mem_range.mpr (Nat.lt_succ_self m))
  exact not_strictAnti_of_wellFoundedLT K hanti

/-- **Corollary 4.8 (preservation of a generating vector).**  If `x` generates
an Artinian module and `y` is arbitrary, then `x + λ y` generates for all but
finitely many central scalars `λ`. -/
theorem generator_pencil_finite [IsArtinian A M] {x : M}
    (hx : Submodule.span A {x} = ⊤) (y : M) :
    {l : k | Submodule.span A {x + algebraMap k A l • y} ≠ ⊤}.Finite := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hx ▸ Submodule.mem_top : y ∈ _)
  refine (chain_bad_finite x c (fun l => Submodule.span A {x + algebraMap k A l • y})).subset ?_
  intro l hl
  have heq : x + algebraMap k A l • y = (1 + algebraMap k A l * c) • x := by
    rw [← hc, add_smul, one_smul, mul_smul]
  refine ⟨?_, ?_⟩
  · rw [← heq]; exact Submodule.mem_span_singleton_self _
  · intro hxN
    apply hl
    rw [eq_top_iff, ← hx, Submodule.span_le, Set.singleton_subset_iff]
    exact hxN

/-- **Proposition 4.7 (activated pencil), left-module form.**  In an Artinian
module generated by `e`, suppose `L • v = 0` and `e = B • v + L • u`.  Then
`v + λ u` generates for all but finitely many central scalars `λ`.

For a right module over `T` (that is `A = Tᵐᵒᵖ`) the hypotheses read
`v L = 0` and `e = v B + u L`, exactly as in the manuscript. -/
theorem activated_pencil_finite [IsArtinian A M] {e v u : M} {B L : A}
    (he : Submodule.span A {e} = ⊤) (hvL : L • v = 0) (heq : e = B • v + L • u) :
    {l : k | Submodule.span A {v + algebraMap k A l • u} ≠ ⊤}.Finite := by
  obtain ⟨cu, hcu⟩ := Submodule.mem_span_singleton.mp (he ▸ Submodule.mem_top : u ∈ _)
  refine ((chain_bad_finite e (B * cu)
    (fun l => Submodule.span A {v + algebraMap k A l • u})).union
      (Set.finite_singleton (0 : k))).subset ?_
  intro l hl
  by_cases hl0 : l = 0
  · exact Or.inr hl0
  left
  set W := Submodule.span A {v + algebraMap k A l • u}
  have hw : v + algebraMap k A l • u ∈ W := Submodule.mem_span_singleton_self _
  have hLu : L • u ∈ W := by
    have h1 : L • (v + algebraMap k A l • u) = algebraMap k A l • (L • u) := by
      rw [smul_add, hvL, zero_add, ← mul_smul, ← mul_smul, Algebra.commutes]
    have h2 := Submodule.smul_mem W (algebraMap k A l⁻¹) (Submodule.smul_mem W L hw)
    rwa [h1, ← mul_smul, ← map_mul, inv_mul_cancel₀ hl0, map_one, one_smul] at h2
  refine ⟨?_, ?_⟩
  · have hexp : (1 + algebraMap k A l * (B * cu)) • e =
        B • (v + algebraMap k A l • u) + L • u := by
      rw [add_smul, one_smul, mul_smul, mul_smul, hcu, smul_add, ← mul_smul B,
        ← Algebra.commutes, mul_smul]
      conv_lhs => rw [heq]
      abel
    rw [hexp]
    exact W.add_mem (W.smul_mem B hw) hLu
  · intro heW
    apply hl
    rw [eq_top_iff, ← he, Submodule.span_le, Set.singleton_subset_iff]
    exact heW

end SymplecticStafford.Paper
