import SymplecticStafford.FiniteLength.CentralFinitePencil
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite-dimensional-over-the-center division blocks

`IsotypicBlocks` deliberately leaves the finite exceptional-set statement as
a hypothesis for arbitrary division rings.  This file supplies a positive
bridge when each division ring is finite-dimensional over the central
parameter field.  The coefficient space `ι →₀ E` is then finite-dimensional
over `K`; its `E`-linear combination map is restricted to `K`, and a left
inverse supplies the split realization required by `CentralFinitePencil`.

The centrality equations are explicit.  In particular, this file does not
silently identify a noncommutative division ring with a central matrix ring.
It proves the finite bad-set input for the activated-pencil consumer, but it
does not construct the Jacobson-top/block comparison or a universal
finite-length filtration.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section Single

variable {K : Type u} {E : Type v} {V : Type w}
variable [Field K] [Infinite K] [DivisionRing E]
variable [AddCommGroup V] [Module E V] [Module K V] [Module K E]
variable {ι : Type*} [Fintype ι]

/-- A finite-dimensional-over-the-center repeated division-ring pencil has
only finitely many parameters at which its initially independent block loses
independence.

`central_coeff` identifies the `K`-action on coefficients with the chosen
embedding, `central_embedding` records that the image is central in `E`, and
`central_vector` does the same on the block module.  These are the exact
compatibility fields needed by the restriction-of-scalars calculation.
-/
theorem finite_bad_of_finite_central_division_pencil
    [FiniteDimensional K E]
    (ιmap : K →+* E)
    (central_coeff : ∀ (k : K) (e : E), k • e = ιmap k * e)
    (central_embedding : ∀ (k : K) (e : E),
      ιmap k * e = e * ιmap k)
    (central_vector : ∀ (k : K) (v : V),
      k • v = (ιmap k) • v)
    (x y : ι → V)
    (hx : LinearIndependent E x) :
    Set.Finite {z : K | ¬ LinearIndependent E
      (fun i => x i + (ιmap z) • y i)} := by
  let P := ι →₀ E
  let baseE : P →ₗ[E] V := Finsupp.linearCombination E x
  let dirE : P →ₗ[E] V := Finsupp.linearCombination E y
  letI : LinearMap.CompatibleSMul P V K E :=
    ⟨by
      intro f k q
      have hq : k • q = (ιmap k) • q := by
        ext i
        change k • q i = ιmap k * q i
        rw [central_coeff]
      calc
        f (k • q) = f ((ιmap k) • q) := by rw [hq]
        _ = (ιmap k) • f q := f.map_smul (ιmap k) q
        _ = k • f q := by rw [central_vector]⟩
  let baseK : P →ₗ[K] V := LinearMap.restrictScalars K baseE
  let dirK : P →ₗ[K] V := LinearMap.restrictScalars K dirE
  have hbaseE : baseE.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (linearIndependent_iff_injective_finsuppLinearCombination).mp hx
  have hbaseK : baseK.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro q q' hqq
    exact (LinearMap.ker_eq_bot.mp hbaseE) hqq
  let retract : V →ₗ[K] P := baseK.leftInverse
  have hsplit : retract.comp baseK = LinearMap.id := by
    exact baseK.leftInverse_comp_of_inj hbaseK
  have hcomb : ∀ (z : K) (q : P),
      (baseK + z • dirK) q =
        (Finsupp.linearCombination E
          (fun i => x i + (ιmap z) • y i)) q := by
    intro z q
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    change baseE q + z • dirE q = _
    rw [central_vector]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply]
    have hpoint :
        (fun (i : ι) (a : E) => a • (x i + (ιmap z) • y i)) =
          (fun (i : ι) (a : E) =>
            a • x i + a • ((ιmap z) • y i)) := by
      funext i a
      rw [smul_add]
    have hscalar :
        Finsupp.sum q (fun i a => a • ((ιmap z) • y i)) =
          (ιmap z) • Finsupp.sum q (fun i a => a • y i) := by
      rw [Finsupp.smul_sum]
      apply Finsupp.sum_congr
      intro i hi
      calc
        q i • ιmap z • y i = (q i * ιmap z) • y i :=
          smul_smul (q i) (ιmap z) (y i)
        _ = (ιmap z * q i) • y i := by
          rw [central_embedding]
        _ = ιmap z • q i • y i :=
          (smul_smul (ιmap z) (q i) (y i)).symm
    rw [hpoint, Finsupp.sum_add, hscalar]
  have hreal : ∀ z : K,
      LinearIndependent E (fun i => x i + (ιmap z) • y i) ↔
        Function.Injective (baseK + z • dirK) := by
    intro z
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    rw [show Function.Injective (baseK + z • dirK) ↔
        Function.Injective (Finsupp.linearCombination E
          (fun i => x i + (ιmap z) • y i)) by
      constructor <;> intro h q q' hqq'
      · apply h
        rw [hcomb z q, hcomb z q']
        exact hqq'
      · apply h
        rw [← hcomb z q, ← hcomb z q']
        exact hqq']
  exact finite_bad_of_split_central_pencil
    (block := fun z i => x i + (ιmap z) • y i)
    baseK dirK retract hsplit hreal

end Single

section Family

variable {K : Type u} [Field K] [Infinite K]
variable {J : Type v} [Fintype J] [DecidableEq J]
variable {r : J → Nat}
variable {E : J → Type w} [∀ j, DivisionRing (E j)]
variable {V : J → Type*} [∀ j, AddCommGroup (V j)]
variable [∀ j, Module (E j) (V j)] [∀ j, Module K (V j)]
variable [∀ j, Module K (E j)] [∀ j, FiniteDimensional K (E j)]

/-- Finite simultaneous avoidance for a finite family of repeated
division-ring blocks, each finite-dimensional over the same central field.
The theorem is the finite-bad-set input consumed by the isotypic activated
consumer; top/Jacobson comparison remains a separate hypothesis there.
-/
theorem finite_bad_of_finite_central_division_blocks
    (ιmap : ∀ j, K →+* E j)
    (central_coeff : ∀ (j : J) (k : K) (e : E j),
      k • e = ιmap j k * e)
    (central_embedding : ∀ (j : J) (k : K) (e : E j),
      ιmap j k * e = e * ιmap j k)
    (central_vector : ∀ (j : J) (k : K) (v : V j),
      k • v = (ιmap j k) • v)
    (x y : ∀ j, Fin (r j) → V j)
    (hx : ∀ j, LinearIndependent (E j) (x j)) :
    Set.Finite {z : K | ¬ ∀ j, LinearIndependent (E j)
      (fun i => x j i + (ιmap j z) • y j i)} := by
  classical
  have hbad : ∀ j : J, Set.Finite {z : K |
      ¬ LinearIndependent (E j)
        (fun i => x j i + (ιmap j z) • y j i)} := by
    intro j
    exact finite_bad_of_finite_central_division_pencil
      (ιmap := ιmap j) (central_coeff := central_coeff j)
      (central_embedding := central_embedding j)
      (central_vector := central_vector j) (x := x j) (y := y j) (hx j)
  have hall : (⋃ j : J, {z : K |
      ¬ LinearIndependent (E j)
        (fun i => x j i + (ιmap j z) • y j i)}).Finite := by
    exact Set.finite_iUnion hbad
  apply hall.subset
  intro z hz
  rcases not_forall.mp hz with ⟨j, hj⟩
  exact Set.mem_iUnion.2 ⟨j, hj⟩

end Family

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.finite_bad_of_finite_central_division_pencil
#print axioms
  SymplecticStafford.FiniteLength.finite_bad_of_finite_central_division_blocks
