module

public import SymplecticStafford.FiniteLength.FiniteCentralDivisionPencil
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

@[expose] public section

/-!
# A determinant-free finite-central division-block pencil

This is an independent proof of the finite bad-scalar statement.  The
division ring `E` is retained in the realization hypothesis; only the finite
coefficient space `P` is viewed over the central field `K`.  A split initial
map turns every nonzero bad parameter into a central eigenvalue of one
`K`-linear endomorphism.  The finite spectrum (equivalently the nonzero
minimal-polynomial norm) gives finiteness; no matrix determinant or arbitrary
zero pencil is used.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

variable {K : Type u} {E : Type v} {V : Type w} {P : Type*}
variable [Field K] [Infinite K] [DivisionRing E]
variable [AddCommGroup V] [Module K V] [Module E V] [Module K E]
variable [AddCommGroup P] [Module K P] [FiniteDimensional K P]
variable {ι : Type*} [Fintype ι]

theorem finite_bad_of_split_central_pencil_spectrum
    (block : K → ι → V)
    (base : P →ₗ[K] V) (direction : P →ₗ[K] V)
    (retract : V →ₗ[K] P)
    (split : retract.comp base = LinearMap.id)
    (realization : ∀ z : K,
      LinearIndependent E (block z) ↔
        Function.Injective (base + z • direction)) :
    Set.Finite {z : K | ¬ LinearIndependent E (block z)} := by
  let f : Module.End K P := retract.comp direction
  have hf : Set.Finite (spectrum K f) := Module.End.finite_spectrum f
  let image : Set K := (fun μ : K => -μ⁻¹) '' spectrum K f
  have himage : image.Finite := hf.image _
  have htarget : (({0} : Set K) ∪ image).Finite :=
    (Set.finite_singleton (0 : K)).union himage
  apply htarget.subset
  intro z hz
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  right
  have hnotinj : ¬ Function.Injective (base + z • direction) := by
    intro hinj
    apply hz
    exact (realization z).mpr hinj
  have hkerne : (base + z • direction).ker ≠ ⊥ :=
    (LinearMap.ker_eq_bot.not).mpr hnotinj
  obtain ⟨x, hxker, hx⟩ := (Submodule.ne_bot_iff _).mp hkerne
  have hker : (base + z • direction) x = 0 := hxker
  have hcomp : (retract.comp (base + z • direction)) x = 0 := by
    rw [LinearMap.comp_apply]
    rw [show (base + z • direction) x = 0 from hker]
    simp
  have hsplitx : retract (base x) = x := by
    have hsx := congrArg (fun g : P →ₗ[K] P => g x) split
    simpa [LinearMap.comp_apply] using hsx
  have heq : f x = (-z⁻¹) • x := by
    have hlin : x + z • f x = 0 := by
      have hcomp' : retract (base x + z • direction x) = 0 := by
        simpa [LinearMap.comp_apply, LinearMap.add_apply,
          LinearMap.smul_apply] using hcomp
      rw [LinearMap.map_add, LinearMap.map_smul, hsplitx] at hcomp'
      simpa [f, LinearMap.comp_apply] using hcomp'
    have := congrArg (fun y : P => z⁻¹ • y) hlin
    have hlin' : z⁻¹ • x + f x = 0 := by
      simpa [smul_add, smul_smul, inv_mul_cancel₀ hz0] using this
    simpa [neg_smul] using (eq_neg_of_add_eq_zero_right hlin')
  have hevec : f.HasEigenvector (-z⁻¹) x := by
    rw [Module.End.hasEigenvector_iff]
    exact ⟨Module.End.mem_eigenspace_iff.mpr heq, hx⟩
  have hespec : -z⁻¹ ∈ spectrum K f :=
    (Module.End.hasEigenvalue_iff_mem_spectrum).mp
      (Module.End.hasEigenvalue_of_hasEigenvector hevec)
  refine ⟨-z⁻¹, hespec, ?_⟩
  field_simp

/-! The block-level form is the advertised arbitrary division-ring theorem.
The only nonzero hypothesis is the displayed `E`-independence of the initial
tuple.  The split map is built from that independence, and the proof then
uses the determinant-free theorem above. -/

theorem finite_bad_of_finite_central_division_pencil_spectrum
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
        _ = (ιmap z * q i) • y i := by rw [central_embedding]
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
      constructor <;> intro h q q' hqq
      · apply h
        rw [hcomb z q, hcomb z q']
        exact hqq
      · apply h
        rw [← hcomb z q, ← hcomb z q']
        exact hqq]
  exact finite_bad_of_split_central_pencil_spectrum
    (block := fun z i => x i + (ιmap z) • y i)
    baseK dirK retract hsplit hreal

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.finite_bad_of_split_central_pencil_spectrum
#print axioms SymplecticStafford.FiniteLength.finite_bad_of_finite_central_division_pencil_spectrum
