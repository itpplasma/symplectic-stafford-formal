module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import SymplecticStafford.Filtered.GoodFiltration
public import SymplecticStafford.Filtered.WeightedFaithfulCalibration

@[expose] public section

/-!
# An actual good filtered module calibration

This is a concrete end-to-end instance over the polynomial algebra
`ℚ[X]`.  The algebra has its usual nat-degree filtration, and the rank-one
module `ℚ[X]` receives the one-generator good filtration constructed by
`GoodFiltration`.  A coordinate embedding into one finite coefficient slot is
faithful, and the diagonal weighted action detects every nonzero module
element, even when its slot has a negative integer weight.

The example is intentionally commutative and finite free.  It verifies the
module-side M04 mechanism under explicit filtration bounds, but it does not
construct the corresponding noncommutative full-symbol source theorem.
-/

namespace SymplecticStafford.Filtered

open scoped Polynomial

namespace PolynomialGoodModuleCalibration

noncomputable section

abbrev A := ℚ[X]

/-- The usual exhaustive multiplicative nat-degree filtration on `ℚ[X]`. -/
def algebraFiltration : FiltrationData A where
  carrier n := {p | p.natDegree ≤ n}
  zero_mem := by simp
  one_mem := by simp
  add_mem := by
    intro i j p q hp hq
    change p.natDegree ≤ i at hp
    change q.natDegree ≤ j at hq
    change (p + q).natDegree ≤ max i j
    exact (Polynomial.natDegree_add_le p q).trans
      (max_le (hp.trans (Nat.le_max_left _ _))
        (hq.trans (Nat.le_max_right _ _)))
  mul_mem := by
    intro i j p q hp hq
    change p.natDegree ≤ i at hp
    change q.natDegree ≤ j at hq
    change (p * q).natDegree ≤ i + j
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp hq)
  monotone := by
    intro i j hij p hp
    exact hp.trans hij
  exhaustive := by
    intro p
    exact ⟨p.natDegree, by change p.natDegree ≤ p.natDegree; rfl⟩

def generator : Fin 1 → A := fun _ => 1

theorem generator_span_top :
    Submodule.span A (Set.range generator) = ⊤ := by
  apply top_unique
  intro p hp
  have hone : (1 : A) ∈ Submodule.span A (Set.range generator) := by
    apply Submodule.subset_span
    exact ⟨0, rfl⟩
  simpa using (Submodule.smul_mem
    (Submodule.span A (Set.range generator)) p hone)

def moduleFiltration : ModuleFiltrationData algebraFiltration A :=
  GoodFiltration.moduleFiltration algebraFiltration generator
    (fun _ => 0) generator_span_top

def coordinateEncode : A →ₗ[A] (Fin 1 → A) where
  toFun p := fun _ => p
  map_add' p q := by
    funext i
    simp
  map_smul' a p := by
    funext i
    simp [smul_eq_mul]

def detector : FaithfulWeightedDetector
    (ι := Fin 1) (K := A) (M := A) where
  encode := coordinateEncode
  encode_injective := by
    intro p q h
    exact congrFun h 0
  triangular := WeightedFaithfulCalibration.diagonalSystem
    (fun _ => (-3 : Int))

def correction : Matrix (Fin 1) (Fin 1) A := fun _ _ => 0

theorem correction_sq : correction ^ 1 = 0 := by
  rw [pow_one]
  funext i j
  simp [correction]

theorem moduleFiltration_explicit_bound (p : A) :
    ModuleHasDegreeAtMost moduleFiltration p.natDegree p := by
  change p ∈ GoodFiltration.carrier algebraFiltration generator
    (fun _ => 0) p.natDegree
  apply AddSubmonoid.subset_closure
  refine ⟨0, p.natDegree, p, ?_, ?_, ?_⟩
  · simp
  · change p.natDegree ≤ p.natDegree
    rfl
  · simp [generator, smul_eq_mul]

theorem good_module_detect_nonzero {p : A} (hp : p ≠ 0) :
    ∃ n : ℕ, ModuleHasDegreeAtMost moduleFiltration n p ∧
      ∃ i, detector.triangular.action (detector.encode p) i ≠ 0 := by
  exact ⟨p.natDegree, moduleFiltration_explicit_bound p,
    detector.detect_nonzero hp⟩

theorem good_module_detect_after_correction {p : A} (hp : p ≠ 0) :
    ∃ n : ℕ, ModuleHasDegreeAtMost moduleFiltration n p ∧
      ∃ i, Matrix.vecMul
        (fun j => detector.triangular.action (detector.encode p) j)
        (1 - correction) i ≠ 0 := by
  exact ⟨p.natDegree, moduleFiltration_explicit_bound p,
    detector.detect_after_nilpotent_right_correction
      correction 1 correction_sq hp⟩

end

end PolynomialGoodModuleCalibration

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.PolynomialGoodModuleCalibration.good_module_detect_nonzero
#print axioms SymplecticStafford.Filtered.PolynomialGoodModuleCalibration.good_module_detect_after_correction
