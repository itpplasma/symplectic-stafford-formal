module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import SymplecticStafford.Filtered.M01StructuralClass

@[expose] public section

/-! Independent oracle for the structural M01 interface. -/

namespace SymplecticStafford.M01StructuralClassOracle

open SymplecticStafford.Filtered

section PolynomialCalibration

noncomputable section

local instance : Algebra ℚ (Polynomial ℚ) := Polynomial.algebraOfAlgebra

def polynomialFiltration : AdditiveFilteredRingData (Polynomial ℚ) where
  carrier n :=
    { carrier := {p | p.natDegree ≤ n}
      zero_mem' := by simp
      add_mem' := by
        intro p q hp hq
        exact (Polynomial.natDegree_add_le p q).trans
          (max_le hp hq)
      neg_mem' := by
        intro p hp
        simpa [Polynomial.natDegree_neg] using hp }
  one_mem := by simp
  mul_mem := by
    intro i j p q hp hq
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp hq)
  monotone := by
    intro i j hij p hp
    exact hp.trans hij
  exhaustive := by
    intro p
    exact ⟨p.natDegree, by
      change p.natDegree ≤ p.natDegree
      exact le_rfl⟩

def polynomialModel : M01FilteredAlgebra ℚ (Polynomial ℚ) where
  filtration := polynomialFiltration
  central := by intro k p; simp [Polynomial.C_mul, mul_comm]
  degree_zero := by
    ext p
    constructor
    · intro hp
      exact ⟨p.coeff 0, by
        rw [show p = Polynomial.C (p.coeff 0) by
          apply Polynomial.eq_C_of_natDegree_le_zero
          exact hp]
        simpa using (Polynomial.C_eq_algebraMap (R := ℚ) _).symm⟩
    · rintro ⟨k, rfl⟩
      change (algebraMap ℚ (Polynomial ℚ) k).natDegree ≤ 0
      simp [Polynomial.algebraMap_apply]

example {p : Polynomial ℚ} (hp : p ≠ 0) :
    ∃ n : ℕ, ∃ hnp : p ∈ polynomialModel.filtration.carrier n,
      AdditiveFilteredRingData.associatedClass
        polynomialModel.filtration n p hnp ≠ 0 :=
  polynomialModel.separated_detection hp

example : Polynomial.X ∈ polynomialModel.filtration.carrier 1 := by
  change Polynomial.X.natDegree ≤ 1
  simp

example :
    AdditiveFilteredRingData.associatedClass polynomialModel.filtration 1
        Polynomial.X (by
          change Polynomial.X.natDegree ≤ 1
          simp) ≠ 0 := by
  intro h
  have hmem :=
    (AdditiveFilteredRingData.associatedClass_eq_zero_iff
      polynomialModel.filtration 1 Polynomial.X (by
        change Polynomial.X.natDegree ≤ 1
        simp)).mp h
  change Polynomial.X.natDegree ≤ 0 at hmem
  simp at hmem

end

end PolynomialCalibration

abbrev K := ℚ
abbrev R := ℚ

def constantFiltration : AdditiveFilteredRingData R where
  carrier := fun _ => ⊤
  one_mem := by simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij a ha; simp
  exhaustive := by intro a; exact ⟨0, by simp⟩

def model : M01FilteredAlgebra K R where
  filtration := constantFiltration
  central := by intro k a; ring
  degree_zero := by
    ext a
    constructor
    · intro ha
      exact ⟨a, by simp⟩
    · rintro ⟨k, rfl⟩
      exact (show k ∈ (⊤ : AddSubgroup R) by simp)

example :
    (model.filtration.carrier 0 : Set R) = Set.range (algebraMap K R) :=
  model.degree_zero

example {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ hna : a ∈ model.filtration.carrier n,
      AdditiveFilteredRingData.associatedClass model.filtration n a hna ≠ 0 :=
  model.separated_detection ha

example :
    Function.Injective (algebraMap K R) :=
  M01FilteredAlgebra.algebraMap_injective

example :
    Subring (ReesPolynomial R) :=
  model.reesRing

end SymplecticStafford.M01StructuralClassOracle

#print axioms SymplecticStafford.M01StructuralClassOracle.model
#print axioms SymplecticStafford.Filtered.M01FilteredAlgebra.separated_detection
