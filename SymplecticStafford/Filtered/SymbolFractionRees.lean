import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic
import SymplecticStafford.Filtered.SymbolFractionFiltration

/-!
# The Laurent Rees subring of a selected symbol localization

Let `T` be the actual right Ore localization supplied by
`SymbolFractionFiltration.Data`.  Its integer indexed fraction filtration has
an honest Laurent Rees realization inside `AddMonoidAlgebra T ℤ`: a finite
formal sum is admitted when its coefficient in degree `z` belongs to the
actual fraction layer `F_z`.

The construction below proves only the algebraic Rees facts available from
the actual filtration.  In particular, it does not assert Noetherianity,
identify this ring with a homogeneous localization, or transfer any module
length statement.  It does prove the concrete homogeneous unit calculation
for each selected denominator.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

open SymplecticStafford
open SymbolDenominatorSubmonoid
open SymbolFractionInverse
open SymbolFractionFiltration

namespace SymbolFractionRees

variable {R : Type u} [Ring R]

abbrev T (C : SymbolFractionFiltration.Data R) :=
  C.inverse.localization.Localization

abbrev LaurentPolynomial (C : SymbolFractionFiltration.Data R) :=
  AddMonoidAlgebra (T C) ℤ

/- A bounded Laurent polynomial uses the actual integer fraction filtration,
   rather than a proposition-valued stand-in. -/
def Bounded (C : SymbolFractionFiltration.Data R)
    (p : LaurentPolynomial C) : Prop :=
  ∀ z : ℤ, p.coeff z ∈ C.fractionFiltration z

private theorem finset_sum_mem
    {A : Type*} [AddCommGroup A]
    {F : AddSubgroup A} {s : Finset α} {g : α → A}
    (hg : ∀ a ∈ s, g a ∈ F) : (∑ a ∈ s, g a) ∈ F := by
  classical
  induction s using Finset.induction_on with
  | empty => exact F.zero_mem
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact F.add_mem (hg a (by simp)) (ih (by
        intro b hb
        exact hg b (by simp [hb])))

theorem bounded_zero (C : SymbolFractionFiltration.Data R) :
    Bounded C (0 : LaurentPolynomial C) := by
  intro z
  exact (C.fractionFiltration z).zero_mem

theorem bounded_one (C : SymbolFractionFiltration.Data R) :
    Bounded C (1 : LaurentPolynomial C) := by
  intro z
  by_cases hz : z = 0
  · subst z
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single_apply]
    rw [if_pos rfl]
    exact C.degreeZeroSubring.one_mem
  · have hzero := (C.fractionFiltration z).zero_mem
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single_apply]
    rw [if_neg (Ne.symm hz)]
    exact hzero

theorem bounded_add
    (C : SymbolFractionFiltration.Data R)
    {p q : LaurentPolynomial C}
    (hp : Bounded C p) (hq : Bounded C q) :
    Bounded C (p + q) := by
  intro z
  rw [AddMonoidAlgebra.coeff_add]
  exact (C.fractionFiltration z).add_mem (hp z) (hq z)

theorem bounded_neg
    (C : SymbolFractionFiltration.Data R)
    {p : LaurentPolynomial C} (hp : Bounded C p) :
    Bounded C (-p) := by
  intro z
  simpa using (C.fractionFiltration z).neg_mem (hp z)

theorem bounded_mul
    (C : SymbolFractionFiltration.Data R)
    {p q : LaurentPolynomial C}
    (hp : Bounded C p) (hq : Bounded C q) :
    Bounded C (p * q) := by
  classical
  intro z
  rw [AddMonoidAlgebra.coeff_mul]
  apply finset_sum_mem
  intro a ha
  apply finset_sum_mem
  intro b hb
  by_cases hab : a + b = z
  · simp only [hab, if_pos]
    have hmul := C.fractionFiltration_mul_mem (hp a) (hq b)
    simpa [hab] using hmul
  · have hzero := (C.fractionFiltration z).zero_mem
    simpa [hab] using hzero

/-- The actual Laurent Rees subring attached to the fraction filtration. -/
def reesSubring (C : SymbolFractionFiltration.Data R) :
    Subring (LaurentPolynomial C) where
  carrier := {p | Bounded C p}
  zero_mem' := bounded_zero C
  add_mem' := bounded_add C
  neg_mem' := bounded_neg C
  one_mem' := bounded_one C
  mul_mem' := bounded_mul C

abbrev ReesRing (C : SymbolFractionFiltration.Data R) := reesSubring C

theorem coe_bounded (C : SymbolFractionFiltration.Data R)
    (p : ReesRing C) : Bounded C (p : LaurentPolynomial C) :=
  p.property

theorem inclusion_injective (C : SymbolFractionFiltration.Data R) :
    Function.Injective (reesSubring C).subtype := by
  intro p q h
  exact Subtype.ext h

private theorem single_bounded
    (C : SymbolFractionFiltration.Data R) (z : ℤ) (a : T C)
    (ha : a ∈ C.fractionFiltration z) :
    Bounded C (AddMonoidAlgebra.single z a) := by
  intro w
  rw [AddMonoidAlgebra.coeff_single_apply]
  by_cases hzw : z = w
  · subst w
    simpa using ha
  · have hzero := (C.fractionFiltration w).zero_mem
    simpa [hzw] using hzero

/-- A bounded homogeneous Laurent term. -/
def homogeneous
    (C : SymbolFractionFiltration.Data R) (z : ℤ) (a : T C)
    (ha : a ∈ C.fractionFiltration z) : ReesRing C :=
  ⟨AddMonoidAlgebra.single z a, single_bounded C z a ha⟩

@[simp] theorem coe_homogeneous
    (C : SymbolFractionFiltration.Data R) (z : ℤ) (a : T C)
    (ha : a ∈ C.fractionFiltration z) :
    ((homogeneous C z a ha : ReesRing C) : LaurentPolynomial C) =
      AddMonoidAlgebra.single z a := rfl

theorem homogeneous_mul
    (C : SymbolFractionFiltration.Data R)
    (z w : ℤ) (a b : T C)
    (ha : a ∈ C.fractionFiltration z)
    (hb : b ∈ C.fractionFiltration w) :
    homogeneous C z a ha * homogeneous C w b hb =
      homogeneous C (z + w) (a * b)
        (by simpa using C.fractionFiltration_mul_mem ha hb) := by
  apply Subtype.ext
  change AddMonoidAlgebra.single z a * AddMonoidAlgebra.single w b =
    AddMonoidAlgebra.single (z + w) (a * b)
  rw [AddMonoidAlgebra.single_mul_single]

/- The identity has degree zero in the actual fraction filtration. -/
private theorem denominator_degree_one
    (C : SymbolFractionFiltration.Data R) :
    C.inverse.denominator_degree (1 : C.inverse.localization.denominators) = 0 := by
  let hmem : (1 : R) ∈
      SymbolDenominatorSubmonoid.submonoid C.inverse.filtration C.inverse.symbols :=
    (SymbolDenominatorSubmonoid.submonoid C.inverse.filtration C.inverse.symbols).one_mem
  have hzero : SymbolDenominatorSubmonoid.Admissible
      C.inverse.filtration C.inverse.symbols (1 : R) 0 :=
    ⟨C.inverse.filtration.one_mem, C.inverse.symbols.one_mem⟩
  have hdeg : SymbolDenominatorSubmonoid.degree
      C.inverse.filtration C.inverse.symbols hmem = 0 := by
    apply SymbolDenominatorSubmonoid.degree_eq_of_minimal
      C.inverse.filtration C.inverse.symbols hzero
    intro n hn
    omega
  dsimp [SymbolFractionInverse.Data.denominator_degree]
  simpa [hmem, C.inverse.denominators_eq_submonoid] using hdeg

/- The image of a selected denominator is in the corresponding actual
   fraction layer.  The denominator `1` in the clearing witness has degree
   zero by the preceding least-degree calculation. -/
theorem numerator_mem_degree
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) :
    C.inverse.localization.numerator (s : R) ∈
      C.fractionFiltration (Int.ofNat (C.inverse.denominator_degree s)) := by
  change C.inverse.fractionDegreeAtMost
    (Int.ofNat (C.inverse.denominator_degree s))
    (C.inverse.localization.numerator (s : R))
  rcases C.inverse.denominator_admissible s with ⟨hs, _hSigma⟩
  refine Or.inr ⟨(s : R), (1 : C.inverse.localization.denominators),
    C.inverse.denominator_degree s, hs, ?_, ?_⟩
  · simp
  · rw [denominator_degree_one C]
    simp

noncomputable def homogeneousDenominator
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) : ReesRing C :=
    homogeneous C (Int.ofNat (C.inverse.denominator_degree s))
    (C.inverse.localization.numerator (s : R))
    (numerator_mem_degree C s)

private noncomputable def denominatorInverse
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) : T C :=
  ((IsUnit.unit (C.inverse.localization.denominator_unit s)).inv : T C)

private theorem denominatorInverse_mul_numerator
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) :
    denominatorInverse C s *
        C.inverse.localization.numerator (s : R) = 1 := by
  let h := C.inverse.localization.denominator_unit s
  have hunit : (IsUnit.unit h : T C) =
      C.inverse.localization.numerator (s : R) := IsUnit.unit_spec h
  calc
    ((IsUnit.unit h).inv : T C) *
        C.inverse.localization.numerator (s : R) =
        ((IsUnit.unit h).inv : T C) * (IsUnit.unit h : T C) :=
      congrArg (fun x : T C => ((IsUnit.unit h).inv : T C) * x)
        hunit.symm
    _ = 1 := Units.inv_mul _

private theorem numerator_mul_denominatorInverse
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) :
    C.inverse.localization.numerator (s : R) * denominatorInverse C s = 1 := by
  let h := C.inverse.localization.denominator_unit s
  have hunit : (IsUnit.unit h : T C) =
      C.inverse.localization.numerator (s : R) := IsUnit.unit_spec h
  calc
    C.inverse.localization.numerator (s : R) *
        ((IsUnit.unit h).inv : T C) =
        (IsUnit.unit h : T C) * ((IsUnit.unit h).inv : T C) :=
      congrArg (fun x : T C => x * ((IsUnit.unit h).inv : T C))
        hunit.symm
    _ = 1 := Units.mul_inv _

theorem denominatorInverse_mem_neg_degree
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) :
    denominatorInverse C s ∈
      C.fractionFiltration (-Int.ofNat (C.inverse.denominator_degree s)) := by
  change C.inverse.fractionDegreeAtMost
    (-Int.ofNat (C.inverse.denominator_degree s))
    (denominatorInverse C s)
  rcases C.inverse.denominator_admissible s with ⟨_hs, _hSigma⟩
  refine Or.inr ⟨(1 : R), s, 0, C.inverse.filtration.one_mem, ?_, ?_⟩
  · simpa using denominatorInverse_mul_numerator C s
  · simp

  noncomputable def homogeneousDenominatorInverse
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) : ReesRing C :=
  homogeneous C (-Int.ofNat (C.inverse.denominator_degree s))
    (denominatorInverse C s) (denominatorInverse_mem_neg_degree C s)

/-- The homogeneous selected denominator is a genuine unit in the Laurent Rees
    subring.  The inverse is constructed from the actual localization unit and
    has the opposite filtration degree. -/
theorem homogeneousDenominator_isUnit
    (C : SymbolFractionFiltration.Data R)
    (s : C.inverse.localization.denominators) :
    IsUnit (homogeneousDenominator C s) := by
  refine ⟨⟨homogeneousDenominator C s,
    homogeneousDenominatorInverse C s, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change AddMonoidAlgebra.single
        (Int.ofNat (C.inverse.denominator_degree s))
        (C.inverse.localization.numerator (s : R)) *
      AddMonoidAlgebra.single
        (-Int.ofNat (C.inverse.denominator_degree s))
        (denominatorInverse C s) = 1
    rw [AddMonoidAlgebra.single_mul_single]
    simp [numerator_mul_denominatorInverse]
  · apply Subtype.ext
    change AddMonoidAlgebra.single
        (-Int.ofNat (C.inverse.denominator_degree s))
        (denominatorInverse C s) *
      AddMonoidAlgebra.single
        (Int.ofNat (C.inverse.denominator_degree s))
        (C.inverse.localization.numerator (s : R)) = 1
    rw [AddMonoidAlgebra.single_mul_single]
    simp [denominatorInverse_mul_numerator]

end SymbolFractionRees

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.SymbolFractionRees.bounded_mul
#print axioms
  SymplecticStafford.Filtered.SymbolFractionRees.numerator_mem_degree
#print axioms
  SymplecticStafford.Filtered.SymbolFractionRees.homogeneousDenominator_isUnit
