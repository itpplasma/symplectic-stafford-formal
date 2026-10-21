module

public import Mathlib.Data.Nat.Prime.Int
public import SymplecticStafford.Ordered.M08IdealQuotientExact

@[expose] public section

/-!
Independent trust-disabled oracle for the actual commutative ideal-chain
sequence.  The concrete chain `(6) ≤ (2)` in `ℤ` has a nonzero class in
`(2)/(6)`, and the oracle checks the induced actions and consumes the
resulting actual support equality.
-/

namespace SymplecticStaffordTest.M08IdealQuotientExact

open SymplecticStafford.Ordered

abbrev I6 : Ideal ℤ := Ideal.span ({(6 : ℤ)} : Set ℤ)
abbrev J2 : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)

theorem I6_le_J2 : I6 ≤ J2 := by
  rw [I6, J2, Ideal.span_singleton_le_span_singleton]
  norm_num

theorem two_not_mem_I6 : (2 : ℤ) ∉ I6 := by
  intro h
  rw [I6, Ideal.mem_span_singleton] at h
  rcases h with ⟨c, hc⟩
  omega

def twoClass :
    (J2 ⧸ idealQuotientKernel I6 J2) :=
  Submodule.Quotient.mk (p := idealQuotientKernel I6 J2)
    ⟨2, by
      exact Ideal.subset_span (by simp)⟩

theorem twoClass_left_action :
    idealQuotientLeftMap I6 J2 I6_le_J2 twoClass = I6.mkQ 2 := by
  change I6.mkQ 2 = I6.mkQ 2
  rfl

theorem twoClass_is_nonzero :
    I6.mkQ 2 ≠ 0 := by
  intro hzero
  apply two_not_mem_I6
  exact (Submodule.Quotient.mk_eq_zero I6).mp hzero

theorem fourClass_right_action :
    idealQuotientRightMap I6 J2 I6_le_J2 (I6.mkQ 4) = J2.mkQ 4 := by
  change J2.mkQ 4 = J2.mkQ 4
  rfl

theorem twoClass_right_maps_to_zero :
    idealQuotientRightMap I6 J2 I6_le_J2 (I6.mkQ 2) = 0 := by
  change J2.mkQ 2 = 0
  apply (Submodule.Quotient.mk_eq_zero J2).mpr
  exact Ideal.subset_span (by simp)

theorem oneClass_right_maps_to_nonzero :
    idealQuotientRightMap I6 J2 I6_le_J2 (I6.mkQ 1) ≠ 0 := by
  intro hzero
  have hone : (1 : ℤ) ∈ J2 := by
    apply (Submodule.Quotient.mk_eq_zero J2).mp
    exact hzero
  rw [J2, Ideal.mem_span_singleton] at hone
  rcases hone with ⟨c, hc⟩
  omega

theorem concrete_support_equality :
    Module.support ℤ (ℤ ⧸ I6) =
      Module.support ℤ (J2 ⧸ idealQuotientKernel I6 J2) ∪
        Module.support ℤ (ℤ ⧸ J2) :=
  idealQuotient_support_eq_union I6 J2 I6_le_J2

def primeTwo : PrimeSpectrum ℤ :=
  ⟨J2, (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two⟩

theorem primeTwo_middle_support :
    primeTwo ∈ Module.support ℤ (ℤ ⧸ I6) := by
  apply Module.mem_support_iff_of_finite.mpr
  rw [Ideal.annihilator_quotient]
  exact I6_le_J2

theorem primeTwo_support_consumed :
    primeTwo ∈ Module.support ℤ (J2 ⧸ idealQuotientKernel I6 J2) ∪
      Module.support ℤ (ℤ ⧸ J2) := by
  rw [← concrete_support_equality]
  exact primeTwo_middle_support

example (p : PrimeSpectrum ℤ)
    (hp : p ∈ Module.support ℤ (ℤ ⧸ I6)) :
    p ∈ Module.support ℤ (J2 ⧸ idealQuotientKernel I6 J2) ∪
      Module.support ℤ (ℤ ⧸ J2) := by
  rw [← concrete_support_equality]
  exact hp

end SymplecticStaffordTest.M08IdealQuotientExact

#print axioms SymplecticStaffordTest.M08IdealQuotientExact.I6_le_J2
#print axioms SymplecticStaffordTest.M08IdealQuotientExact.twoClass_left_action
#print axioms SymplecticStaffordTest.M08IdealQuotientExact.concrete_support_equality
#print axioms SymplecticStaffordTest.M08IdealQuotientExact.twoClass_is_nonzero
#print axioms SymplecticStaffordTest.M08IdealQuotientExact.primeTwo_support_consumed
