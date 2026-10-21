module

public import SymplecticStafford.Filtered.OriginalCentralSupport

@[expose] public section

/-!
# Independent oracle for the original-central support bridge

The zero right ideal of `ℤ` gives a nonzero original quotient.  The oracle
checks the concrete class/membership bridge, the nonempty central support,
the empty-support endpoint, and the `WithBot Nat`/integer terminal encoding.
-/

namespace SymplecticStafford.OriginalCentralSupportOracle

open SymplecticStafford
open SymplecticStafford.Filtered

def zeroRightIdeal : RingRightIdeal (R := ℤ) where
  carrier := {0}
  zero_mem := by simp
  add_mem := by
    intro a b ha hb
    change a = 0 at ha
    change b = 0 at hb
    change a + b = 0
    rw [ha, hb, add_zero]
  neg_mem := by
    intro a ha
    change a = 0 at ha
    change -a = 0
    rw [ha, neg_zero]
  right_mul_mem := by
    intro a ha r
    change a = 0 at ha
    change a * r = 0
    rw [ha, zero_mul]

example : (Submodule.Quotient.mk (1 : ℤ) :
    OriginalRightQuotient zeroRightIdeal) ≠ 0 := by
  intro h
  have hmem : (1 : ℤ) ∈ zeroRightIdeal :=
    (originalRightQuotient_mk_eq_zero_iff_mem zeroRightIdeal 1).mp h
  change (1 : ℤ) = 0 at hmem
  norm_num at hmem

example :
    (OriginalCentralCharacteristicSupport zeroRightIdeal).Nonempty := by
  apply (originalCentralCharacteristicSupport_nonempty_iff zeroRightIdeal).mpr
  exact ⟨⟨Submodule.Quotient.mk (1 : ℤ), 0,
    by
      intro h
      have hmem : (1 : ℤ) ∈ zeroRightIdeal :=
        (originalRightQuotient_mk_eq_zero_iff_mem zeroRightIdeal 1).mp h
      change (1 : ℤ) = 0 at hmem
      norm_num at hmem⟩⟩

example : OriginalCentralCharacteristicSupport zeroRightIdeal ≠ ∅ := by
  intro h
  have : (OriginalCentralCharacteristicSupport zeroRightIdeal).Nonempty := by
    apply (originalCentralCharacteristicSupport_nonempty_iff zeroRightIdeal).mpr
    exact ⟨⟨Submodule.Quotient.mk (1 : ℤ), 0,
      by
        intro hq
        have hmem : (1 : ℤ) ∈ zeroRightIdeal :=
          (originalRightQuotient_mk_eq_zero_iff_mem zeroRightIdeal 1).mp hq
        change (1 : ℤ) = 0 at hmem
        norm_num at hmem⟩⟩
  exact Set.not_nonempty_empty (h ▸ this)

example : (1 : ℤ) ∉ zeroRightIdeal := by
  change (1 : ℤ) ≠ 0
  norm_num

example :
    OriginalCentralCharacteristicSupport zeroRightIdeal = ∅ ↔
      (1 : ℤ) ∈ zeroRightIdeal :=
  originalCentralCharacteristicSupport_empty_iff_one_mem zeroRightIdeal

def bottomWitness : DimensionDefectWitness where
  dimension := ⊥
  defect := -1
  defect_eq_dimension := rfl

example : bottomWitness.dimension = (⊥ : SupportDimension) := by
  exact bottomWitness.bot_of_defect_le_neg_one (by rfl)

example (n : Nat) :
    supportDimensionDefect (n : SupportDimension) ≠ -1 := by
  intro h
  exact (WithBot.coe_ne_bot :
    (n : SupportDimension) ≠ (⊥ : SupportDimension))
    ((supportDimensionDefect_eq_neg_one_iff (n : SupportDimension)).mp h)

end SymplecticStafford.OriginalCentralSupportOracle

#print axioms SymplecticStafford.OriginalCentralSupportOracle.bottomWitness
#print axioms SymplecticStafford.OriginalCentralSupportOracle.zeroRightIdeal
