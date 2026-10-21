module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Support
public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Ordered.CharacteristicSupportFiniteProducer

@[expose] public section

/-!
Independent trust-disabled consumer for the finite-colon M08 bridge.  The
coefficient modules are `ZMod 1`, so the localized-zero field is discharged
by an actual subsingleton instance.  The colon witness and the affine
producer remain concrete original-ring data; no support-union proposition is
postulated.
-/

namespace SymplecticStaffordTest.CharacteristicSupportFiniteProducer

open SymplecticStafford
open SymplecticStafford.Ordered

abbrev Q := ZMod 1

def idInjective : Function.Injective (RingHom.id ℤ) := by
  intro a b h
  exact h

def producerData : AmbientProducerData (RingHom.id ℤ) (1 : ℤ) 2 3 1 2 where
  localA := (-1 : ℤ)
  localB := (1 : ℤ)
  localC := (-2 : ℤ)
  localZ := (1 : ℤ)
  denominator := 1
  A0s := 5
  A1s := 6
  S0s := -2
  hdiv := by norm_num
  hold := by norm_num
  hnew := by norm_num
  clear_A0 := by norm_num
  clear_A1 := by norm_num
  clear_S0 := by norm_num

def integerColonGeneration : FiniteRightGeneration (R := ℤ)
    (commonColonRightIdeal 1 3) where
  generators := {1}
  mem_iff := by
    intro x
    constructor
    · intro hx
      refine ⟨fun _ => x, ?_⟩
      simp [Finset.sum_singleton]
    · intro hx
      rcases hx with ⟨c, hc⟩
      refine ⟨3 * x, ?_⟩
      rw [hc]
      ring

def finiteData :
    FiniteColonCharacteristicSupportProducer
      (A := ℤ) (QF := Q) (QG := Q)
      (RingHom.id ℤ) (RingHom.id ℤ) 1 2 3 1 2 Q where
  injective := idInjective
  local_producer := by
    intro p hpF hpG
    refine ⟨producerData, ?_⟩
    exact (Ideal.ne_top_iff_one p.asIdeal).mp p.isPrime.ne_top
  colon_generators := integerColonGeneration
  common_zero_of_cleared_expansion := by
    intro p s hs hexpand
    infer_instance

example :
    characteristicSupport (A := ℤ) Q ⊆
      characteristicSupport (A := ℤ) Q ∪ characteristicSupport (A := ℤ) Q := by
  exact characteristicSupport_commonIdeal_subset_union_of_finite_colon_generation
    (A := ℤ) (QJ := Q) (QF := Q) (QG := Q)
    (RingHom.id ℤ) (RingHom.id ℤ) 1 2 3 1 2 finiteData

example :
    ∃ r : ℤ, ∃ c : ℤ → ℤ,
      producerData.denominator = 1 * r +
        ∑ k ∈ integerColonGeneration.generators, (2 * 1) * k * c k := by
  exact ambient_denominator_colon_generator_expansion
    (A := ℤ) (QF := Q) (QG := Q)
    (RingHom.id ℤ) (RingHom.id ℤ) 1 2 3 1 2 finiteData producerData

example : ∀ k ∈ integerColonGeneration.generators, ∀ t : ℤ,
    (∀ y : ℤ, t * y = y * t) →
      ∃ c : ℤ,
        3 * 1 * k = 1 * c ∧
          2 * 1 * k = 1 * (-t * c) + (2 + t * 3) * 1 * k := by
  intro k hk t ht
  exact (characteristicSupport_commonIdeal_subset_union_with_colon_pencil_certificates
    (A := ℤ) (QJ := Q) (QF := Q) (QG := Q)
    (RingHom.id ℤ) (RingHom.id ℤ) 1 2 3 1 2 finiteData).2 k hk t ht

end SymplecticStaffordTest.CharacteristicSupportFiniteProducer

#print axioms
  SymplecticStaffordTest.CharacteristicSupportFiniteProducer.finiteData
