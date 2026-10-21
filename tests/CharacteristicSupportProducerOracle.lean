module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Support
public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Ordered.CharacteristicSupportProducer

@[expose] public section

/-!
Independent oracle for the actual `Module.support` M08 consumer.  All three
modules are the subsingleton `ZMod 1`, so the localized common quotient is
provably zero; the local producer and original-U clearance remain explicit.
-/

namespace SymplecticStaffordTest.CharacteristicSupportProducer

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

def localData :
    LocalCharacteristicSupportProducer (A := ℤ) (QF := Q) (QG := Q)
      (RingHom.id ℤ) (RingHom.id ℤ) 1 2 3 1 2 Q where
  injective := idInjective
  local_producer := by
    intro p hpF hpG
    refine ⟨producerData, ?_⟩
    exact (Ideal.ne_top_iff_one p.asIdeal).mp p.isPrime.ne_top
  common_zero_of_cleared_mem := by
    intro p s hs hmem
    infer_instance

example :
    characteristicSupport (A := ℤ) Q ⊆
      characteristicSupport (A := ℤ) Q ∪ characteristicSupport (A := ℤ) Q := by
  exact characteristicSupport_commonIdeal_subset_union
    (A := ℤ) (QJ := Q) (QF := Q) (QG := Q)
    (RingHom.id ℤ) (RingHom.id ℤ) 1 2 3 1 2 localData

example :
    (1 : ℤ) ∈ commonIdeal (1 : ℤ) (2 : ℤ) (3 : ℤ) := by
  simpa using (principal_mem_commonIdeal (d := (1 : ℤ)) (F := (2 : ℤ))
    (G := (3 : ℤ)) (r := (1 : ℤ)))

end SymplecticStaffordTest.CharacteristicSupportProducer
