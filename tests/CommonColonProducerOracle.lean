module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NoncommRing
public import SymplecticStafford.Ordered.CommonColonProducer

@[expose] public section

/-!
Independent oracle for the ordered common-colon producer.  The first example
uses a genuinely noncommutative matrix ambient ring with an injective scalar
map from the integers; the second checks the original-U return on integers.
-/

namespace SymplecticStaffordTest.CommonColonProducer

open SymplecticStafford
open SymplecticStafford.Ordered

theorem id_injective : Function.Injective (RingHom.id ℤ) := by
  intro a b h
  exact h

def integerData : AmbientProducerData (RingHom.id ℤ) (1 : ℤ) 2 3 1 2 where
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

example :
    integerData.denominator ∈ commonIdeal (1 : ℤ) 2 3 := by
  exact (ambient_producer_returns_original_commonIdeal (RingHom.id ℤ)
    id_injective 1 2 3 1 2 integerData).1

example :
    3 * 1 * integerData.S0s = 1 * (-integerData.A1s) := by
  exact (ambient_producer_returns_original_commonIdeal (RingHom.id ℤ)
    id_injective 1 2 3 1 2 integerData).2

example :
    (1 : ℤ) ∈ commonIdeal (1 : ℤ) (2 : ℤ) (3 : ℤ) := by
  simpa using (principal_mem_commonIdeal (d := (1 : ℤ)) (F := (2 : ℤ))
    (G := (3 : ℤ)) (r := (1 : ℤ)))

end SymplecticStaffordTest.CommonColonProducer
