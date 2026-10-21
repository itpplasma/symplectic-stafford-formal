module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.NoncommRing
public import SymplecticStafford.Ordered.CommonColon

@[expose] public section

/-!
# The ordered common-colon producer

This file isolates the algebraic part of the all-dimensional common-colon
argument.  It does not identify a characteristic support or prove that a
localization exists.  Instead, it consumes an injective ambient algebra map,
two local affine certificates, and simultaneous right-clearance of exactly
the three coefficients occurring in the ordered pencil.  The output is a
literal element of the original `commonIdeal`, together with the original-U
common-colon equation.

The coefficient equation is obtained by evaluating the central pencil at
`0` and `1`.  This is algebraically equivalent to comparing coefficients in a
central polynomial parameter, while avoiding any commutative-coefficient
encoding of a noncommutative polynomial ring.
-/

namespace SymplecticStafford.Ordered

universe u v

section Pencil

variable {R : Type u} [Ring R]

/- The three coefficients in the ordered identity from the paper.  The
   parentheses are intentional: no factor is commuted. -/
def producerA0 (a C z G d b : R) : R :=
  a + C * z * (G * d) * b

def producerA1 (c G d b : R) : R :=
  -c * (G * d) * b

def producerS0 (b L z G d : R) : R :=
  b - L * z * (G * d) * b

theorem producer_ordered_pencil_identity
    (d F G L C a b c z t : R)
    (hdiv : F * d * L = d * C)
    (hold : (1 : R) = d * a + F * d * b)
    (hnew : (1 : R) = d * c + G * d * L * z)
    (hcentral : ∀ x : R, t * x = x * t) :
    (1 : R) =
      d * (producerA0 a C z G d b + t * producerA1 c G d b) +
        (F + t * G) * d * producerS0 b L z G d := by
  unfold producerA0 producerA1 producerS0
  have hdiv' : d * C * z * (G * d) * b =
      F * d * L * z * (G * d) * b := by
    rw [hdiv]
  have hnew' : (d * c + G * d * L * z) * (G * d) * b =
      (G * d) * b := by
    rw [← hnew]
    simp
  calc
    (1 : R) = d * a + F * d * b := hold
    _ = d * a + F * d * b +
          (d * C * z * (G * d) * b - F * d * L * z * (G * d) * b) +
          t * ((G * d) * b -
            (d * c + G * d * L * z) * (G * d) * b) := by
      rw [hdiv', hnew']
      simp
    _ = d * (a + C * z * (G * d) * b +
        t * (-c * (G * d) * b)) +
        (F + t * G) * d * (b - L * z * (G * d) * b) := by
      have htd : d * t = t * d := (hcentral d).symm
      have htd' : ∀ x : R, d * (t * x) = t * (d * x) := by
        intro x
        rw [← mul_assoc, htd, mul_assoc]
      simp only [mul_add, add_mul]
      rw [htd']
      noncomm_ring

theorem producer_zero_identity
    (d F G L C a b c z : R)
    (hdiv : F * d * L = d * C)
    (hold : (1 : R) = d * a + F * d * b)
    (hnew : (1 : R) = d * c + G * d * L * z) :
    (1 : R) = d * producerA0 a C z G d b + F * d * producerS0 b L z G d := by
  simpa using producer_ordered_pencil_identity d F G L C a b c z 0
    hdiv hold hnew (by intro x; simp)

theorem producer_one_minus_zero_coefficient
    (d F G L C a b c z : R)
    (hdiv : F * d * L = d * C)
    (hold : (1 : R) = d * a + F * d * b)
    (hnew : (1 : R) = d * c + G * d * L * z) :
    G * d * producerS0 b L z G d =
      d * (-producerA1 c G d b) := by
  have hzero := producer_zero_identity d F G L C a b c z hdiv hold hnew
  have hone := producer_ordered_pencil_identity d F G L C a b c z 1
    hdiv hold hnew (by intro x; simp)
  have hone' :
      (1 : R) = d * (a + C * z * (G * d) * b + -c * (G * d) * b) +
        (F + G) * d * (b - L * z * (G * d) * b) := by
    simpa [producerA0, producerA1, producerS0] using hone
  dsimp [producerA0, producerA1, producerS0] at hzero hone ⊢
  calc
    G * d * (b - L * z * (G * d) * b) =
        (d * (a + C * z * (G * d) * b + -c * (G * d) * b) +
          (F + G) * d * (b - L * z * (G * d) * b)) -
        (d * (a + C * z * (G * d) * b) +
          F * d * (b - L * z * (G * d) * b)) -
        d * (-c * (G * d) * b) := by
      noncomm_ring
    _ = (1 : R) - 1 - d * (-c * (G * d) * b) := by
      rw [hone'.symm, hzero.symm]
    _ = d * (-(-c * (G * d) * b)) := by
      noncomm_ring

end Pencil

section AmbientProducer

variable {R : Type u} [Ring R]
variable {S : Type v} [Ring S]

/- A local affine certificate and three simultaneous right-clearances.  The
   lifts `A0s`, `A1s`, and `S0s` are elements of the original ring; the
   equations are in the ambient ring and therefore expose the exact
   injectivity needed to return to original U. -/
structure AmbientProducerData (ι : R →+* S)
    (d F G L C : R) where
  localA : S
  localB : S
  localC : S
  localZ : S
  denominator : R
  A0s : R
  A1s : R
  S0s : R
  hdiv : F * d * L = d * C
  hold : (1 : S) = ι d * localA + ι F * ι d * localB
  hnew : (1 : S) = ι d * localC + ι G * ι d * ι L * localZ
  clear_A0 :
    (localA + ι C * localZ * (ι G * ι d) * localB) * ι denominator = ι A0s
  clear_A1 :
    (-localC * (ι G * ι d) * localB) * ι denominator = ι A1s
  clear_S0 :
    (localB - ι L * localZ * (ι G * ι d) * localB) * ι denominator = ι S0s

theorem ambient_producer_returns_original_commonIdeal
    (ι : R →+* S) (hι : Function.Injective ι)
    (d F G L C : R)
    (H : AmbientProducerData ι d F G L C) :
    H.denominator ∈ commonIdeal d F G ∧
      G * d * H.S0s = d * (-H.A1s) := by
  let dS : S := ι d
  let FS : S := ι F
  let GS : S := ι G
  let LS : S := ι L
  let CS : S := ι C
  have hdivS : FS * dS * LS = dS * CS := by
    dsimp [FS, dS, LS, CS]
    simpa only [map_mul] using congrArg ι H.hdiv
  have hzero := producer_zero_identity dS FS GS LS CS H.localA H.localB H.localC H.localZ
    hdivS H.hold H.hnew
  have hone := producer_ordered_pencil_identity dS FS GS LS CS H.localA H.localB H.localC H.localZ 1
    hdivS H.hold H.hnew (by intro x; simp)
  have hzero_clear := congrArg (fun x : S => x * ι H.denominator) hzero
  have hone_clear := congrArg (fun x : S => x * ι H.denominator) hone
  have hA0 :
      ι H.denominator = ι d * ι H.A0s + ι F * ι d * ι H.S0s := by
    simp only [producerA0, producerS0] at hzero_clear
    calc
      ι H.denominator =
          dS * ((H.localA + CS * H.localZ * (GS * dS) * H.localB) *
            ι H.denominator) +
            FS * dS * ((H.localB - LS * H.localZ * (GS * dS) * H.localB) *
              ι H.denominator) := by
        simpa only [one_mul, add_mul, mul_assoc] using hzero_clear
      _ = dS * ι H.A0s + FS * dS * ι H.S0s := by
        rw [H.clear_A0, H.clear_S0]
      _ = ι d * ι H.A0s + ι F * ι d * ι H.S0s := by
        rfl
  have hA1 :
      ι G * ι d * ι H.S0s = ι d * (-ι H.A1s) := by
    have hcoeff := producer_one_minus_zero_coefficient dS FS GS LS CS
      H.localA H.localB H.localC H.localZ hdivS H.hold H.hnew
    have hcoeff_clear := congrArg (fun x : S => x * ι H.denominator) hcoeff
    simp only [producerS0, producerA1] at hcoeff_clear
    have hcoeff_clear' :
        GS * dS *
            ((H.localB - LS * H.localZ * (GS * dS) * H.localB) *
              ι H.denominator) =
          dS * (-((-H.localC * (GS * dS) * H.localB) *
            ι H.denominator)) := by
      convert hcoeff_clear using 1 <;> noncomm_ring
    calc
      ι G * ι d * ι H.S0s =
          GS * dS *
            ((H.localB - LS * H.localZ * (GS * dS) * H.localB) *
              ι H.denominator) := by
        rw [H.clear_S0]
      _ = dS * (-((-H.localC * (GS * dS) * H.localB) *
            ι H.denominator)) := hcoeff_clear'
      _ = dS * (-ι H.A1s) := by rw [H.clear_A1]
      _ = ι d * (-ι H.A1s) := by rfl
  have hden :
      H.denominator = d * H.A0s + (F * d) * H.S0s := by
    apply hι
    simpa [map_add, map_mul] using hA0
  have hcolon : G * d * H.S0s = d * (-H.A1s) := by
    apply hι
    simpa [map_mul] using hA1
  constructor
  · refine ⟨H.A0s, H.S0s, ?_, hden⟩
    exact ⟨-H.A1s, hcolon⟩
  · exact hcolon

end AmbientProducer

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.producer_ordered_pencil_identity
#print axioms SymplecticStafford.Ordered.producer_one_minus_zero_coefficient
#print axioms SymplecticStafford.Ordered.ambient_producer_returns_original_commonIdeal
