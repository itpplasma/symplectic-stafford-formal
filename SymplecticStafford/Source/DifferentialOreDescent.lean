module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.NoncommRing
public import SymplecticStafford.Filtered.Localization
public import SymplecticStafford.Semantics.Contract

@[expose] public section

/-!
# Differential--Ore source descent boundary

The paper's differential source-changing argument has two logically distinct
parts.  This file records the concrete hypotheses for the differential chart
(commutative coefficient algebra, filtration lowering, finite powered cover,
and a central parameter field with whole-chart S1), then gives the small
original-ring assembly consumer.  The missing chart-to-global construction is
an explicit `GlobalClearanceBridge` input; it is not inferred from these
hypotheses and no universal source producer is asserted.

Every clearance term below is an identity in the original `U`, with the
ordered factors `d * R + (F * d) * S` unchanged.
-/

namespace SymplecticStafford.Source.DifferentialOre

universe u v w x

variable {U : Type u} [Ring U]
variable {A : Type v} [CommRing A]
variable {S : Type w} [Ring S]
variable {K : Type x} [Field K]

/-- A finite list of coefficient denominators together with exponents. -/
abbrev PoweredCover (A : Type v) := List (A × Nat)

/-- The coefficient sum associated with a powered finite cover. -/
def poweredCoverSum
    (coefficient : A →+* U)
    (cover : PoweredCover A) (weights : List A) : U :=
  (cover.zipWith (fun p a => coefficient (p.1 ^ p.2 * a)) weights).sum

/-- Explicit differential/Ore chart assumptions.

`localized_S1` is the whole-chart central-parameter hypothesis after the
chart has been formed.  `right_power_ore` and `left_power_ore` retain the two
directions of power clearing.  None of these fields states that a global
source exists. -/
structure Hypotheses
    (U : Type u) [Ring U]
    (A : Type v) [CommRing A]
    (S : Type w) [Ring S]
    (K : Type x) [Field K] where
  coefficient : A →+* U
  coefficient_injective : Function.Injective coefficient
  filtration : SymplecticStafford.Filtered.FiltrationData U
  coefficient_degree_zero : ∀ a : A,
    SymplecticStafford.Filtered.HasDegreeAtMost filtration 0 (coefficient a)
  commutator_lowers : ∀ (n : Nat) (P : U) (a : A),
    SymplecticStafford.Filtered.HasDegreeAtMost filtration (n + 1) P →
      SymplecticStafford.Filtered.HasDegreeAtMost filtration n
        (P * coefficient a - coefficient a * P)
  cover : PoweredCover A
  cover_nonzero : ∀ p, p ∈ cover → coefficient p.1 ≠ 0
  cover_unit : ∃ weights : List A,
    weights.length = cover.length ∧ poweredCoverSum coefficient cover weights = 1
  chartMap : U →+* S
  parameterMap : K →+* S
  parameter_central : ∀ z : K, ∀ x : S,
    parameterMap z * x = x * parameterMap z
  localized_S1 : SymplecticStafford.SameDivisorS1 (R := S)
  right_power_ore : ∀ p, p ∈ cover → ∀ x : S,
    ∃ n : Nat, ∃ y : U,
      x * (chartMap (coefficient p.1)) ^ n = chartMap y
  left_power_ore : ∀ p, p ∈ cover → ∀ x : S,
    ∃ n : Nat, ∃ y : U,
      (chartMap (coefficient p.1)) ^ n * x = chartMap y

/-- One finite-cover term after the local differential calculation has been
cleared back to `U`. -/
structure CoverClearanceTerm
    (H : Hypotheses U A S K) (d F : U) where
  denominator : A
  exponent : Nat
  weight : A
  cofactor₁ : U
  cofactor₂ : U
  in_cover : (denominator, exponent) ∈ H.cover
  clearance : H.coefficient
      (denominator ^ exponent * weight) =
    d * cofactor₁ + (F * d) * cofactor₂

/-- A finite list of original-ring clearances whose coefficient terms sum to
one.  This is the precise algebraic output still required from source
selection and chart descent. -/
structure FiniteCoverClearance
    (H : Hypotheses U A S K) (d F : U) where
  terms : List (CoverClearanceTerm H d F)
  unit_identity :
    (terms.map (fun t => H.coefficient
      (t.denominator ^ t.exponent * t.weight))).sum = 1

/-- The exact missing bridge from local chart certificates to one global
original source.  It is deliberately a supplied field, not a theorem of the
differential/Ore assumptions above. -/
structure GlobalClearanceBridge
    (H : Hypotheses U A S K) where
  clearance : ∀ d : U, d ≠ 0 →
    ∃ F : U, Nonempty (FiniteCoverClearance H d F)

theorem finite_cover_clearance_identity
    (H : Hypotheses U A S K) {d F : U}
    (C : FiniteCoverClearance H d F) :
    ∃ R S : U, (1 : U) = d * R + (F * d) * S := by
  have hsum : ∀ xs : List (CoverClearanceTerm H d F),
      (xs.map (fun t => H.coefficient
        (t.denominator ^ t.exponent * t.weight))).sum =
        d * (xs.map CoverClearanceTerm.cofactor₁).sum +
          (F * d) * (xs.map CoverClearanceTerm.cofactor₂).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons t ts ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [t.clearance, ih]
        noncomm_ring
  refine ⟨(C.terms.map CoverClearanceTerm.cofactor₁).sum,
    (C.terms.map CoverClearanceTerm.cofactor₂).sum, ?_⟩
  calc
    (1 : U) = (C.terms.map (fun t => H.coefficient
        (t.denominator ^ t.exponent * t.weight))).sum :=
      C.unit_identity.symm
    _ = d * (C.terms.map CoverClearanceTerm.cofactor₁).sum +
          (F * d) * (C.terms.map CoverClearanceTerm.cofactor₂).sum :=
      hsum C.terms

theorem consume_global_clearance
    (H : Hypotheses U A S K) (B : GlobalClearanceBridge H) :
    SymplecticStafford.OriginalSameDivisor U := by
  intro d hd
  rcases B.clearance d hd with ⟨F, ⟨C⟩⟩
  rcases finite_cover_clearance_identity H C with ⟨R, S, h⟩
  exact ⟨F, R, S, h⟩

end SymplecticStafford.Source.DifferentialOre

#print axioms SymplecticStafford.Source.DifferentialOre.finite_cover_clearance_identity
#print axioms SymplecticStafford.Source.DifferentialOre.consume_global_clearance
