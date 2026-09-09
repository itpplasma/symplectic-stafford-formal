import Mathlib.Tactic.NoncommRing
import SymplecticStafford.Source.DifferentialOreDescent

/-!
# Bounded algebraization of a formal quantum slice

Formal or microlocal slice data lives in a completion (or another chart ring)
and therefore does not, by itself, give an element of the original algebra.
This file isolates the exact finite interface that is sufficient.  A formal
certificate has finitely many terms, a common formal unit identity, and each
of its finitely many right coefficients is explicitly the image of a bounded
element of the original `U`.  Injectivity of the chart and completion maps
then reflects the formal identity to `U`; the existing differential/Ore
consumer assembles the finite cover and proves `OriginalSameDivisor`.

The bounded lifts and their source-dependent finite list are hypotheses.  No
completion, formal specialization, torus-finiteness, or microlocal theorem is
silently treated as such a lift.  In particular, this is a target theorem for
the missing quantum algebraization step, not a universal producer.
-/

namespace SymplecticStafford.Source.QuantizedSlice

universe u v w x y

open SymplecticStafford.Source.DifferentialOre

variable {U : Type u} [Ring U]
variable {A : Type v} [CommRing A]
variable {S : Type w} [Ring S]
variable {K : Type x} [Field K]
variable {Q : Type y} [Ring Q]

/- The completion/chart maps are deliberately separate: a formal slice need
not be the localization ring used by the differential consumer. -/
structure ChartData (H : Hypotheses U A S K) (Q : Type y) [Ring Q] where
  completionMap : S →+* Q
  completion_injective : Function.Injective completionMap
  chart_injective : Function.Injective H.chartMap

namespace ChartData

variable {H : Hypotheses U A S K}

def coefficientValue (H : Hypotheses U A S K) (a : A) (n : Nat) (b : A) : U :=
  H.coefficient (a ^ n * b)

private theorem map_list_sum_comp (φ : U →+* S) (ψ : S →+* Q)
    (xs : List U) :
    ψ (φ xs.sum) = (xs.map (fun x => ψ (φ x))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/- One formal affine clearance term.  `right₁_lift` and `right₂_lift` are the
finite algebraization certificate: the formal cofactors are not merely
rational or completed elements, but images of actual bounded elements of U. -/
structure Term (C : ChartData H Q) (d F : U) where
  denominator : A
  exponent : Nat
  weight : A
  in_cover : (denominator, exponent) ∈ H.cover
  bound : Nat
  formal₁ : Q
  formal₂ : Q
  formal_identity :
    C.completionMap (H.chartMap
        (coefficientValue H denominator exponent weight)) =
      C.completionMap (H.chartMap d) * formal₁ +
        (C.completionMap (H.chartMap F) * C.completionMap (H.chartMap d)) *
          formal₂
  right₁ : U
  right₂ : U
  right₁_bounded : SymplecticStafford.Filtered.HasDegreeAtMost
    H.filtration bound right₁
  right₂_bounded : SymplecticStafford.Filtered.HasDegreeAtMost
    H.filtration bound right₂
  right₁_lift : formal₁ = C.completionMap (H.chartMap right₁)
  right₂_lift : formal₂ = C.completionMap (H.chartMap right₂)

/- A finite formal certificate may depend on d and its source F.  The
unit identity is kept in Q, where the slice calculation takes place. -/
structure Clearance (C : ChartData H Q) (d F : U) where
  terms : List (Term C d F)
  formal_unit_identity :
    (terms.map (fun t => C.completionMap (H.chartMap
      (coefficientValue H t.denominator t.exponent t.weight)))).sum = 1

private theorem finite_bound (C : ChartData H Q) (xs : List (Term C d F)) :
    ∃ N : Nat, ∀ t ∈ xs, t.bound ≤ N := by
  induction xs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons t ts ih =>
      rcases ih with ⟨N, hN⟩
      refine ⟨max t.bound N, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact le_trans (hN x hx) (Nat.le_max_right _ _)

theorem common_bound (C : ChartData H Q)
    (P : Clearance C d F) :
    ∃ N : Nat, ∀ t ∈ P.terms,
      t.bound ≤ N ∧
        SymplecticStafford.Filtered.HasDegreeAtMost H.filtration N t.right₁ ∧
        SymplecticStafford.Filtered.HasDegreeAtMost H.filtration N t.right₂ := by
  rcases finite_bound C P.terms with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  exact ⟨hN t ht,
    H.filtration.monotone (hN t ht) t.right₁_bounded,
    H.filtration.monotone (hN t ht) t.right₂_bounded⟩

private theorem term_clearance (C : ChartData H Q)
    (t : Term C d F) :
    coefficientValue H t.denominator t.exponent t.weight =
      d * t.right₁ + (F * d) * t.right₂ := by
  apply C.chart_injective
  apply C.completion_injective
  calc
    C.completionMap (H.chartMap
        (coefficientValue H t.denominator t.exponent t.weight)) =
        C.completionMap (H.chartMap d) * t.formal₁ +
          (C.completionMap (H.chartMap F) * C.completionMap (H.chartMap d)) *
            t.formal₂ := t.formal_identity
    _ = C.completionMap (H.chartMap d) *
          C.completionMap (H.chartMap t.right₁) +
          (C.completionMap (H.chartMap F) * C.completionMap (H.chartMap d)) *
            C.completionMap (H.chartMap t.right₂) := by
          rw [t.right₁_lift, t.right₂_lift]
    _ = C.completionMap (H.chartMap
          (d * t.right₁ + (F * d) * t.right₂)) := by
          simp only [map_add, map_mul]

def toCoverTerm (C : ChartData H Q) (t : Term C d F) :
    CoverClearanceTerm H d F where
  denominator := t.denominator
  exponent := t.exponent
  weight := t.weight
  cofactor₁ := t.right₁
  cofactor₂ := t.right₂
  in_cover := t.in_cover
  clearance := term_clearance C t

theorem to_original_clearance (C : ChartData H Q)
    (P : Clearance C d F) :
    Nonempty (FiniteCoverClearance H d F) := by
  refine ⟨⟨P.terms.map (toCoverTerm C), ?_⟩⟩
  have hunit :
      (P.terms.map (fun t => coefficientValue H t.denominator
        t.exponent t.weight)).sum = 1 := by
    apply C.chart_injective
    apply C.completion_injective
    calc
      C.completionMap (H.chartMap
          ((P.terms.map (fun t => coefficientValue H t.denominator
            t.exponent t.weight)).sum)) =
          (P.terms.map (fun t => C.completionMap (H.chartMap
            (coefficientValue H t.denominator t.exponent t.weight)))).sum := by
              rw [map_list_sum_comp]
              rw [List.map_map]
              rfl
      _ = 1 := P.formal_unit_identity
      _ = C.completionMap (H.chartMap (1 : U)) := by simp
  rw [List.map_map]
  exact hunit

/- The exact missing bridge: for every nonzero divisor the formal slice must
provide one finite certificate and bounded original lifts for all its formal
cofactors. -/
structure GlobalBridge (H : Hypotheses U A S K) (Q : Type y) [Ring Q]
    extends ChartData H Q where
  clearance : ∀ d : U, d ≠ 0 →
    ∃ F : U, Nonempty (Clearance toChartData d F)

theorem GlobalBridge.to_clearance_bridge
    (B : GlobalBridge H Q) : GlobalClearanceBridge H where
  clearance := by
    intro d hd
    rcases B.clearance d hd with ⟨F, ⟨P⟩⟩
    exact ⟨F, to_original_clearance B.toChartData P⟩

theorem GlobalBridge.consume
    (B : GlobalBridge H Q) :
    SymplecticStafford.OriginalSameDivisor (R := U) :=
  consume_global_clearance H B.to_clearance_bridge

end ChartData

end SymplecticStafford.Source.QuantizedSlice

#print axioms
  SymplecticStafford.Source.QuantizedSlice.ChartData.to_original_clearance
#print axioms
  SymplecticStafford.Source.QuantizedSlice.ChartData.GlobalBridge.consume
