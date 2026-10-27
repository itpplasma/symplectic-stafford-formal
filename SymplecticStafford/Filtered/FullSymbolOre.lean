module

public import SymplecticStafford.Filtered.FinitePowerOre

@[expose] public section

/-!
# Full-symbol algebraic localization boundary

This file names the exact extra data which a genuine full-symbol argument
must provide before the finite power-Ore API can be used.  In particular, a
symbol is represented by an element of the *algebraic* Rees quotient and is
lifted to the original ring.  The chart map is required to be injective, and
the chart-wide inverse and right-Ore witnesses remain explicit.

The structure is intentionally a boundary, not a construction from a
principal open or a completed quantum chart.  The final theorems give the
exact quotient-to-chart passage available from these hypotheses: the power
fraction object maps bijectively to the specified chart, and finite symbol
families have a common original-ring denominator power.  No Noetherianity,
faithful good-filtration theorem, or completion specialization is inferred.
-/

namespace SymplecticStafford.Filtered

universe u v

variable {R : Type u} [Semiring R]
variable {S : Type v} [Semiring S]

namespace FullSymbolOreCertificate

/-! A full-symbol witness for one algebraic chart. -/
structure Data (R : Type u) (S : Type v)
    [Semiring R] [Semiring S] where
  localization : PowerOreLocalizationCertificate R S
  /-- The chosen homogeneous-symbol lift in the actual algebraic Rees object. -/
  symbolLift : ReesTerm localization.sourceFiltration
  symbolLift_value : symbolLift.value = localization.denominator
  /-- The chosen symbol is not the zero Rees class. -/
  symbolLift_nonzero :
    ReesQuotient.mk symbolLift ≠ ReesQuotient.zero
  /-- Equality of chart elements can be reflected to the original ring. -/
  map_injective : Function.Injective localization.map

variable (C : Data R S)

theorem symbolLift_value_mem :
    C.localization.denominator ∈
      C.localization.sourceFiltration.carrier C.symbolLift.degree := by
  rw [← C.symbolLift_value]
  exact C.symbolLift.bounded

theorem symbolLift_class_value :
    ReesQuotient.value (ReesQuotient.mk C.symbolLift) =
      C.localization.denominator := by
  rw [ReesQuotient.value_mk]
  exact C.symbolLift_value

theorem symbolLift_class_nonzero :
    ReesQuotient.mk C.symbolLift ≠ ReesQuotient.zero :=
  C.symbolLift_nonzero

/-- The algebraic power-fraction map attached to the full-symbol witness. -/
def fractionEval : PowerOreLocalizationCertificate.PowerFraction
    C.localization → S :=
  C.localization.fractionEval

theorem fractionEval_surjective : Function.Surjective (fractionEval C) :=
  PowerOreLocalizationCertificate.fractionEval_surjective C.localization

theorem fractionEval_injective : Function.Injective (fractionEval C) := by
  intro p q hpq
  induction p using Quotient.inductionOn with
  | _ p =>
    induction q using Quotient.inductionOn with
    | _ q =>
      change C.localization.map p.1 * C.localization.inverse ^ p.2 =
        C.localization.map q.1 * C.localization.inverse ^ q.2 at hpq
      have hrel := (PowerOreLocalizationCertificate.fractionEval_eq_iff_fractionRel
        C.localization C.map_injective (p := p) (q := q)).1 hpq
      exact Quotient.sound hrel

theorem fractionEval_bijective : Function.Bijective (fractionEval C) :=
  ⟨fractionEval_injective C, fractionEval_surjective C⟩

/-- Every chart element has a unique algebraic power-fraction class.

The representative itself is in the quotient of original-ring pairs; no
formal or completed element is introduced by this passage.
-/
theorem exists_unique_fraction (x : S) :
    ∃! q : PowerOreLocalizationCertificate.PowerFraction C.localization,
      fractionEval C q = x := by
  rcases fractionEval_surjective C x with ⟨q, hq⟩
  refine ⟨q, hq, ?_⟩
  intro r hr
  exact fractionEval_injective C (hr.trans hq.symm)

/-- Exact equality of algebraic chart fractions is the original-U relation. -/
theorem fractionEval_eq_iff_fractionRel
    {p q : R × Nat} :
    fractionEval C (C.localization.fractionMk p.1 p.2) =
        fractionEval C (C.localization.fractionMk q.1 q.2) ↔
      C.localization.fractionRel p q := by
  change C.localization.map p.1 * C.localization.inverse ^ p.2 =
      C.localization.map q.1 * C.localization.inverse ^ q.2 ↔ _
  exact PowerOreLocalizationCertificate.fractionEval_eq_iff_fractionRel
    C.localization C.map_injective
      (p := p) (q := q)

/-- A finite family of algebraic Rees symbols has one common right power. -/
theorem finite_symbol_common_fraction_power
    (xs : List (ReesTerm C.localization.sourceFiltration)) :
    ∃ n : Nat, ∀ x ∈ xs, ∃ a : R,
      C.localization.map x.value =
        C.localization.map a * C.localization.inverse ^ n := by
  rcases C.localization.finite_fraction_normal_form
      (xs.map (fun x => C.localization.map x.value)) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro x hx
  have hmem : C.localization.map x.value ∈
      xs.map (fun y => C.localization.map y.value) := by
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  exact hn _ hmem

end FullSymbolOreCertificate

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FullSymbolOreCertificate.fractionEval_bijective
#print axioms SymplecticStafford.Filtered.FullSymbolOreCertificate.exists_unique_fraction
#print axioms SymplecticStafford.Filtered.FullSymbolOreCertificate.finite_symbol_common_fraction_power
