import SymplecticStafford.Filtered.ReesModuleNoetherianBoundary

/- Independent oracle for the sequence-ring obstruction. -/
namespace SymplecticStaffordTest.ReesModuleNoetherianBoundary

open SymplecticStafford.Filtered

example (n : ℕ) :
    (constantNegFiltration.carrier n : Set SequenceRing) = Set.univ := by
  exact constantNegFiltration_carrier n

example : sequenceCoordinate 2 ∈ sequencePrefixIdeal 3 := by
  exact sequenceCoordinate_mem_succ 2

example :
    (sequencePrefixIdeal 2 : Submodule SequenceRing SequenceRing) ≠
      (sequencePrefixIdeal 3 : Submodule SequenceRing SequenceRing) := by
  exact sequencePrefixIdeal_strict 2

example : ¬ IsNoetherianRing SequenceRing :=
  sequenceRing_not_noetherian

example :
    ¬ Nonempty (ReesModuleNoetherianCertificate SequenceRing SequenceRing) :=
  no_sequence_module_noetherian_certificate

example :
    ¬ (SymplecticStafford.AdmissibleSymplecticClass SequenceRing →
      Nonempty (ReesModuleNoetherianCertificate SequenceRing SequenceRing)) :=
  no_certificate_from_historical_class_labels

example :
    SymplecticStafford.AdmissibleSymplecticClass SequenceRing :=
  historicalClassOnSequenceRing

end SymplecticStaffordTest.ReesModuleNoetherianBoundary
