module

public import SymplecticStafford.Induction.TestRetentionObstruction

@[expose] public section

/-!
# Independent oracle for the source-dependent retention boundary

The oracle checks that both lower calls pass the carried test but the affine
pencil source does not.  It is intentionally independent of any producer or
support construction.
-/

namespace SymplecticStafford.Induction.TestRetentionObstructionOracle

open SymplecticStafford.Induction

example :
    ∀ t, t ∈ retentionBoundary.carried →
      retentionBoundaryPass t 0 ∧
        retentionBoundaryPass t 1 := by
  exact retention_boundary_lower_passes

example :
    ¬ (∀ t, t ∈ retentionBoundary.carried →
      retentionBoundaryPass t
        (pencilMember retentionBoundaryParameters
          0 1 ())) := by
  exact retention_boundary_pencil_fails

example :
    (∀ t, t ∈ retentionBoundary.carried →
      retentionBoundaryPass t 0 ∧
        retentionBoundaryPass t 1) ∧
      ¬ (∀ t, t ∈ retentionBoundary.carried →
        retentionBoundaryPass t
          (pencilMember retentionBoundaryParameters
            0 1 ())) := by
  exact lower_passes_do_not_supply_pencil_retention

end SymplecticStafford.Induction.TestRetentionObstructionOracle
