module

public import SymplecticStafford.Paper.Setting
public import SymplecticStafford.Paper.RightFraction
public import SymplecticStafford.Paper.Localization
public import SymplecticStafford.Paper.Pencil
public import SymplecticStafford.Paper.DivisionPencil
public import SymplecticStafford.Paper.NoFiniteRank
public import SymplecticStafford.Paper.Test
public import SymplecticStafford.Paper.SourceSelection
public import SymplecticStafford.Paper.Dimension
public import SymplecticStafford.Paper.Induction
public import SymplecticStafford.Paper.Opposite
public import SymplecticStafford.Paper.ConsequencesGeneration
public import SymplecticStafford.Paper.ConsequencesRank
public import SymplecticStafford.Paper.ConsequencesForU

@[expose] public section

/-!
# The formal proof of the Symplectic Stafford theorem

This umbrella module imports the complete Mathlib-only development of the
manuscript: the filtered setting and localization package (§§2–3 with the
Zariskian closure Z1–Z9), finite-length source selection and pencils (§4),
the common colon ideal and the controlled codimension induction (§§5–6),
opposite transport and the module-theoretic consequences (§7).  The main
theorem is `SymplecticStafford.Paper.FilteredAlgebraData.targetA`.
-/
