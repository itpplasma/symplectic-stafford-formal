import SymplecticStafford.Paper.Setting
import SymplecticStafford.Paper.RightFraction
import SymplecticStafford.Paper.Localization
import SymplecticStafford.Paper.Pencil
import SymplecticStafford.Paper.DivisionPencil
import SymplecticStafford.Paper.NoFiniteRank
import SymplecticStafford.Paper.Test
import SymplecticStafford.Paper.SourceSelection
import SymplecticStafford.Paper.Dimension
import SymplecticStafford.Paper.Induction
import SymplecticStafford.Paper.Opposite
import SymplecticStafford.Paper.ConsequencesGeneration
import SymplecticStafford.Paper.ConsequencesRank
import SymplecticStafford.Paper.ConsequencesForU

/-!
# The formal proof of the Symplectic Stafford theorem

This umbrella module imports the complete Mathlib-only development of the
manuscript: the filtered setting and localization package (§§2–3 with the
Zariskian closure Z1–Z9), finite-length source selection and pencils (§4),
the common colon ideal and the controlled codimension induction (§§5–6),
opposite transport and the module-theoretic consequences (§7).  The main
theorem is `SymplecticStafford.Paper.FilteredAlgebraData.targetA`.
-/
