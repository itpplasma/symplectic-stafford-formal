import Mathlib.Tactic
import SymplecticStafford.Induction.CentralFieldSupportRemoval

/-!
# Independent central-field support-removal oracle

This oracle uses `ℚ` as the central field and two concrete support
components.  The component indexed by `0` has exceptional polynomial `X`,
so every scalar selected by the theorem is visibly nonzero; the output
support then drops from `{0,1}` to `{1}`.  The carried test has a genuine
nonzero tail and a concrete generation predicate (`True`), so retention is
checked on an actual list element rather than on an empty list.
-/

namespace SymplecticStafford.Induction.CentralFieldSupportRemovalOracle

open SymplecticStafford.Induction

abbrev K := ℚ
abbrev κ := Fin 2

def parameters : CentralParameters ℚ ℚ where
  embed := id
  central := by intro z x; exact mul_comm _ _

def carriedTest : LocalTest ℚ Unit Unit where
  targetDivisor := 0
  localization := ()
  cyclicModule := ()
  canonicalGenerator := ()
  rightTail := 1
  offset := 0
  localization_spec := True
  localization_spec_proof := True.intro
  finite_length_cyclic_spec := True
  finite_length_cyclic_proof := True.intro
  canonical_generator_spec := True
  canonical_generator_spec_proof := True.intro
  rightTail_nonzero := by norm_num
  generation := fun _ => True

def carried : List (LocalTest ℚ Unit Unit) := [carriedTest]

theorem carried_mem : carriedTest ∈ carried := by simp [carried]

def support (_d f : ℚ) (_xs : List (LocalTest ℚ Unit Unit)) : Finset κ :=
  if f = 0 then {0, 1} else {1}

noncomputable def certificate :
    CentralFieldRemovalRetentionCertificate (κ := κ) parameters 0 0 1 carried where
  support := support
  componentPolynomial := fun p => if p = 0 then Polynomial.X else 1
  testPolynomial := fun _ => 1
  componentPolynomial_ne_zero := by
    intro p hp
    split <;> simp
  testPolynomial_ne_zero := by
    intro t ht
    simp
  strict_support_of_good := by
    intro z hgood
    have hzero : (Polynomial.X : Polynomial ℚ).eval z ≠ 0 := by
      exact hgood 0 (by simp [support])
    have hz : z ≠ 0 := by simpa using hzero
    simp [support, pencilMember, parameters, hz]
    decide
  pencil_generation_of_good := by
    intro z hcomponent htests t ht hF hG
    have ht' : t = carriedTest := by simpa [carried] using ht
    subst t
    change True
    trivial

noncomputable example :
    ∃ z : ℚ, z ∉ (∅ : Set ℚ) ∧
      support 0 (pencilMember parameters 0 1 z) carried ⊂ support 0 0 carried ∧
      (∀ t, t ∈ carried → t.generation (pencilMember parameters 0 1 z)) := by
  simpa [certificate, support, pencilMember, parameters] using
    (exists_central_field_support_removal_and_retention
      (c := certificate) (baseBad := (∅ : Set ℚ)) Set.finite_empty
      (by intro t ht; have ht' : t = carriedTest := by simpa [carried] using ht
          subst t; change True; trivial)
      (by intro t ht; have ht' : t = carriedTest := by simpa [carried] using ht
          subst t; change True; trivial))

example :
    Set.Finite {z : ℚ | (Polynomial.X : Polynomial ℚ).eval z = 0} := by
  exact finite_eval_zero_set (by simp)

example : carriedTest.generation 0 := by change True; trivial

end SymplecticStafford.Induction.CentralFieldSupportRemovalOracle

#print axioms SymplecticStafford.Induction.CentralFieldSupportRemovalOracle.certificate
#print axioms SymplecticStafford.Induction.exists_central_field_support_removal_and_retention
