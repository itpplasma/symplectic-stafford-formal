import SymplecticStafford.Induction.ConstructiveSuccessor

/-!
# A sharp obstruction to deriving the successor from the lower contract

This model isolates what remains genuinely mathematical in M10.  The lower
`StrongPh` contract can hold at its stated integer bound while the next bound
is impossible for every source.  Consequently no successor can be constructed
from lower-call plumbing and finite-test retention alone: a producer must
prove an actual defect-decrease/support-removal statement.
-/

namespace SymplecticStafford.Induction

universe u v w

variable {U : Type u} [Semiring U]

/-- A defect with no room for one more induction step. -/
def flatDefect : Nat → Nat → List (LocalTest Nat Unit Empty) → Int :=
  fun _ _ _ => -1

/-- The flat model satisfies the lower index `P₁` over `Nat`.  Empty cyclic
modules make all finite-test obligations explicit and vacuous; the source is
still constructed pointwise as `A.B + 0*A.a`. -/
def flatLower : StrongPh 0 1 flatDefect := by
  intro d hd A Ω hΩ
  refine {
    H := 0
    source := A.B
    source_eq := by simp
    defect_bound := by norm_num [flatDefect, defectBound]
    tests_pass := ?_ }
  intro t ht
  exact nomatch t.cyclicModule

/-- The next index is impossible in the same model, independently of any
choice of source. -/
theorem flat_next_impossible : StrongPh 0 2 flatDefect → False := by
  intro next
  let A : AffineSource Nat := ⟨0, 1, by decide⟩
  have w := next 1 (by decide) A [] (admissibleTestList_nil 1)
  have hb := w.defect_bound
  norm_num [flatDefect, defectBound] at hb

/-- Therefore a `SuccessorRule` cannot be obtained merely from this lower
contract, even after choosing arbitrary central parameters and component
labels. -/
theorem flat_no_successor_rule
    {Λ : Type u} (P : CentralParameters Nat Λ) (κ : Type v) :
    SuccessorRule P κ 0 1 flatDefect flatLower → False := by
  intro rule
  exact flat_next_impossible (strongPh_succ P κ rule)

/-- The same contradiction reaches the constructive boundary directly: an
explicit source/arithmetic certificate would already contain the missing
one-step defect decrease. -/
theorem flat_no_constructive_data
    {Λ : Type u} (P : CentralParameters Nat Λ) (κ : Type v)
    (A : AffineSource Nat) (Ω : List (LocalTest Nat Unit Empty))
    (hΩ : AdmissibleTestList 1 Ω)
    (c : SuccessorConstruction P κ 0 1 flatDefect flatLower
      1 (by decide) A Ω hΩ) : False := by
  have hb := c.output_bound
  rw [c.output_defect_eq, flatDefect] at hb
  norm_num [defectBound] at hb

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.flat_next_impossible
#print axioms SymplecticStafford.Induction.flat_no_successor_rule
#print axioms SymplecticStafford.Induction.flat_no_constructive_data
