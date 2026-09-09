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

/- A separate defect model shows that the base is not supplied by the
   induction plumbing either.  M01--M08 module and finite-generation facts do
   not mention this defect, so they cannot establish the required `P₁` bound
   without an additional base theorem. -/
def baseFlatDefect : Nat → Nat → List (LocalTest Nat Unit Empty) → Int :=
  fun _ _ _ => 0

theorem base_impossible : StrongPh 0 1 baseFlatDefect → False := by
  intro base
  let A : AffineSource Nat := ⟨0, 1, by decide⟩
  have w := base 1 (by decide) A [] (admissibleTestList_nil 1)
  have hb := w.defect_bound
  norm_num [baseFlatDefect, defectBound] at hb

/- The same countermodel can be stated at the pointwise producer boundary.
   This is the precise M09 obstruction: the `BaseProducer` interface is not
   derivable from the induction plumbing, because its advertised `P₁` bound
   is already inconsistent with the flat defect. -/
theorem no_base_producer_flat : BaseProducer 0 baseFlatDefect → False := by
  intro producer
  exact base_impossible (base_producer_strongPh producer)

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
#print axioms SymplecticStafford.Induction.base_impossible
#print axioms SymplecticStafford.Induction.flat_no_successor_rule
#print axioms SymplecticStafford.Induction.flat_no_constructive_data
