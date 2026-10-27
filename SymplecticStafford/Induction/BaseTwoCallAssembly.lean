module

public import SymplecticStafford.Induction.TwoCallDescentProducer
public import SymplecticStafford.Induction.ConstructiveSuccessor

@[expose] public section

/-!
# Base-to-endpoint assembly without a hidden base witness

`FiniteIndex` consumes a `StrongPh D 1` witness directly.  This file moves
that boundary back one step: the base is supplied as the pointwise
`BaseProducer`, and is converted to `StrongPh` by its checked constructor
before the raw two-call family is iterated.  The endpoint and terminal
cofactor conclusions are then assembled in original `U`.

No universal base, support-removal theorem, or scalar producer is inferred:
those remain the explicit `BaseProducer`, `TwoCallDescentFamily`, and
zero-extraction hypotheses.
-/

namespace SymplecticStafford.Induction

universe u v w x y

variable {U : Type u} [Semiring U]

section

variable {Λ : Type x} {κ : Type y} [Infinite Λ] [DecidableEq κ]

/-! The base output is constructed from pointwise source/bound/test fields,
then the endpoint is constructed from raw two-call data; neither step accepts
an already-built output witness as an input. -/
noncomputable def strongPh_fin_index_of_base_and_two_call_descent
    {T : Type v} {V : Type w}
    {P : CentralParameters U Λ} {D : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    (base : BaseProducer D defect)
    (family : TwoCallDescentFamily P κ D defect) :
    StrongPh D (D + 1) defect := by
  exact strongPh_fin_index_of_two_call_descent
    (base_producer_strongPh base) family

/-! Terminal extraction is kept explicit and remains a literal original-ring
cofactor statement. -/
noncomputable def terminal_cofactors_of_base_and_two_call_descent
    {T : Type v} {V : Type w}
    {P : CentralParameters U Λ} {D : Nat}
    {defect : U → U → List (LocalTest U T V) → Int}
    (base : BaseProducer D defect)
    (family : TwoCallDescentFamily P κ D defect)
    (zero_extraction : ∀ {d f : U} {Ω : List (LocalTest U T V)},
      defect d f Ω ≤ -1 → OriginalCofactors d f)
    (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U T V))
    (hΩ : AdmissibleTestList d Ω) :
    OriginalCofactors d
      (strongPh_fin_index_of_base_and_two_call_descent base family
        d hd A Ω hΩ).source := by
  exact terminal_cofactors_of_two_call_descent
    (base_producer_strongPh base) family zero_extraction d hd A Ω hΩ

end

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.strongPh_fin_index_of_base_and_two_call_descent
#print axioms SymplecticStafford.Induction.terminal_cofactors_of_base_and_two_call_descent
