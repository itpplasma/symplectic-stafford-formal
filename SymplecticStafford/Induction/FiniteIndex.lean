module

public import SymplecticStafford.Induction.StrongPh

@[expose] public section

/-!
# Finite-index induction for the strong `P_h` contract

This module supplies only the generic finite-index logic behind the M09--M10
interface.  A caller must provide `P₁` and, at every index, a successor rule
whose `SuccessorCertificate.output` is the next `P_h` witness.  Consequently
the theorem below does not construct the paper's local tests, source, or
successor certificate; it merely composes supplied certificates by ordinary
natural-number induction.

The final original-ring step is likewise an explicit
`TerminationInterface`.  Keeping it as an argument makes the boundary
visible: the result is a conditional terminal-cofactor theorem, not the
universal producer or a Phase-I/Phase-II completion claim.
-/

namespace SymplecticStafford.Induction

universe u v w x y

variable {U : Type u} [Semiring U]

/-! The family of exact two-call successor rules used by finite induction. -/
def SuccessorFamily
    {T : Type v} {V : Type w}
    {Λ : Type x} (P : CentralParameters U Λ)
    (κ : Type y)
    (D : Nat)
    (defect : U → U → List (LocalTest U T V) → Int) : Type _ :=
  ∀ h : Nat, ∀ (lower : StrongPh D h defect),
    SuccessorRule P κ D h defect lower

/-!
Given `P₁` and a successor rule at every index, derive the endpoint
`P_(D+1)`.  The `D = 0` case is intentionally included: the supplied base is
already the requested endpoint there. -/
def strongPh_fin_index
    {T : Type v} {V : Type w}
    {Λ : Type x} (P : CentralParameters U Λ)
    (κ : Type y)
    (D : Nat)
    (defect : U → U → List (LocalTest U T V) → Int)
    (base : StrongPh D 1 defect)
    (successors : SuccessorFamily P κ D defect) :
    StrongPh D (D + 1) defect := by
  let rec climb (n : Nat) : StrongPh D (1 + n) defect :=
    match n with
    | 0 => base
    | n + 1 => strongPh_succ P κ (successors (1 + n) (climb n))
  exact cast (congrArg (fun h : Nat => StrongPh D h defect) (Nat.add_comm 1 D))
    (climb D)

/-! The endpoint proof and its terminal original-ring bridge in one call.

`zero_extraction` and the endpoint arithmetic equality are deliberately
explicit.  Together they are the only supplied bridge from the defect bound
`≤ -1` to literal cofactors in the original ring.  Making the arithmetic
equality an input keeps this generic composition theorem independent of the
particular integer-normalization lemma used by a client.
-/
def terminal_cofactors_fin_index
    {T : Type v} {V : Type w}
    {Λ : Type x} (P : CentralParameters U Λ)
    (κ : Type y)
    (D : Nat)
    (defect : U → U → List (LocalTest U T V) → Int)
    (base : StrongPh D 1 defect)
    (successors : SuccessorFamily P κ D defect)
    (zero_extraction : ∀ {d f : U} {Ω : List (LocalTest U T V)},
      defect d f Ω ≤ -1 → OriginalCofactors d f)
    (endpoint_bound : defectBound D (D + 1) = -1)
    (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U T V))
    (hΩ : AdmissibleTestList d Ω) :
    OriginalCofactors d
      (strongPh_fin_index P κ D defect base successors d hd A Ω hΩ).source := by
  apply zero_extraction
  rw [← endpoint_bound]
  exact (strongPh_fin_index P κ D defect base successors d hd A Ω hΩ).defect_bound

/-! A named endpoint package keeps the output witness available to callers.
This is useful to an oracle because it can inspect the affine-source and
retention fields before applying `terminal_cofactors_fin_index`. -/
structure FiniteIndexEndpoint
    {T : Type v} {V : Type w}
    (D : Nat)
    (defect : U → U → List (LocalTest U T V) → Int) where
  witness : StrongPh D (D + 1) defect

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.strongPh_fin_index
#print axioms SymplecticStafford.Induction.terminal_cofactors_fin_index
