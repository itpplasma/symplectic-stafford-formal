import SymplecticStafford.Induction.FiniteScalarAvoidance
import Mathlib.Algebra.Polynomial.Roots

/-!
# Central-field polynomial certificates for support removal

The successor needs two kinds of finite exceptional sets: one for each old
support component and one for each carried local test.  The generic bridge
accepts these sets as propositions.  This file strengthens that interface at
the local-module boundary: a nonzero polynomial over an infinite central
field is enough to produce each finite exceptional set.

The strict-support and carried-test implications remain explicit.  They are
the actual local module input: a polynomial certificate only says where the
implication may fail; it does not prove that a localized module is cyclic or
that a component disappears.
-/

namespace SymplecticStafford.Induction

universe u v w x y

variable {U : Type u} [Semiring U]

section

variable {K : Type v} [Field K]
variable {κ : Type w} [DecidableEq κ]
variable {T : Type x} {V : Type y}

/-- A nonzero central-field polynomial has only finitely many exceptional
parameters.  The displayed set is in evaluation order, matching the pencil
parameter used by the induction interfaces. -/
theorem finite_eval_zero_set {p : Polynomial K} (hp : p ≠ 0) :
    Set.Finite {z : K | p.eval z = 0} := by
  simpa only [Polynomial.IsRoot] using
    (Polynomial.finite_setOfPred_isRoot (R := K) hp)

/-! The full local certificate.  `strict_support_of_good` is the source-
dependent support-removal theorem and `pencil_generation_of_good` is the
carried-test theorem that must come from the actual localized module. -/
structure CentralFieldRemovalRetentionCertificate
    (P : CentralParameters U K)
    (d old new : U) (Ω : List (LocalTest U T V)) where
  support : U → U → List (LocalTest U T V) → Finset κ
  componentPolynomial : κ → Polynomial K
  testPolynomial : LocalTest U T V → Polynomial K
  componentPolynomial_ne_zero : ∀ p,
    p ∈ support d old Ω → componentPolynomial p ≠ 0
  testPolynomial_ne_zero : ∀ t, t ∈ Ω → testPolynomial t ≠ 0
  strict_support_of_good : ∀ z : K,
    (∀ p, p ∈ support d old Ω → (componentPolynomial p).eval z ≠ 0) →
      support d (pencilMember P old new z) Ω ⊂ support d old Ω
  pencil_generation_of_good : ∀ z : K,
    (∀ p, p ∈ support d old Ω → (componentPolynomial p).eval z ≠ 0) →
    (∀ t, t ∈ Ω → (testPolynomial t).eval z ≠ 0) →
    (∀ t, t ∈ Ω → t.generation old → t.generation new →
      t.generation (pencilMember P old new z))

end

section Main

variable {K : Type v} [Field K] [Infinite K]
variable {κ : Type w} [DecidableEq κ]
variable {T : Type x} {V : Type y}

/-- One central scalar simultaneously removes a support component and retains
every carried test, when the local module supplies nonzero polynomial
certificates and the two displayed source-dependent implications. -/
theorem exists_central_field_support_removal_and_retention
    {P : CentralParameters U K}
    {d old new : U} {Ω : List (LocalTest U T V)}
    (c : CentralFieldRemovalRetentionCertificate (K := K)
      (κ := κ) P d old new Ω)
    (baseBad : Set K) (hbase : baseBad.Finite)
    (hold : ∀ t, t ∈ Ω → t.generation old)
    (hnew : ∀ t, t ∈ Ω → t.generation new) :
    ∃ z : K,
      z ∉ baseBad ∧
        c.support d (pencilMember P old new z) Ω ⊂ c.support d old Ω ∧
        (∀ t, t ∈ Ω →
          t.generation (pencilMember P old new z)) := by
  have hcomponent : ∀ p, p ∈ c.support d old Ω →
      Set.Finite {z : K | (c.componentPolynomial p).eval z = 0} := by
    intro p hp
    exact finite_eval_zero_set (c.componentPolynomial_ne_zero p hp)
  have htest : ∀ t, t ∈ Ω →
      Set.Finite {z : K | (c.testPolynomial t).eval z = 0} := by
    intro t ht
    exact finite_eval_zero_set (c.testPolynomial_ne_zero t ht)
  obtain ⟨z, hzbase, hzcomp, hztest⟩ :=
    exists_scalar_avoiding_finset_list
      (c.support d old Ω) Ω
      (fun p z => (c.componentPolynomial p).eval z = 0)
      (fun t z => (c.testPolynomial t).eval z = 0)
      baseBad hcomponent htest hbase
  refine ⟨z, hzbase, c.strict_support_of_good z ?_, ?_⟩
  · intro p hp hzero
    exact hzcomp p hp hzero
  · intro t ht
    apply c.pencil_generation_of_good z ?_ ?_ t ht (hold t ht) (hnew t ht)
    · intro p hp hzero
      exact hzcomp p hp hzero
    · intro t' ht' hzero
      exact hztest t' ht' hzero

end Main

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.finite_eval_zero_set
#print axioms SymplecticStafford.Induction.exists_central_field_support_removal_and_retention
