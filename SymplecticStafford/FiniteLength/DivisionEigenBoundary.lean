import SymplecticStafford.FiniteLength.IsotypicBlocks
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Sharp boundary for division-ring pencil finiteness

For a genuinely noncommutative endomorphism division ring, the ordinary
determinant and Mathlib's commutative-ring eigenvector theorem are
unavailable.  The exact replacement needed by the isotypic pencil is an
independent witness family indexed by the bad central scalars.  Finite
generation of the block over its division ring then proves that the bad set
is finite, with no scalarization of the coefficients.

The witness structure records the intended pencil failure set, so this is a
usable contract for a future determinant-free proof: it remains to construct
the witnesses (typically from central eigenvectors), but no finiteness claim
is hidden in a field-only lemma.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section

variable {K : Type u} {E : Type v} {V : Type w}
variable [Field K] [DivisionRing E] [AddCommGroup V] [Module E V]
variable [Module.Finite E V]
variable {ι : Type*}

/-- A determinant-free certificate for a central pencil's bad parameters.

`pencil z` is the block tuple at scalar `z`; `bad_spec` identifies `bad`
with the parameters where that tuple is not independent over `E`.  The
independence of `witness` is the only finiteness input and is meaningful for
arbitrary division rings.
-/
structure CentralPencilBadWitness
    (pencil : K → ι → V) where
  bad : Set K
  witness : bad → V
  bad_spec : ∀ z : K,
    z ∈ bad ↔ ¬ LinearIndependent E (pencil z)
  witness_independent : LinearIndependent E witness

theorem CentralPencilBadWitness.finite
    (pencil : K → ι → V)
    (W : CentralPencilBadWitness (K := K) (E := E) (V := V)
      pencil) :
    W.bad.Finite := by
  haveI : Finite W.bad := W.witness_independent.finite_of_isNoetherian
  exact Set.toFinite W.bad

/-- Convenient specialization when the bad set is already equipped with a
finite independent witness family; this keeps the pencil specification in
the theorem type for comparison audits.
-/
theorem finite_central_pencil_bad_of_independent_witness
    {ι : Type*} (pencil : K → ι → V)
    (bad : Set K) (witness : bad → V)
    (hbad : ∀ z : K,
      z ∈ bad ↔ ¬ LinearIndependent E (pencil z))
    (hindependent : LinearIndependent E witness) :
    bad.Finite := by
  let W : CentralPencilBadWitness (K := K) (E := E) (V := V)
      pencil :=
    { bad := bad
      witness := witness
      bad_spec := by intro z; exact hbad z
      witness_independent := hindependent }
  exact W.finite pencil

end

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.CentralPencilBadWitness.finite
#print axioms
  SymplecticStafford.FiniteLength.finite_central_pencil_bad_of_independent_witness
