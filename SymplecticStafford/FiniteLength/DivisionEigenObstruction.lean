module

public import SymplecticStafford.FiniteLength.DivisionEigenBoundary

@[expose] public section

/-!
# Minimal obstruction to an unconditional pencil-finiteness lemma

Finite generation over a division ring only bounds an *independent* family.
It cannot by itself make the bad parameters of an arbitrary pencil finite:
the zero pencil is bad at every scalar.  This theorem is the checked boundary
that prevents the isotypic contract from silently becoming a universal
noncommutative pencil theorem.
-/

namespace SymplecticStafford.FiniteLength

universe u v

section

variable {K : Type u} {E : Type v} {V : Type*}
variable [Field K] [DivisionRing E] [AddCommGroup V] [Module E V]
variable [Infinite K]

theorem zero_pencil_bad_set_not_finite :
    ¬ ({z : K | ¬ LinearIndependent E (fun _ : Unit => (0 : V))}).Finite := by
  have hzero : ¬ LinearIndependent E (fun _ : Unit => (0 : V)) := by
    intro h
    exact h.ne_zero () (by simp)
  have hbad : {z : K | ¬ LinearIndependent E
      (fun _ : Unit => (0 : V))} = Set.univ := by
    ext z
    simp [hzero]
  rw [hbad, Set.not_finite]
  exact Set.infinite_univ

end

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.zero_pencil_bad_set_not_finite
