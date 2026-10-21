module

public import SymplecticStafford.FiniteLength.PencilBridge
public import SymplecticStafford.FiniteLength.MatrixPencil
public import SymplecticStafford.FiniteLength.RadicalLift

@[expose] public section

/-!
# Simultaneous finite-length top pencils

This file isolates the part of the finite-length argument which is genuinely
elementary once the semisimple-top coordinates have been exposed.  Each local
top is represented by a finite product of division rings.  A nonzero coordinate
of `v` can vanish after the central pencil perturbation at at most one scalar;
the finite union of these exceptional sets can therefore be avoided together
with any previously forbidden finite set.

The theorem below is deliberately an interface theorem.  It does not assert
the finite-length decomposition, radical lifting, or the construction of the
top coordinates from a cyclic quotient.  Those are separate M06 obligations.
In particular, no generation conclusion is stored as a structure field: the
caller supplies the explicit reflection implication to the theorem and gets
an existential proposition as its result.
-/

namespace SymplecticStafford.FiniteLength

section SimultaneousTop

variable {K : Type*} [Field K] [Infinite K]
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {ι : J → Type*} [∀ j, Fintype (ι j)]
variable [∀ j, DecidableEq (ι j)]
variable {D : (j : J) → ι j → Type*}
variable [∀ j i, DivisionRing (D j i)]
variable (ιmap : (j : J) → (i : ι j) → K →+* D j i)

/-- The union of all local top-pencil exceptions is finite. -/
theorem finite_simultaneous_pencil_exceptions
    (v u : (j : J) → (i : ι j) → D j i)
    (hv : ∀ j i, v j i ≠ 0)
    (hinj : ∀ j i, Function.Injective (ιmap j i)) :
    Set.Finite
      (⋃ j : J, {z : K | ∃ i, v j i + ιmap j i z * u j i = 0}) := by
  classical
  apply Set.finite_iUnion
  intro j
  exact finite_pencil_exceptions (fun i => ιmap j i) (v j) (u j)
    (fun i => hv j i) (fun i => hinj j i)

/--
One central scalar simultaneously keeps every prescribed finite semisimple top
generator, while avoiding an arbitrary finite set of scalars.  The only
generation input is the explicit coordinate criterion, proved in
`Pencil.lean`; no finite-length or radical-lifting theorem is hidden here.
-/
theorem exists_simultaneous_top_generator_avoiding
    (v u : (j : J) → (i : ι j) → D j i)
    (hv : ∀ j i, v j i ≠ 0)
    (hinj : ∀ j i, Function.Injective (ιmap j i))
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K,
      z ∉ forbidden ∧
        ∀ j, TopGenerator (fun i => v j i + ιmap j i z * u j i) := by
  classical
  let exceptions : Set K :=
    ⋃ j : J, {z : K | ∃ i, v j i + ιmap j i z * u j i = 0}
  have hexceptions : exceptions.Finite := by
    exact finite_simultaneous_pencil_exceptions ιmap v u hv hinj
  have hall : (forbidden ∪ exceptions).Finite := hforbidden.union hexceptions
  obtain ⟨z, hz⟩ := (Set.infinite_univ.sdiff hall).nonempty
  refine ⟨z, ?_, ?_⟩
  · intro h
    exact hz.2 (Or.inl h)
  · intro j
    apply (semisimple_top_criterion _).2
    intro i hzero
    apply hz.2
    right
    exact Set.mem_iUnion.2 ⟨j, ⟨i, hzero⟩⟩

end SimultaneousTop

section ActivatedRightModule

variable {R M K : Type*} [Semiring R] [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Field K] [Module K M] [Infinite K]
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {ι : J → Type*} [∀ j, Fintype (ι j)]
variable [∀ j, DecidableEq (ι j)]
variable {D : (j : J) → ι j → Type*}
variable [∀ j i, DivisionRing (D j i)]
variable (ιmap : (j : J) → (i : ι j) → K →+* D j i)

/--
Simultaneous activated-pencil generation for a finite family of local tops.

`top` and `map_smul` are the concrete finite-top coordinates, while
`reflects_generation` is an ordinary theorem hypothesis saying that a vector
which generates each exposed top is right-cyclic.  Thus the result is useful
for a finite-length quotient after its top decomposition and radical-lifting
lemma have been proved, but it does not pretend to prove those lemmas.
-/
theorem exists_simultaneous_right_cyclic_avoiding
    (top : M →+ ((j : J) → (i : ι j) → D j i))
    (map_smul : ∀ (z : K) (m : M) (j : J) (i : ι j),
      top (z • m) j i = ιmap j i z * top m j i)
    (reflects_generation : ∀ m,
      (∀ j, TopGenerator (fun i => top m j i)) →
        RightCyclic (R := R) m)
    (m u : M)
    (hm : ∀ j i, top m j i ≠ 0)
    (hinj : ∀ j i, Function.Injective (ιmap j i))
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K,
      z ∉ forbidden ∧ RightCyclic (R := R) (m + z • u) := by
  classical
  have htop : ∀ j i, top (m + (0 : K) • u) j i ≠ 0 := by
    intro j i
    simpa using hm j i
  have hmap : ∀ (z : K) (j : J) (i : ι j),
      top (m + z • u) j i = top m j i + ιmap j i z * top u j i := by
    intro z j i
    calc
      top (m + z • u) j i = (top m + top (z • u)) j i := by rw [map_add]
      _ = top m j i + top (z • u) j i := rfl
      _ = top m j i + ιmap j i z * top u j i := by rw [map_smul]
  have htopgen :
      ∃ z : K, z ∉ forbidden ∧
        ∀ j, TopGenerator (fun i => top (m + z • u) j i) := by
    obtain ⟨z, hz, hgen⟩ := exists_simultaneous_top_generator_avoiding
      ιmap (fun j i => top m j i) (fun _ _ => top u _ _) hm hinj forbidden hforbidden
    refine ⟨z, hz, ?_⟩
    intro j
    simpa [hmap] using hgen j
  obtain ⟨z, hz, hgen⟩ := htopgen
  exact ⟨z, hz, reflects_generation (m + z • u) hgen⟩

end ActivatedRightModule

section ActivatedFiniteTopLift

variable {R M K : Type*} [Semiring R] [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Field K] [Module K M] [Infinite K]
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {ι : J → Type*} [∀ j, Fintype (ι j)]
variable [∀ j, DecidableEq (ι j)]
variable {D : (j : J) → ι j → Type*}
variable [∀ j i, DivisionRing (D j i)]
variable (ιmap : (j : J) → (i : ι j) → K →+* D j i)

/-- Activated cyclicity with an explicit finite top-lifting certificate.

For every top-generating vector, `finite_top_lift` supplies a finite
descending filtration in the sense of `FiniteTopLifting`; the latter is then
used to reflect top generation to right cyclicity.  Thus this theorem applies
to arbitrary supplied finite-length filtrations, including repeated simple
factors, while making clear that the filtration and top comparison are still
inputs rather than consequences of finite length.  The selected scalar also
obeys the ordered relation forced by `vL_zero` and `e_decomp`. -/
theorem exists_activated_right_cyclic_of_finite_top_lifting
    (top : M →+ ((j : J) → (i : ι j) → D j i))
    (map_smul : ∀ (z : K) (m : M) (j : J) (i : ι j),
      top (z • m) j i = ιmap j i z * top m j i)
    (finite_top_lift : ∀ m,
      (∀ j, TopGenerator (fun i => top m j i)) →
        ∃ n : Nat, Nonempty (FiniteTopLifting R M n m))
    (rightAction : R → M → M)
    (rightAction_add : ∀ (r : R) (x y : M),
      rightAction r (x + y) = rightAction r x + rightAction r y)
    (central_smul_right : ∀ (k : K) (m : M) (r : R),
      rightAction r (k • m) = k • rightAction r m)
    (v u e : M) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : ∀ j i, top v j i ≠ 0)
    (hinj : ∀ j i, Function.Injective (ιmap j i))
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧
      RightCyclic (R := R) (v + z • u) ∧
      rightAction l (v + z • u) + z • rightAction b v = z • e := by
  obtain ⟨z, hz, hgen⟩ := exists_simultaneous_top_generator_avoiding
    ιmap (fun j i => top v j i) (fun j i => top u j i) hv hinj
    forbidden hforbidden
  have hgen' : ∀ j, TopGenerator (fun i => top (v + z • u) j i) := by
    intro j
    have hmap : ∀ i, top (v + z • u) j i =
        top v j i + ιmap j i z * top u j i := by
      intro i
      calc
        top (v + z • u) j i = (top v + top (z • u)) j i := by rw [map_add]
        _ = top v j i + top (z • u) j i := rfl
        _ = top v j i + ιmap j i z * top u j i := by rw [map_smul]
    simpa [hmap] using hgen j
  obtain ⟨n, hF⟩ := finite_top_lift (v + z • u) hgen'
  obtain ⟨F⟩ := hF
  refine ⟨z, hz, rightCyclic_of_finite_top_lifting F, ?_⟩
  exact pencil_right_action_add rightAction rightAction_add
    central_smul_right v u e b l vL_zero e_decomp z

end ActivatedFiniteTopLift

section ActivatedRepeatedBlocks

variable {R M K : Type*} [Semiring R] [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Field K] [Module K M] [Infinite K]
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {r : Nat}

/-- Simultaneous generation for a finite family of repeated matrix blocks,
with the activated relation retained in the original right-action order.

`top` is the supplied finite-length top comparison and
`reflects_generation` is the only module-theoretic bridge: it says that
generation of every exposed matrix block lifts to right cyclicity.  The
matrix products in `MatrixTopGenerator` are ordered `top m * coefficient`.
The hypotheses `vL_zero` and `e_decomp` are used through
`pencil_right_action_add`, so the conclusion records the exact relation
`(v + k • u)L + k • (vB) = k • e` for the selected scalar. -/
theorem exists_activated_matrix_right_cyclic_avoiding
    (top : M →+ ((j : J) → Matrix (Fin r) (Fin r) K))
    (map_smul : ∀ (z : K) (m : M) (j : J),
      top (z • m) j = z • top m j)
    (reflects_generation : ∀ m,
      (∀ j, MatrixTopGenerator (top m j)) →
        RightCyclic (R := R) m)
    (rightAction : R → M → M)
    (rightAction_add : ∀ (r : R) (x y : M),
      rightAction r (x + y) = rightAction r x + rightAction r y)
    (central_smul_right : ∀ (k : K) (m : M) (r : R),
      rightAction r (k • m) = k • rightAction r m)
    (v u e : M) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : ∀ j, Matrix.det (top v j) ≠ 0)
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ k : K, k ∉ forbidden ∧
      RightCyclic (R := R) (v + k • u) ∧
      rightAction l (v + k • u) + k • rightAction b v = k • e := by
  have htop : ∀ j, Matrix.det (top v j) ≠ 0 := hv
  obtain ⟨k, hk, hgen⟩ := exists_simultaneous_matrix_top_generator_avoiding
    (A := fun j => top v j) (C := fun j => top u j) htop forbidden hforbidden
  refine ⟨k, hk, ?_, ?_⟩
  · apply reflects_generation
    intro j
    have htop_add : top (v + k • u) j = top v j + k • top u j := by
      calc
        top (v + k • u) j = (top v + top (k • u)) j := by rw [map_add]
        _ = top v j + top (k • u) j := rfl
        _ = top v j + k • top u j := by rw [map_smul]
    rw [htop_add]
    exact hgen j
  · exact pencil_right_action_add rightAction rightAction_add
      central_smul_right v u e b l vL_zero e_decomp k

end ActivatedRepeatedBlocks

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.finite_simultaneous_pencil_exceptions
#print axioms SymplecticStafford.FiniteLength.exists_simultaneous_top_generator_avoiding
#print axioms SymplecticStafford.FiniteLength.exists_simultaneous_right_cyclic_avoiding
#print axioms SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_finite_top_lifting
#print axioms SymplecticStafford.FiniteLength.exists_activated_matrix_right_cyclic_avoiding
