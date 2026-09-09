import SymplecticStafford.FiniteLength.FiniteCentralDivisionActivated

/-!
# Minimal-prime local finite-length input for activated division blocks

The filtered/localized M05 endpoint is a `MinimalPrimeLocalInput`: it names a
local model obtained from a finite good module and supplies the local
Noetherian/Artinian certificate.  This file turns that certificate into an
explicit right composition filtration, including finite adjacent quotients,
and feeds the resulting finite module to the finite-central M07 consumer.

The support set, minimal point, local source and local finiteness fields remain
visible in the input.  No filtered characteristic-support construction,
finite-length theorem for arbitrary modules, or block/Jacobson comparison is
constructed here.
-/

namespace SymplecticStafford.FiniteLength

universe u v w q

section LocalFiltration

variable {R : Type u} [Ring R] {G : Type v} {N : Type w}
variable [AddCommGroup G] [Module Rᵐᵒᵖ G]
variable [AddCommGroup N] [Module Rᵐᵒᵖ N]
variable {α : Type v} [Preorder α]

/-- An M05 local certificate yields the explicit finite right composition
filtration needed by the M07 consumers.  Its levels are the composition
series supplied by the proved finite-length endpoint.  The current activated
consumer is label-independent and fixes its filtration label type to `Unit`,
so the local certificate's support labels remain explicit input data but are
collapsed to the canonical singleton support in the returned filtration.
-/
theorem right_filtration_of_minimalPrime_local
    (W : MinimalPrimeLocalInput (R := Rᵐᵒᵖ) G N α) :
    ∃ n : Nat,
      Nonempty (RightMinimalSupportFiltration (R := R) (M := N)
        (α := Unit) n) := by
  have hlength := local_isFiniteLength_of_minimalPrime W
  obtain ⟨s, hshead, hslast⟩ :=
    isFiniteLength_iff_exists_compositionSeries.mp hlength
  letI : Module.Finite Rᵐᵒᵖ N := local_module_finite_of_minimalPrime W
  have hsplit : IsNoetherian Rᵐᵒᵖ N ∧ IsArtinian Rᵐᵒᵖ N :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hlength
  letI : IsNoetherian Rᵐᵒᵖ N := hsplit.1
  let support : Set Unit := {()}
  let minimalPoint : MinimalSupportPoint support :=
    { point := ()
      mem_support := by simp [support]
      minimal := by
        intro q hq _
        simpa [support] using hq }
  let F : RightMinimalSupportFiltration (R := R) (M := N)
      (α := Unit) s.length :=
    { support := support
      minimalPoint := minimalPoint
      level := s.toFun
      head := hshead
      last := hslast
      step := s.step
      quotient_finite := by
        intro i
        letI : Module.Finite Rᵐᵒᵖ (s.toFun i.succ) :=
          Module.Finite.of_injective
            (σ := RingHom.id Rᵐᵒᵖ) (σ' := RingHom.id Rᵐᵒᵖ)
            (s.toFun i.succ).subtype
            (Submodule.injective_subtype _)
        exact Module.Finite.of_surjective
          (Submodule.mkQ
            ((s.toFun i.castSucc).comap (s.toFun i.succ).subtype))
          (Submodule.mkQ_surjective
            ((s.toFun i.castSucc).comap (s.toFun i.succ).subtype)) }
  exact ⟨s.length, ⟨F⟩⟩

end LocalFiltration

section Activated

variable {R : Type u} {G : Type v} {N : Type w} {K : Type q} [Ring R]
    [AddCommGroup G] [Module Rᵐᵒᵖ G]
    [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Field K] [Module K N] [Infinite K]
    {J : Type*} [Fintype J] [DecidableEq J]
    {r : J → Nat}
    {EJ : J → Type*} [∀ j, DivisionRing (EJ j)]
    {QJ : J → Type*} [∀ j, AddCommGroup (QJ j)]
    [∀ j, Module (EJ j) (QJ j)] [∀ j, Module K (QJ j)]
    [∀ j, Module K (EJ j)] [∀ j, FiniteDimensional K (EJ j)]
    {α : Type v} [Preorder α]

/-- Compose an explicit M05 minimal-prime local certificate with the
finite-central repeated-division-block M07 consumer.

The actual activated module is the local model `N`, not the source good
module `G`.  All block/Jacobson comparison data and the ordered right action
remain explicit, while finite generation is derived from `W.source_surjective`
and finite length from `W.local_noetherian`/`W.local_artinian`.
-/
theorem exists_activated_right_cyclic_of_minimalPrime_local_finite_central_isotypic
    (W : MinimalPrimeLocalInput (R := Rᵐᵒᵖ) G N α)
    (ι : (j : J) → K →+* EJ j)
    (top : N →+ ((j : J) → (Fin (r j) → QJ j)))
    (map_smul : ∀ (z : K) (m : N) (j : J) (i : Fin (r j)),
      top (z • m) j i = (ι j z) • top m j i)
    (central_coeff : ∀ (j : J) (k : K) (e : EJ j),
      k • e = ι j k * e)
    (central_embedding : ∀ (j : J) (k : K) (e : EJ j),
      ι j k * e = e * ι j k)
    (central_vector : ∀ (j : J) (k : K) (v : QJ j),
      k • v = (ι j k) • v)
    (block_generator : ∀ (j : J) (x : Fin (r j) → QJ j), Prop)
    (block_generator_iff_linearIndependent : ∀ j x,
      block_generator j x ↔ LinearIndependent (EJ j) x)
    (top_generator_iff_jacobson : ∀ m : N,
      (∀ j, block_generator j (top m j)) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ N).mkQ m))
    (rightAction : R → N → N)
    (rightAction_add : ∀ (a : R) (x y : N),
      rightAction a (x + y) = rightAction a x + rightAction a y)
    (central_smul_right : ∀ (k : K) (m : N) (a : R),
      rightAction a (k • m) = k • rightAction a m)
    (v u e : N) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : ∀ j, block_generator j (top v j))
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧
      RightCyclic (R := R) (v + z • u) ∧
      rightAction l (v + z • u) + z • rightAction b v = z • e := by
  obtain ⟨n, hF⟩ := right_filtration_of_minimalPrime_local W
  rcases hF with ⟨F⟩
  exact exists_activated_right_cyclic_of_finite_central_isotypic
    F ι top map_smul central_coeff central_embedding central_vector
    block_generator block_generator_iff_linearIndependent
    top_generator_iff_jacobson rightAction rightAction_add central_smul_right
    v u e b l vL_zero e_decomp hv forbidden hforbidden

end Activated

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.right_filtration_of_minimalPrime_local
#print axioms
  SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_minimalPrime_local_finite_central_isotypic
