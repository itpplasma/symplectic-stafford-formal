module

public import SymplecticStafford.Paper.RightFraction
public import SymplecticStafford.Paper.Pencil

@[expose] public section

/-!
# Admissible local tests (paper Definition 1.1)

An admissible test is a tuple `(T, V, e, b, z)`: `T` is a ring of right
fractions of `U` (an actual Ore localization in the application) which is a
simple nondivision domain, `V` is a finite-length right `T`-module generated
by `e`, `b ∈ U` is nonzero and `z ∈ V`.  A source `F ∈ U` satisfies the test
when `(z + e F b) T = V`.

Right `T`-modules are `Tᵐᵒᵖ`-modules: `e · x` is `op x • e`.
-/

namespace SymplecticStafford.Paper

open MulOpposite

universe w

/-- An admissible local test (paper Definition 1.1). -/
structure Test (k U : Type*) [Field k] [Ring U] [Algebra k U] where
  /-- The localization. -/
  T : Type w
  [ring : Ring T]
  [alg : Algebra k T]
  ι : U →ₐ[k] T
  S : Submonoid U
  frac : IsRightFractions S (ι : U →+* T)
  simple : IsSimpleRing T
  domain : IsDomain T
  nondivision : ∃ τ : T, τ ≠ 0 ∧ ¬ IsUnit τ
  /-- The finite-length cyclic right module. -/
  V : Type w
  [acg : AddCommGroup V]
  [mod : Module Tᵐᵒᵖ V]
  artinian : IsArtinian Tᵐᵒᵖ V
  noetherian : IsNoetherian Tᵐᵒᵖ V
  e : V
  e_gen : Submodule.span Tᵐᵒᵖ {e} = ⊤
  b : U
  b_ne : b ≠ 0
  z : V

attribute [instance] Test.ring Test.alg Test.acg Test.mod

namespace Test

variable {k U : Type*} [Field k] [Ring U] [Algebra k U]

/-- `F` satisfies the test: `(z + e F b) T = V`. -/
def Satisfies (τ : Test.{w} k U) (F : U) : Prop :=
  Submodule.span τ.Tᵐᵒᵖ {τ.z + op (τ.ι (F * τ.b)) • τ.e} = ⊤

/-- The central scalar `λ` acts on a right `T`-module through `T`. -/
lemma op_algebraMap_mul_smul (τ : Test.{w} k U) (l : k) (x : τ.T) (v : τ.V) :
    op (algebraMap k τ.T l * x) • v = algebraMap k τ.Tᵐᵒᵖ l • (op x • v) := by
  rw [← mul_smul, MulOpposite.algebraMap_apply, ← op_mul, Algebra.commutes]

/-- **Retention of a carried test along a pencil** (the use of Corollary 4.8
in the successor step, (6.8)). -/
lemma satisfies_pencil_finite (τ : Test.{w} k U) {F : U} (hF : τ.Satisfies F) (G₀ : U) :
    {l : k | ¬ τ.Satisfies (F + algebraMap k U l * G₀)}.Finite := by
  have := τ.artinian
  refine (generator_pencil_finite (k := k) hF (op (τ.ι (G₀ * τ.b)) • τ.e)).subset ?_
  intro l hl
  refine fun h => hl ?_
  unfold Satisfies
  rw [add_mul, map_add, op_add, add_smul, mul_assoc, map_mul τ.ι (algebraMap k U l),
    AlgHom.commutes, op_algebraMap_mul_smul, ← add_assoc]
  exact h

end Test

end SymplecticStafford.Paper
