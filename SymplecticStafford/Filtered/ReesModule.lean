import Mathlib.Algebra.Module.Basic
import SymplecticStafford.Filtered.ReesQuotient

/-!
# Bounded Rees module terms

This file supplies the module side of the algebraic Rees checkpoint.  A
`ModuleFiltrationData` is a filtration of an `R`-module compatible with the
given filtration on `R`.  Bounded module terms, modulo equality of their
underlying module values, carry the scalar action induced by the value
quotient of scalar terms.

The quotient action is useful independently of any Noetherian hypothesis:
all representative changes and all module laws are checked in the kernel.
It does not assert that the Rees algebra is Noetherian or construct a good
filtration for an arbitrary module.
-/

namespace SymplecticStafford.Filtered

universe u v

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A multiplicative filtration on an `R`-module, compatible with `F`. -/
structure ModuleFiltrationData (F : FiltrationData R) (M : Type v)
    [AddCommMonoid M] [Module R M] where
  carrier : ℕ → Set M
  zero_mem : 0 ∈ carrier 0
  add_mem : ∀ {i j : ℕ} {x y : M}, x ∈ carrier i → y ∈ carrier j →
    x + y ∈ carrier (max i j)
  smul_mem : ∀ {i j : ℕ} {a : R} {x : M}, a ∈ F.carrier i →
    x ∈ carrier j → a • x ∈ carrier (i + j)
  monotone : Monotone carrier
  exhaustive : ∀ x : M, ∃ n : ℕ, x ∈ carrier n

def ModuleHasDegreeAtMost {F : FiltrationData R} {M : Type v}
    [AddCommMonoid M] [Module R M]
    (G : ModuleFiltrationData F M) (n : ℕ) (x : M) : Prop :=
  x ∈ G.carrier n

variable {F : FiltrationData R} {G : ModuleFiltrationData F M}

/-- An element of the raw bounded Rees module. -/
structure ReesModuleTerm (G : ModuleFiltrationData F M) where
  degree : ℕ
  value : M
  bounded : ModuleHasDegreeAtMost G degree value

namespace ReesModuleTerm

@[ext]
theorem ext {x y : ReesModuleTerm G} (hdegree : x.degree = y.degree)
    (hvalue : x.value = y.value) : x = y := by
  cases x with
  | mk xd xv xb =>
    cases y with
    | mk yd yv yb =>
      cases hdegree
      cases hvalue
      rfl

def reindex (x : ReesModuleTerm G) {n : ℕ} (h : x.degree ≤ n) :
    ReesModuleTerm G where
  degree := n
  value := x.value
  bounded := G.monotone h x.bounded

@[simp] theorem reindex_degree (x : ReesModuleTerm G) {n : ℕ}
    (h : x.degree ≤ n) : (reindex x h).degree = n := rfl

@[simp] theorem reindex_value (x : ReesModuleTerm G) {n : ℕ}
    (h : x.degree ≤ n) : (reindex x h).value = x.value := rfl

theorem reindex_reindex (x : ReesModuleTerm G) {m n : ℕ}
    (hm : x.degree ≤ m) (hn : m ≤ n) :
    reindex (reindex x hm) hn = reindex x (hm.trans hn) := by
  apply ext <;> rfl

theorem exists_value (G : ModuleFiltrationData F M) (x : M) :
    ∃ y : ReesModuleTerm G, y.value = x := by
  obtain ⟨n, hn⟩ := G.exhaustive x
  exact ⟨⟨n, x, hn⟩, rfl⟩

def zero : ReesModuleTerm G where
  degree := 0
  value := 0
  bounded := G.zero_mem

def add (x y : ReesModuleTerm G) : ReesModuleTerm G where
  degree := max x.degree y.degree
  value := x.value + y.value
  bounded := G.add_mem x.bounded y.bounded

/-- Scalar action on raw bounded terms. -/
def smul (a : ReesTerm F) (x : ReesModuleTerm G) : ReesModuleTerm G where
  degree := a.degree + x.degree
  value := a.value • x.value
  bounded := G.smul_mem a.bounded x.bounded

theorem reindex_add (x y : ReesModuleTerm G) {n : ℕ}
    (h : max x.degree y.degree ≤ n) (hx : x.degree ≤ n) (hy : y.degree ≤ n) :
    reindex (add x y) h = add (reindex x hx) (reindex y hy) := by
  apply ext
  · change n = max n n
    simp
  · rfl

theorem reindex_smul (a : ReesTerm F) (x : ReesModuleTerm G)
    {m n : ℕ} (ha : a.degree ≤ m) (hx : x.degree ≤ n) :
    reindex (smul a x) (Nat.add_le_add ha hx) =
      smul (ReesTerm.reindex a ha) (reindex x hx) := by
  apply ext <;> rfl

theorem add_assoc_term (x y z : ReesModuleTerm G) :
    add (add x y) z = add x (add y z) := by
  apply ext
  · exact max_assoc _ _ _
  · exact add_assoc _ _ _

theorem add_comm_term (x y : ReesModuleTerm G) : add x y = add y x := by
  apply ext
  · exact max_comm _ _
  · exact add_comm _ _

end ReesModuleTerm

namespace ReesModuleQuotient

variable {F : FiltrationData R} {G : ModuleFiltrationData F M}

def valueRel (x y : ReesModuleTerm G) : Prop := x.value = y.value

def valueSetoid (G : ModuleFiltrationData F M) : Setoid (ReesModuleTerm G) where
  r := valueRel
  iseqv := {
    refl := by intro x; rfl
    symm := by intro x y h; exact h.symm
    trans := by intro x y z hxy hyz; exact hxy.trans hyz
  }

end ReesModuleQuotient

/-- Raw bounded module terms modulo equality of their module values. -/
def ReesModuleQuotient {F : FiltrationData R} {M : Type v}
    [AddCommMonoid M] [Module R M] (G : ModuleFiltrationData F M) :=
  Quotient (ReesModuleQuotient.valueSetoid G)

namespace ReesModuleQuotient

theorem valueRel_add {x x' y y' : ReesModuleTerm G}
    (hx : valueRel x x') (hy : valueRel y y') :
    valueRel (ReesModuleTerm.add x y) (ReesModuleTerm.add x' y') := by
  change x.value + y.value = x'.value + y'.value
  exact congrArg₂ (· + ·) hx hy

theorem valueRel_smul {a a' : ReesTerm F} {x x' : ReesModuleTerm G}
    (ha : ReesTerm.valueRel a a') (hx : valueRel x x') :
    valueRel (ReesModuleTerm.smul a x) (ReesModuleTerm.smul a' x') := by
  change a.value • x.value = a'.value • x'.value
  change a.value = a'.value at ha
  change x.value = x'.value at hx
  rw [ha, hx]

def mk (x : ReesModuleTerm G) : ReesModuleQuotient G :=
  Quotient.mk (valueSetoid G) x

private theorem quotient_eq {x y : ReesModuleTerm G} (h : valueRel x y) :
    mk x = mk y :=
  @Quotient.sound (ReesModuleTerm G) (valueSetoid G) x y h

private theorem value_congr (x y : ReesModuleTerm G)
    (h : ReesModuleQuotient.valueRel x y) : x.value = y.value := h

def value : ReesModuleQuotient G → M :=
  Quotient.lift ReesModuleTerm.value value_congr

@[simp] theorem value_mk (x : ReesModuleTerm G) : value (mk x) = x.value := by
  change Quotient.lift ReesModuleTerm.value (value_congr (G := G))
      (Quotient.mk (ReesModuleQuotient.valueSetoid G) x) = x.value
  exact Quotient.lift_mk _ _ x

theorem eq_of_value_eq {x y : ReesModuleQuotient G} (h : value x = value y) : x = y := by
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y =>
      change x.value = y.value at h
      exact quotient_eq h

theorem reindex_mk (x : ReesModuleTerm G) {n : ℕ} (h : x.degree ≤ n) :
    mk (ReesModuleTerm.reindex x h) = mk x := quotient_eq rfl

def add (x y : ReesModuleQuotient G) : ReesModuleQuotient G :=
  Quotient.liftOn₂ x y
    (fun a b => mk (ReesModuleTerm.add a b))
    (by
      intro a b c d hac hbd
      exact quotient_eq (valueRel_add hac hbd))

def zero : ReesModuleQuotient G := mk ReesModuleTerm.zero

def smul (a : ReesQuotient F) (x : ReesModuleQuotient G) :
    ReesModuleQuotient G :=
  Quotient.liftOn₂ a x
    (fun b y => mk (ReesModuleTerm.smul b y))
    (by
      intro b y c z hbc hyz
      exact quotient_eq (valueRel_smul hbc hyz))

@[simp] theorem value_add (x y : ReesModuleQuotient G) :
    value (add x y) = value x + value y := by
  refine Quotient.inductionOn₂ x y ?_
  intro x y
  change value (mk (ReesModuleTerm.add x y)) =
    value (mk x) + value (mk y)
  rw [value_mk, value_mk, value_mk]
  rfl

@[simp] theorem value_smul (a : ReesQuotient F) (x : ReesModuleQuotient G) :
    value (smul a x) = ReesQuotient.value a • value x := by
  refine Quotient.inductionOn₂ a x ?_
  intro a x
  change value (mk (ReesModuleTerm.smul a x)) =
    ReesQuotient.value (ReesQuotient.mk a) • value (mk x)
  rw [value_mk, ReesQuotient.value_mk, value_mk]
  rfl

theorem add_assoc (x y z : ReesModuleQuotient G) :
    add (add x y) z = add x (add y z) := by
  apply eq_of_value_eq
  simp only [value_add]
  exact _root_.add_assoc _ _ _

theorem add_comm (x y : ReesModuleQuotient G) : add x y = add y x := by
  apply eq_of_value_eq
  simp only [value_add]
  exact _root_.add_comm _ _

theorem add_zero (x : ReesModuleQuotient G) : add x zero = x := by
  apply eq_of_value_eq
  have hz : value (zero (G := G)) = (0 : M) := by
    change value (mk (ReesModuleTerm.zero (G := G))) = (0 : M)
    rw [value_mk]
    rfl
  rw [value_add, hz]
  exact _root_.add_zero _

theorem zero_add (x : ReesModuleQuotient G) : add zero x = x := by
  apply eq_of_value_eq
  have hz : value (zero (G := G)) = (0 : M) := by
    change value (mk (ReesModuleTerm.zero (G := G))) = (0 : M)
    rw [value_mk]
    rfl
  rw [value_add, hz]
  exact _root_.zero_add _

theorem smul_add (a : ReesQuotient F) (x y : ReesModuleQuotient G) :
    smul a (add x y) = add (smul a x) (smul a y) := by
  apply eq_of_value_eq
  simp only [value_smul, value_add]
  exact _root_.smul_add _ _ _

theorem add_smul (a b : ReesQuotient F) (x : ReesModuleQuotient G) :
    smul (ReesQuotient.add a b) x = add (smul a x) (smul b x) := by
  apply eq_of_value_eq
  simp only [value_smul, ReesQuotient.value_add, value_add]
  exact _root_.add_smul _ _ _

theorem zero_smul (x : ReesModuleQuotient G) :
    smul ReesQuotient.zero x = mk (ReesModuleTerm.zero (G := G)) := by
  apply eq_of_value_eq
  have hz : ReesQuotient.value (ReesQuotient.zero (F := F)) = (0 : R) := by
    change ReesQuotient.value (ReesQuotient.mk (ReesTerm.zero (F := F))) = (0 : R)
    rw [ReesQuotient.value_mk]
    rfl
  have hm : value (mk (ReesModuleTerm.zero (G := G))) = (0 : M) := by
    rw [value_mk]
    rfl
  rw [value_smul, hz, hm]
  exact Module.zero_smul _

theorem smul_zero (a : ReesQuotient F) :
    smul a zero = mk (ReesModuleTerm.zero (G := G)) := by
  apply eq_of_value_eq
  have hm : value (zero (G := G)) = (0 : M) := by
    change value (mk (ReesModuleTerm.zero (G := G))) = (0 : M)
    rw [value_mk]
    rfl
  rw [value_smul, hm]
  exact _root_.smul_zero _

theorem one_smul (x : ReesModuleQuotient G) :
    smul ReesQuotient.one x = x := by
  apply eq_of_value_eq
  have ho : ReesQuotient.value (ReesQuotient.one (F := F)) = (1 : R) := by
    change ReesQuotient.value (ReesQuotient.mk (ReesTerm.one (F := F))) = (1 : R)
    rw [ReesQuotient.value_mk]
    rfl
  rw [value_smul, ho]
  exact _root_.one_smul R _

theorem mul_smul (a b : ReesQuotient F) (x : ReesModuleQuotient G) :
    smul (ReesQuotient.mul a b) x = smul a (smul b x) := by
  apply eq_of_value_eq
  simp only [value_smul, ReesQuotient.value_mul]
  exact (smul_smul _ _ _).symm

theorem exists_value (G : ModuleFiltrationData F M) (x : M) :
    ∃ y : ReesModuleQuotient G, value y = x := by
  rcases ReesModuleTerm.exists_value G x with ⟨y, hy⟩
  exact ⟨mk y, by simp [hy]⟩

end ReesModuleQuotient

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.ReesModuleQuotient.smul_add
#print axioms SymplecticStafford.Filtered.ReesModuleQuotient.add_smul
#print axioms SymplecticStafford.Filtered.ReesModuleQuotient.mul_smul
#print axioms SymplecticStafford.Filtered.ReesModuleQuotient.exists_value
