import OperatorKO7.Kernel
import OperatorKO7.Meta.Recursor.DPConfessionLicense

/-!
# Fold algebra for the seven-constructor `RecursorTerm` signature

`SigmaAlgebra` supplies interpretations for one nullary, two unary, three binary, and one ternary
constructor. `RecursorTerm.fold` evaluates a term in such an algebra.
`RecursorFreeAlgebra.substitution_invariance`, despite its historical name, is the ordinary fold
uniqueness theorem for a function satisfying the seven homomorphism equations.

The constant algebra sends every constructor to one value. `FactorsThroughCollapse` is exactly the
predicate that a function is constant, and the final theorems prove constancy and consequent failure
to distinguish two terms. This module does not prove that a dependency-pair projection is
inexpressible or substitution-variant.
-/

open OperatorKO7
open OperatorKO7.Meta.Recursor.DPConfessionLicense

namespace OperatorKO7.Meta.Recursor.RecursorFreeAlgebra

universe u

/-- An algebra over the seven-constructor, mixed-arity `RecursorTerm` signature. The seven slots
record the carrier-side interpretation of each constructor. -/
structure SigmaAlgebra (α : Type u) : Type u where
  void      : α
  delta     : α → α
  integrate : α → α
  merge     : α → α → α
  app       : α → α → α
  recR      : α → α → α → α
  eqWit     : α → α → α

/-- Recursive evaluation of `RecursorTerm` in a `SigmaAlgebra`. Uniqueness under the homomorphism
equations is proved below. -/
def RecursorTerm.fold {α : Type u} (S : SigmaAlgebra α) :
    RecursorTerm → α
  | .void          => S.void
  | .delta t       => S.delta (RecursorTerm.fold S t)
  | .integrate t   => S.integrate (RecursorTerm.fold S t)
  | .merge a b     => S.merge (RecursorTerm.fold S a)
                              (RecursorTerm.fold S b)
  | .app a b       => S.app (RecursorTerm.fold S a)
                            (RecursorTerm.fold S b)
  | .recR b s n    => S.recR (RecursorTerm.fold S b)
                             (RecursorTerm.fold S s)
                             (RecursorTerm.fold S n)
  | .eqWit a b     => S.eqWit (RecursorTerm.fold S a)
                              (RecursorTerm.fold S b)

/-- The "respects all seven operators" predicate for an arbitrary
function `f : RecursorTerm → α`. -/
structure IsSigmaHomomorphism {α : Type u}
    (f : RecursorTerm → α) (S : SigmaAlgebra α) : Prop where
  pres_void      : f RecursorTerm.void = S.void
  pres_delta     : ∀ t, f (RecursorTerm.delta t) = S.delta (f t)
  pres_integrate : ∀ t, f (RecursorTerm.integrate t) = S.integrate (f t)
  pres_merge     : ∀ a b, f (RecursorTerm.merge a b)
                            = S.merge (f a) (f b)
  pres_app       : ∀ a b, f (RecursorTerm.app a b)
                            = S.app (f a) (f b)
  pres_recR      : ∀ b s n, f (RecursorTerm.recR b s n)
                              = S.recR (f b) (f s) (f n)
  pres_eqWit     : ∀ a b, f (RecursorTerm.eqWit a b)
                            = S.eqWit (f a) (f b)

/-- The fold itself is a Σ-homomorphism into the target carrier. -/
theorem RecursorTerm.fold_isSigmaHomomorphism
    {α : Type u} (S : SigmaAlgebra α) :
    IsSigmaHomomorphism (RecursorTerm.fold S) S where
  pres_void      := rfl
  pres_delta     := fun _ => rfl
  pres_integrate := fun _ => rfl
  pres_merge     := fun _ _ => rfl
  pres_app       := fun _ _ => rfl
  pres_recR      := fun _ _ _ => rfl
  pres_eqWit     := fun _ _ => rfl

/-- Any function satisfying the seven homomorphism equations agrees with the recursive fold. The
historical declaration name uses “substitution invariance,” but the theorem mentions no substitution
operation. -/
theorem RecursorFreeAlgebra.substitution_invariance
    {α : Type u} (S : SigmaAlgebra α)
    (f : RecursorTerm → α) (hf : IsSigmaHomomorphism f S) :
    ∀ t : RecursorTerm, f t = RecursorTerm.fold S t := by
  intro t
  induction t with
  | void          => exact hf.pres_void
  | delta t ih    => simp [RecursorTerm.fold, hf.pres_delta, ih]
  | integrate t ih=> simp [RecursorTerm.fold, hf.pres_integrate, ih]
  | merge a b iha ihb =>
      simp [RecursorTerm.fold, hf.pres_merge, iha, ihb]
  | app a b iha ihb =>
      simp [RecursorTerm.fold, hf.pres_app, iha, ihb]
  | recR b s n ihb ihs ihn =>
      simp [RecursorTerm.fold, hf.pres_recR, ihb, ihs, ihn]
  | eqWit a b iha ihb =>
      simp [RecursorTerm.fold, hf.pres_eqWit, iha, ihb]

/-- The constant-`void` Σ-algebra structure on `RecursorTerm`. Every
slot is the constant function returning `RecursorTerm.void`. -/
def DpCollapseToVoidSigma : SigmaAlgebra RecursorTerm where
  void      := RecursorTerm.void
  delta     := fun _   => RecursorTerm.void
  integrate := fun _   => RecursorTerm.void
  merge     := fun _ _ => RecursorTerm.void
  app       := fun _ _ => RecursorTerm.void
  recR      := fun _ _ _ => RecursorTerm.void
  eqWit     := fun _ _ => RecursorTerm.void

/-- Folding through the constant-`void` algebra agrees with the constant function
`dpCollapseToVoid`. -/
theorem RecursorTerm.fold_DpCollapseToVoidSigma_eq_dpCollapseToVoid
    (t : RecursorTerm) :
    RecursorTerm.fold DpCollapseToVoidSigma t = dpCollapseToVoid t := by
  induction t with
  | void          => rfl
  | delta _ _     => rfl
  | integrate _ _ => rfl
  | merge _ _ _ _ => rfl
  | app _ _ _ _   => rfl
  | recR _ _ _ _ _ _ => rfl
  | eqWit _ _ _ _ => rfl

/-- Historical name for the proposition that `P` is a constant function. -/
def FactorsThroughCollapse {α : Type u}
    (P : RecursorTerm → α) : Prop :=
  ∃ k : α, ∀ t : RecursorTerm, P t = k

/-- A homomorphism into an algebra whose seven operations all return `k` is constant with value `k`. -/
theorem factorsThroughCollapse_of_constantSigmaHomomorphism
    {α : Type u} (k : α) (P : RecursorTerm → α)
    (S : SigmaAlgebra α)
    (hSconst : S.void = k ∧
              (∀ x, S.delta x = k) ∧
              (∀ x, S.integrate x = k) ∧
              (∀ x y, S.merge x y = k) ∧
              (∀ x y, S.app x y = k) ∧
              (∀ x y z, S.recR x y z = k) ∧
              (∀ x y, S.eqWit x y = k))
    (hP : IsSigmaHomomorphism P S) :
    ∀ t : RecursorTerm, P t = k := by
  intro t
  rw [RecursorFreeAlgebra.substitution_invariance S P hP]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hSconst
  induction t with
  | void          => simp [RecursorTerm.fold, h0]
  | delta t ih    => simp [RecursorTerm.fold, h1, ih]
  | integrate t ih=> simp [RecursorTerm.fold, h2, ih]
  | merge a b iha ihb =>
      simp [RecursorTerm.fold, h3, iha, ihb]
  | app a b iha ihb =>
      simp [RecursorTerm.fold, h4, iha, ihb]
  | recR b s n ihb ihs ihn =>
      simp [RecursorTerm.fold, h5, ihb, ihs, ihn]
  | eqWit a b iha ihb =>
      simp [RecursorTerm.fold, h6, iha, ihb]

/-- A function satisfying `FactorsThroughCollapse` has equal values on every two terms. -/
theorem factorsThroughCollapse_no_distinguishing
    {α : Type u} (P : RecursorTerm → α)
    (h : FactorsThroughCollapse P) :
    ∀ a b : RecursorTerm, P a = P b := by
  obtain ⟨k, hk⟩ := h
  intro a b
  rw [hk a, hk b]

end OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
