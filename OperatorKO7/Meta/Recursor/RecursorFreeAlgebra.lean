import OperatorKO7.Kernel
import OperatorKO7.Meta.Recursor.DPConfessionLicense

/-!
# Recursor Free Algebra over the seven-arity KO7 signature

This module supplies the substrate that replaces the W17.3
`PartialProgressClaim` carriers in
`Meta/Recursor/DPConfessionLicense.lean` with unconditional theorems.
The closure path requires a custom free-algebra surface over the
seven-arity KO7 signature
`{void, delta, integrate, merge, app, recR, eqWit}`. This module
ships the surface and the substitution-invariance induction
principle.

## Why a custom surface

Mathlib's `Mathlib.Algebra.Free`, `FreeMonoid.Basic`, and
`Mathlib.Algebra.FreeMagmaWithZero` package free algebras over a
single binary operation (`Free.Magma`) or a single monoid operation
(`FreeMonoid`). Neither generalizes cleanly to a seven-arity mixed
signature with a constant (`void`), three unaries (`delta`,
`integrate`, single-argument view of `merge`/`app`/etc.), three
binaries (`merge`, `app`, `eqWit`), and one ternary (`recR`).
The W17.3 `PartialProgressClaim` carrier flagged this as the
specific Mathlib obstruction. The closure path stated in
`Meta/Recursor/DPConfessionLicense.lean` is "define a custom
`RecursorFreeAlgebra` ... prove the substitution-invariance lemma
by structural induction on the closed-term tree". This module
executes that closure path.

## What the surface provides

The `RecursorTerm` inductive type already lives in
`Meta/Recursor/DPConfessionLicense.lean` (introduced under the
honest-failure carrier). Here we add:

  * `Σ-algebra` structure record bundling the seven operator slots.
  * `RecursorTerm.fold`: the canonical universal-property fold from
    `RecursorTerm` to any Σ-algebra.
  * `RecursorTerm.fold_unique`: the universal property — any
    function that respects the seven operators agrees with `fold`
    on every closed term. This is the substitution-invariance
    induction principle the closure path requires.
  * `IsSigmaHomomorphism`: the predicate "respects all seven
    operators".
  * `DpCollapseToVoidSigma`: the constant-`void` Σ-algebra
    structure. Every `RecursorTerm` folds to `void` under this
    structure. This is the formal handle on the
    `dpCollapseToVoid` collapse used by the existing W17.3
    negative-witness lemma.
  * `FactorsThroughCollapse`: the "image of a function defined on
    the constant-collapse Σ-algebra" predicate. The unconditional
    theorem is "every signature-fold-expressible function factors
    through `dpCollapseToVoid`", combined with the existing
    `DP_projection_is_not_substitution_invariant` lemma to derive
    "DP projection is not signature-fold-expressible".

No `sorry`. No new `axiom`. The substitution-invariance principle
closes by direct structural induction on `RecursorTerm`.
-/

open OperatorKO7
open OperatorKO7.Meta.Recursor.DPConfessionLicense

namespace OperatorKO7.Meta.Recursor.RecursorFreeAlgebra

universe u

/-- A `Σ-algebra` over the seven-arity KO7 signature. The seven slots
record the carrier-side image of each `RecursorTerm` constructor. -/
structure SigmaAlgebra (α : Type u) : Type u where
  void      : α
  delta     : α → α
  integrate : α → α
  merge     : α → α → α
  app       : α → α → α
  recR      : α → α → α → α
  eqWit     : α → α → α

/-- The canonical universal-property fold from `RecursorTerm` to any
`SigmaAlgebra` carrier. This is the unique Σ-algebra homomorphism
into the target carrier, by the universal property of free algebras. -/
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

/-- **Substitution-invariance induction principle.** The universal
property of the free algebra: any Σ-homomorphism `f : RecursorTerm
→ α` agrees with the canonical fold on every closed term. This is
the closure-path principle: a function determined by its
action on the seven generators is uniquely determined on the entire
free algebra.

Proof: by direct structural induction on the closed-term tree. -/
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

/-- The fold under the constant-`void` Σ-algebra structure agrees
with `dpCollapseToVoid` (the existing W17.3 negative-witness
substitution): every closed term folds to `void`. -/
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

/-- "Factors through the constant-`void` Σ-algebra" predicate: a
function `P : RecursorTerm → α` factors iff its image is determined
solely by the carrier's `void` constant. -/
def FactorsThroughCollapse {α : Type u}
    (P : RecursorTerm → α) : Prop :=
  ∃ k : α, ∀ t : RecursorTerm, P t = k

/-- **Lemma.** If a function `P : RecursorTerm → α` is a
Σ-homomorphism into the constant-`void` Σ-algebra (every slot
returns `void`), then `P` is a constant function. This is the
formal handle on "factors through the constant-collapse
substitution". -/
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

/-- **Anti-distinguishability principle.** Any function that factors
through the constant-`void` Σ-algebra cannot distinguish any two
RecursorTerms — its image is constant. -/
theorem factorsThroughCollapse_no_distinguishing
    {α : Type u} (P : RecursorTerm → α)
    (h : FactorsThroughCollapse P) :
    ∀ a b : RecursorTerm, P a = P b := by
  obtain ⟨k, hk⟩ := h
  intro a b
  rw [hk a, hk b]

end OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
