import OperatorKO7.Meta.BoundaryGeneral.EchoLaw
import OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
import OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryCompletion

/-!
# Persistent exogeny: a license expires exactly when its channel goes endogenous

`EchoLaw` classifies a single state. This module makes the classification
dynamic. A channel can read the object at issue time and stop reading it after
the dynamics moves, which is the informational form of guard expiry: the
warrant was real when granted and is gone when spent.

The persistent license is `Box R (InformativeAt E)`, the greatest forward
invariant sublicense of exogeny along `R`, reusing the live `Box` construction
rather than a private copy. The headline is
`license_expiry_iff_reachable_echo`: an exogenous state fails to carry a
persistent license exactly when some reachable state is an echo. License expiry
and channel endogenization are one event.

`safeRel_exogeny_greatest` supplies the dynamics-side companion: the greatest
subrelation of `R` that never carries an exogenous state to an endogenous one.

The payoff is `expired_license_emits_no_licensed_record`: past the expiry point
the echo law applies again, so an expired license licenses nothing.

## Claim typing (binding)
* PROVEN: the theorems below.
* SCOPE: exogeny here is `InformativeAt`, the structural reading. The
  quantitative reading transports through `EchoDeficitBridge` under channel
  sufficiency; this module makes no entropy claim.

## Audit slots
- Relation: an arbitrary one-step `R` on `E.State`.
- Closure: `Relation.ReflTransGen R`, through `Box`.
- Trust: no `sorry`/`admit`/`axiom`/`native_decide`; Mathlib baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.PersistentExogeny

open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.LicensedBoundaryCalculus

variable {E : Episode}

/-! ## The persistent license -/

/-- A state is **exogenous** when its channel reads the object coordinate. -/
def Exogenous (E : Episode) (s : E.State) : Prop :=
  InformativeAt E s

/-- **Persistent exogeny**: the channel reads the object at `s` and at every
`R`-reachable state. This is the greatest forward-invariant sublicense of
exogeny, supplied by the live `Box` construction. -/
def PersistentExogenous (E : Episode) (R : E.State → E.State → Prop) (s : E.State) : Prop :=
  Box R (Exogenous E) s

/-- A persistent license is a license. -/
theorem persistentExogenous_exogenous
    {R : E.State → E.State → Prop} {s : E.State}
    (h : PersistentExogenous E R s) : Exogenous E s :=
  h.holds

/-- A persistent license survives every reduction. -/
theorem persistentExogenous_persists
    {R : E.State → E.State → Prop} {s y : E.State}
    (h : PersistentExogenous E R s) (hy : Relation.ReflTransGen R s y) :
    Exogenous E y :=
  h.persists y hy

/-- The persistent license is itself forward invariant. -/
theorem persistentExogenous_forwardInvariant
    {R : E.State → E.State → Prop} {s y : E.State}
    (h : PersistentExogenous E R s) (hy : Relation.ReflTransGen R s y) :
    PersistentExogenous E R y :=
  box_forwardInvariant h hy

/-- **Greatestness.** Every forward-invariant sublicense of exogeny is contained
in the persistent license. Nothing stable is discarded. -/
theorem persistentExogenous_greatest
    {R : E.State → E.State → Prop} {Q : E.State → Prop}
    (hsub : ∀ s, Q s → Exogenous E s) (hinv : ForwardInvariant R Q)
    {s : E.State} (hs : Q s) : PersistentExogenous E R s :=
  box_greatest hsub hinv hs

/-! ## Expiry is endogenization -/

/-- **The expiry theorem.** An exogenous state carries no persistent license
exactly when some reachable state is an echo. License expiry and channel
endogenization are the same event. -/
theorem license_expiry_iff_reachable_echo
    {R : E.State → E.State → Prop} {s : E.State} (hs : Exogenous E s) :
    ¬ PersistentExogenous E R s ↔
      ∃ y, Relation.ReflTransGen R s y ∧ EchoAt E y := by
  constructor
  · intro hnot
    refine Classical.byContradiction (fun hno => ?_)
    refine hnot ⟨hs, fun y hy => ?_⟩
    refine Classical.byContradiction (fun hne => ?_)
    exact hno ⟨y, hy, (echoAt_iff_not_informativeAt E y).mpr hne⟩
  · rintro ⟨y, hy, hecho⟩ hbox
    exact (echoAt_iff_not_informativeAt E y).mp hecho (hbox.persists y hy)

/-- The contrapositive reading: a license that never meets an echo downstream is
persistent. -/
theorem persistentExogenous_of_no_reachable_echo
    {R : E.State → E.State → Prop} {s : E.State} (hs : Exogenous E s)
    (hno : ¬ ∃ y, Relation.ReflTransGen R s y ∧ EchoAt E y) :
    PersistentExogenous E R s := by
  refine Classical.byContradiction (fun hnot => ?_)
  exact hno ((license_expiry_iff_reachable_echo hs).mp hnot)

/-- A persistent license meets no echo anywhere downstream. -/
theorem persistentExogenous_no_reachable_echo
    {R : E.State → E.State → Prop} {s : E.State}
    (h : PersistentExogenous E R s) :
    ¬ ∃ y, Relation.ReflTransGen R s y ∧ EchoAt E y := by
  rintro ⟨y, hy, hecho⟩
  exact (echoAt_iff_not_informativeAt E y).mp hecho (h.persists y hy)

/-! ## The dynamics-side companion -/

/-- **The greatest exogeny-preserving dynamics.** `SafeRel R Exogenous` retains
exactly the edges that cannot carry an exogenous state to an endogenous one, and
is greatest among such subrelations. -/
theorem safeRel_exogeny_greatest
    {R S : E.State → E.State → Prop}
    (hsub : RelationLE S R) (hpres : Preserves S (Exogenous E)) :
    RelationLE S (SafeRel R (Exogenous E)) :=
  safeRel_greatest hsub hpres

/-- The exogeny-safe dynamics never adds an edge. -/
theorem safeRel_exogeny_subset (R : E.State → E.State → Prop) :
    RelationLE (SafeRel R (Exogenous E)) R :=
  safeRel_subset R (Exogenous E)

/-- The exogeny-safe dynamics preserves exogeny by construction. -/
theorem safeRel_exogeny_preserves (R : E.State → E.State → Prop) :
    Preserves (SafeRel R (Exogenous E)) (Exogenous E) :=
  safeRel_preserves R (Exogenous E)

/-! ## The payoff -/

/-- **An expired license licenses nothing.** Past the endogenization point the
echo law applies again: the state emits no licensed non-null record, however
much record mass the run accumulated getting there. -/
theorem expired_license_emits_no_licensed_record
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {R : E.State → E.State → Prop} {s y : E.State}
    (_hy : Relation.ReflTransGen R s y) (hecho : EchoAt E y) :
    ¬ ∃ r, E.licensedEmits y r ∧ E.nonnull r :=
  no_licensed_nonnull_at_echo hsound hwit hecho

/-- **The dynamic law.** For an exogenous source, either the license is
persistent and every reachable state keeps reading the object, or it expires at
a named reachable state where the echo law resumes and no licensed non-null
record is emitted. There is no third case. -/
theorem persistent_or_expired_at_named_state
    (hsound : LicensedSound E) (hwit : ObjectWitnessed E)
    {R : E.State → E.State → Prop} {s : E.State} (hs : Exogenous E s) :
    PersistentExogenous E R s
      ∨ ∃ y, Relation.ReflTransGen R s y ∧ EchoAt E y
          ∧ ¬ ∃ r, E.licensedEmits y r ∧ E.nonnull r := by
  by_cases hbox : PersistentExogenous E R s
  · exact Or.inl hbox
  · obtain ⟨y, hy, hecho⟩ := (license_expiry_iff_reachable_echo hs).mp hbox
    exact Or.inr ⟨y, hy, hecho, no_licensed_nonnull_at_echo hsound hwit hecho⟩

end OperatorKO7.Meta.BoundaryGeneral.PersistentExogeny
