import OperatorKO7.Meta.BoundaryOperator.UniversalFramework

/-!
# Predicate transport along boundary-operator morphisms

A barrier is the proposition `¬ Reaches B Q`. This module proves two facts for
the maps and commuting equation stored in a `BoundaryMorphism`:

* reachability pushes **forward** along a morphism (`Reaches.push`), and
* a barrier on the target operator pulls **back** to a barrier on the source
  (`barrier_reflect`).

`barrier_reflect` concerns the pulled-back predicate `Q ∘ fY`. Its proof uses
`fX`, domain preservation, and the stored output-commuting equation. The file
introduces neither category structure nor injectivity assumptions.

For every supplied domain witness, the toy boundary operator outputs `false`.
This yields a barrier against `(· = true)` and its pullback through the identity
endomorphism.

## Formal scope

```
Relation: transport of an output-reachability predicate through a BoundaryMorphism.
Closure:  one forward implication and its contrapositive.
Trust:    kernel-checked constructive proofs.
Scope:    boundary operators related by the supplied morphism fields, plus the
          conditional toy-domain barrier.
```
-/

set_option linter.dupNamespace false

namespace OperatorKO7.Meta.BoundaryOperator.UniversalFramework

/-- `Reaches B Q`: some domain witness for `B` produces an output satisfying
`Q`. A barrier has type `¬ Reaches B Q`. -/
def Reaches {X Y : Type*} (B : BoundaryOperator X Y) (Q : Y → Prop) : Prop :=
  ∃ x, ∃ h : B.domain x, Q (B.apply x h)

/-- Reachability pushes forward along a morphism: if `B` reaches the `fY`-pullback
of `Q`, then `B'` reaches `Q`. The witness travels along `fX`; the output equation
is the morphism's commuting square. -/
theorem Reaches.push {X Y X' Y' : Type*}
    {B : BoundaryOperator X Y} {B' : BoundaryOperator X' Y'}
    (φ : BoundaryMorphism B B') {Q : Y' → Prop}
    (h : Reaches B (fun y => Q (φ.fY y))) : Reaches B' Q := by
  obtain ⟨x, hx, hQ⟩ := h
  exact ⟨φ.fX x, φ.domain_preserve x hx, by
    rw [← φ.apply_commute x hx]; exact hQ⟩

/-- Contrapositive of `Reaches.push`: a barrier on `B'` against `Q` pulls back
to a barrier on `B` against `Q ∘ fY`. -/
theorem barrier_reflect {X Y X' Y' : Type*}
    {B : BoundaryOperator X Y} {B' : BoundaryOperator X' Y'}
    (φ : BoundaryMorphism B B') {Q : Y' → Prop}
    (hbar : ¬ Reaches B' Q) : ¬ Reaches B (fun y => Q (φ.fY y)) :=
  fun hreach => hbar (Reaches.push φ hreach)

/-- Every hypothetical toy-domain witness reaching `(· = true)` contradicts
the toy operator's `false` output equation. -/
theorem toy_never_outputs_true :
    ¬ Reaches toyBoundaryOperator (fun y => y = true) := by
  rintro ⟨x, hx, hQ⟩
  cases x with
  | none => exact toyBoundaryOperator_domain_none hx
  | some b =>
      rw [toyBoundaryOperator_apply_some b hx] at hQ
      simp at hQ

/-- Pull back the toy output barrier along the identity endomorphism. -/
theorem toy_barrier_reflects :
    ¬ Reaches toyBoundaryOperator
      (fun y => (fun y' => y' = true) (toyEndomorphism.fY y)) :=
  barrier_reflect toyEndomorphism toy_never_outputs_true

/-- String identifier for the predicate-pullback theorem. -/
def barrier_transport_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalFramework.barrier_reflect"

end OperatorKO7.Meta.BoundaryOperator.UniversalFramework
