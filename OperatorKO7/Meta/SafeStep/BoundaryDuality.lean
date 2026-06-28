import OperatorKO7.Kernel
import OperatorKO7.Meta.BoundaryOperator

/-!
# The orientation-distinction duality as a boundary-operator isomorphism

This is the boundary-operator-level ("LICS-grade") rung of the duality. The
ascent-profile rung (`DistinctionAscentProfile`) shows the two boundaries are
stagewise-equivalent and isomorphic as six-step ascent profiles. This module
strengthens that to a morphism in a category of boundary operators: it exhibits
each boundary as a `BoundaryOperator` carrier (with the full partiality /
irreversibility / gauge-covariance / channel / payload-discarding law
stack) and constructs an explicit isomorphism between them.

It contains no `sorry`, no new `axiom`, no `native_decide`, and no `@[csimp]`.
The public isomorphism theorem has been spot-checked with `#print axioms`
(baseline whitelist `{propext, Classical.choice, Quot.sound}`).

## Honest scope

The boundary-operator presentation captures the *collapse* essence common to both
boundaries: a partial, irreversible, payload-discarding, gauge-covariant
map to a verdict. The distinction instance collapses the diagonal
identity query to its eqW verdict `void`; the orientation instance collapses the
duplicated carrier to its projected verdict. Both instantiate the same collapse
boundary operator, differing only in the verdict, and the verdict isomorphism
(`Equiv.swap`) exhibits them as isomorphic objects. This is a boundary-operator
isomorphism of the collapse structure; it is not a claim that the full rewrite
dynamics of each system are reconstructible from the verdict. The companion module
`SafeStep.DynamicalBoundaryFunctor` now supplies the collapse-preserving dynamical
functors and proves their non-faithfulness.
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.BoundaryOperator

namespace OperatorKO7.Meta.SafeStep.BoundaryDuality

set_option linter.unusedVariables false

/-- The collapse boundary operator: every in-domain input collapses to a single
verdict `y0`, discarding its payload. Both KO7 boundaries instantiate this with
their own verdict. The five boundary-operator laws are discharged exactly as for
`toyBoundaryOperator`, with the two distinct witnesses `void` and `delta void`. -/
noncomputable def collapseBoundaryOperator (y0 : Trace) :
    BoundaryOperator (Option Trace) Trace where
  domain x := x ≠ none
  apply _ _ := y0
  gauge_group := Z2
  gauge_struct := inferInstance
  gauge_action_X _ x := x
  gauge_action_Y _ y := y
  channel := { send := fun x => match x with | some _ => some y0 | none => none }
  Payload := Trace
  payload_extract x := match x with | some a => a | none => void
  partiality := by
    intro hall
    exact (hall none) rfl
  irreversibility := by
    intro y
    rintro ⟨xh, hxy, huniq⟩
    have e0 := huniq ⟨some void, by simp⟩ hxy
    have e1 := huniq ⟨some (delta void), by simp⟩ hxy
    have hpair :
        (⟨some void, by simp⟩ : {x : Option Trace // x ≠ none})
          = ⟨some (delta void), by simp⟩ := e0.trans e1.symm
    have hv : (some void : Option Trace) = some (delta void) :=
      congrArg Subtype.val hpair
    simp at hv
  gaugeCovariance := by
    intro g x h h'
    rfl
  channelPreservation := by
    intro x hx
    cases x with
    | none => exact absurd rfl hx
    | some a => rfl
  payloadDiscarding := by
    intro hrec
    rcases hrec with ⟨recover, hrec⟩
    have h0 := hrec ⟨some void, by simp⟩
    have h1 := hrec ⟨some (delta void), by simp⟩
    simp at h0 h1
    have hbad : (void : Trace) = delta void := h0.symm.trans h1
    simp at hbad

/-- A morphism of boundary operators: carrier maps commuting with the partial
boundary action (domain preservation and apply-commutation). -/
structure BoundaryMorphism {X1 Y1 X2 Y2 : Type}
    (B1 : BoundaryOperator X1 Y1) (B2 : BoundaryOperator X2 Y2) where
  fX : X1 → X2
  fY : Y1 → Y2
  domain_map : ∀ x, B1.domain x → B2.domain (fX x)
  apply_commute : ∀ x (h : B1.domain x),
    fY (B1.apply x h) = B2.apply (fX x) (domain_map x h)

/-- The identity boundary-operator morphism. -/
def BoundaryMorphism.idMor {X Y : Type} (B : BoundaryOperator X Y) :
    BoundaryMorphism B B where
  fX := _root_.id
  fY := _root_.id
  domain_map := fun _ h => h
  apply_commute := fun _ _ => rfl

/-- Composition of boundary-operator morphisms. -/
def BoundaryMorphism.comp {X1 Y1 X2 Y2 X3 Y3 : Type}
    {B1 : BoundaryOperator X1 Y1} {B2 : BoundaryOperator X2 Y2}
    {B3 : BoundaryOperator X3 Y3}
    (g : BoundaryMorphism B2 B3) (f : BoundaryMorphism B1 B2) :
    BoundaryMorphism B1 B3 where
  fX := g.fX ∘ f.fX
  fY := g.fY ∘ f.fY
  domain_map := fun x h => g.domain_map (f.fX x) (f.domain_map x h)
  apply_commute := fun x h => by
    simp only [Function.comp_apply]
    rw [f.apply_commute x h, g.apply_commute (f.fX x) (f.domain_map x h)]

/-- The distinction (confluence) boundary as a boundary operator: the eqW diagonal
query collapses to the verdict `void`. -/
noncomputable def distinctionBoundaryOperator : BoundaryOperator (Option Trace) Trace :=
  collapseBoundaryOperator void

/-- The orientation (termination) boundary as a boundary operator: the duplicated
carrier collapses to its projected verdict, here `delta void`. -/
noncomputable def orientationBoundaryOperator : BoundaryOperator (Option Trace) Trace :=
  collapseBoundaryOperator (delta void)

/-- The verdict isomorphism exchanging the two boundaries' collapse targets. -/
noncomputable def verdictSwap : Trace → Trace := Equiv.swap void (delta void)

/-- THE BOUNDARY-OPERATOR MORPHISM from the distinction boundary to the orientation
boundary: identity on the query carrier, the verdict swap on outputs. -/
noncomputable def distinctionToOrientationBO :
    BoundaryMorphism distinctionBoundaryOperator orientationBoundaryOperator where
  fX := _root_.id
  fY := verdictSwap
  domain_map := fun _ h => h
  apply_commute := fun x h => by
    show verdictSwap void = delta void
    simp [verdictSwap]

/-- The inverse boundary-operator morphism. -/
noncomputable def orientationToDistinctionBO :
    BoundaryMorphism orientationBoundaryOperator distinctionBoundaryOperator where
  fX := _root_.id
  fY := verdictSwap
  domain_map := fun _ h => h
  apply_commute := fun x h => by
    show verdictSwap (delta void) = void
    simp [verdictSwap]

/-- THE DUALITY AS A BOUNDARY-OPERATOR ISOMORPHISM. The morphism and its inverse
compose to the identity on both carriers, so the orientation and distinction
boundaries are isomorphic objects in the category of boundary operators. -/
theorem distinction_orientation_boundary_iso :
    (∀ x, orientationToDistinctionBO.fX (distinctionToOrientationBO.fX x) = x)
      ∧ (∀ y, orientationToDistinctionBO.fY (distinctionToOrientationBO.fY y) = y) := by
  refine ⟨fun x => rfl, fun y => ?_⟩
  show verdictSwap (verdictSwap y) = y
  simp [verdictSwap]

end OperatorKO7.Meta.SafeStep.BoundaryDuality
