import Mathlib

/-!
# Boundary Operator Core

This module introduces the WS-D boundary-operator carrier as a theorem-facing
execution object. The surrounding procedure specification names several carriers that
do not yet exist in the Lean tree, so this file lands the smallest honest local
versions needed to support the boundary operator and its first transport layers.

The payload-discarding law is encoded as global non-recoverability rather than a
pointwise negated existence statement. The pointwise statement would be
inconsistent for any inhabited payload type because a constant recovery map would
trivially satisfy it at a single output.
-/

namespace OperatorKO7.Meta.BoundaryOperator

universe u v

/-- The current WS-D thermodynamic carrier. -/
abbrev KineticEnergy : Type := ℝ

/-- Minimal observable payload used by the licensed-quotient surface. -/
structure Observable where
  label : String
  deriving DecidableEq, Repr

/-- Minimal channel surface needed by the boundary operator and the
pre-entanglement transport. -/
structure Channel (X : Type u) (Y : Type v) where
  send : X → Option Y
  preserves_isolation : Prop := False

/-- Meta-layer target used by the pre-entanglement transport surface. -/
inductive MetaLayer
  | verdict
  deriving DecidableEq, Repr

/-- Named placeholder for the licensed negative-separation witness required by
the licensed-quotient factorization surface. -/
structure LawvereYanofskyNegativeSeparation where
  obstruction : Prop
  holds : obstruction

/-- The WS-D boundary-operator carrier. The six laws are carried as proof
fields so the module remains theorem-facing without introducing standalone
assumption declarations. -/
structure BoundaryOperator (X : Type u) (Y : Type v) where
  domain : X → Prop
  apply : (x : X) → domain x → Y
  gauge_group : Type u
  gauge_struct : Group gauge_group
  gauge_action_X : gauge_group → X → X
  gauge_action_Y : gauge_group → Y → Y
  channel : Channel X Y
  Payload : Type v
  payload_extract : X → Payload
  landauer_cost : (x : X) → domain x → KineticEnergy
  kB : ℝ
  temperature : ℝ
  partiality : ¬ ∀ x : X, domain x
  irreversibility :
    ∀ y : Y, ¬ ∃! xh : {x : X // domain x}, apply xh.1 xh.2 = y
  gaugeCovariance :
    ∀ g : gauge_group, ∀ x : X, ∀ h : domain x,
      ∀ h' : domain (gauge_action_X g x),
        apply (gauge_action_X g x) h' = gauge_action_Y g (apply x h)
  channelPreservation :
    ∀ x : X, ∀ h : domain x,
      channel.send x = some (apply x h)
  payloadDiscarding :
    ¬ ∃ recover : Y → Payload,
        ∀ xh : {x : X // domain x},
          recover (apply xh.1 xh.2) = payload_extract xh.1
  landauerCost :
    ∀ x : X, ∀ h : domain x,
      kB * temperature * Real.log 2 ≤ landauer_cost x h

attribute [instance] BoundaryOperator.gauge_struct

/-- Domain-restricted points of a boundary operator. -/
abbrev DomainPoint {X : Type u} {Y : Type v} (B : BoundaryOperator X Y) : Type u :=
  {x : X // B.domain x}

theorem partiality_holds {X : Type u} {Y : Type v} (B : BoundaryOperator X Y) :
    ¬ ∀ x : X, B.domain x :=
  B.partiality

theorem irreversibility_holds {X : Type u} {Y : Type v} (B : BoundaryOperator X Y)
    (y : Y) :
    ¬ ∃! xh : DomainPoint B, B.apply xh.1 xh.2 = y :=
  B.irreversibility y

theorem gaugeCovariance_holds {X : Type u} {Y : Type v} (B : BoundaryOperator X Y)
    (g : B.gauge_group) (x : X) (h : B.domain x)
    (h' : B.domain (B.gauge_action_X g x)) :
    B.apply (B.gauge_action_X g x) h' = B.gauge_action_Y g (B.apply x h) :=
  B.gaugeCovariance g x h h'

theorem channelPreservation_holds {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) (x : X) (h : B.domain x) :
    B.channel.send x = some (B.apply x h) :=
  B.channelPreservation x h

theorem payloadDiscarding_holds {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) :
    ¬ ∃ recover : Y → B.Payload,
        ∀ xh : DomainPoint B,
          recover (B.apply xh.1 xh.2) = B.payload_extract xh.1 :=
  B.payloadDiscarding

theorem landauerCost_holds {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) (x : X) (h : B.domain x) :
    B.kB * B.temperature * Real.log 2 ≤ B.landauer_cost x h :=
  B.landauerCost x h

/-- The two-element gauge group used by the finite non-vacuous toy example. -/
inductive Z2
  | id
  | flip
  deriving DecidableEq, Repr

namespace Z2

instance : Group Z2 where
  mul
    | .id, h => h
    | .flip, .id => .flip
    | .flip, .flip => .id
  one := .id
  inv
    | .id => .id
    | .flip => .flip
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by
    cases a <;> rfl
  mul_one a := by
    cases a <;> rfl
  inv_mul_cancel a := by
    cases a <;> rfl

/-- The nontrivial action swaps the two live points and fixes the outside-domain point. -/
def actOptionBool : Z2 → Option Bool → Option Bool
  | .id, x => x
  | .flip, none => none
  | .flip, some b => some (!b)

/-- The toy output action is trivial because the toy connector collapses both live
inputs to the same output. -/
def actBool (_ : Z2) (y : Bool) : Bool := y

end Z2

/-- The toy execution channel returns the unique live verdict on the live domain
and is silent outside it. -/
def toyChannel : Channel (Option Bool) Bool where
  send
    | some _ => some false
    | none => none
  preserves_isolation := False

/-- A smallest non-vacuous concrete boundary operator. Two live inputs collapse
to one observable output, which makes irreversibility and payload discarding
theorem-backed rather than vacuous. -/
noncomputable def toyBoundaryOperator : BoundaryOperator (Option Bool) Bool where
  domain x := x ≠ none
  apply _ _ := false
  gauge_group := Z2
  gauge_struct := inferInstance
  gauge_action_X := Z2.actOptionBool
  gauge_action_Y := Z2.actBool
  channel := toyChannel
  Payload := Bool
  payload_extract
    | some b => b
    | none => false
  landauer_cost _ _ := Real.log 2
  kB := 1
  temperature := 1
  partiality := by
    intro hall
    exact hall none rfl
  irreversibility := by
    intro y
    cases y with
    | false =>
        intro huniq
        rcases huniq with ⟨xh, hxout, hunique⟩
        let x0 : {x : Option Bool // x ≠ none} := ⟨some false, by simp⟩
        let x1 : {x : Option Bool // x ≠ none} := ⟨some true, by simp⟩
        have hx0 : false = false := rfl
        have hx1 : false = false := rfl
        have hx0eq : x0 = xh := hunique x0 hx0
        have hx1eq : x1 = xh := hunique x1 hx1
        have hsame : x0 = x1 := hx0eq.trans hx1eq.symm
        have hvals : (some false : Option Bool) = some true := congrArg Subtype.val hsame
        simp at hvals
    | true =>
        intro huniq
        rcases huniq with ⟨xh, hxout, _⟩
        cases xh with
        | mk x hx =>
            cases x <;> simp at hxout
  gaugeCovariance := by
    intro g x h h'
    cases g <;> cases x <;> rfl
  channelPreservation := by
    intro x h
    cases x <;> simp [toyChannel] at h ⊢
  payloadDiscarding := by
    intro hrecover
    rcases hrecover with ⟨recover, hrecover⟩
    have h0 := hrecover ⟨some false, by simp⟩
    have h1 := hrecover ⟨some true, by simp⟩
    simp at h0 h1
    have : false = true := h0.symm.trans h1
    simp at this
  landauerCost := by
    intro x h
    have hlog : 0 ≤ Real.log 2 := by
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith

@[simp] theorem toyBoundaryOperator_domain_none :
    ¬ toyBoundaryOperator.domain none := by
  simp [toyBoundaryOperator]

@[simp] theorem toyBoundaryOperator_domain_some (b : Bool) :
    toyBoundaryOperator.domain (some b) := by
  simp [toyBoundaryOperator]

@[simp] theorem toyBoundaryOperator_apply_some (b : Bool)
    (h : toyBoundaryOperator.domain (some b)) :
    toyBoundaryOperator.apply (some b) h = false := rfl

def toyBoundaryOperator_two_live_inputs :
    DomainPoint toyBoundaryOperator :=
  ⟨some false, by simp [toyBoundaryOperator]⟩

def toyBoundaryOperator_second_live_input :
    DomainPoint toyBoundaryOperator :=
  ⟨some true, by simp [toyBoundaryOperator]⟩

end OperatorKO7.Meta.BoundaryOperator
