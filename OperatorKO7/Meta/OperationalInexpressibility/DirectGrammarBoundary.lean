import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore

/-!
# Direct-grammar operational boundary

This module gives the non-vacuous direct-grammar separation for the fixed
duplicating step and records the reusable observer-fiber obstruction behind it.
Membership in the declared grammar is represented by an indexed derivation
tree whose rules mirror the seven constructors of `MeasureExpr`; it is not a
constant propositional placeholder.

The grammar result concerns orientation-certificate adequacy for
`OrientsDupStep`. It does not assert semantic termination of an arbitrary
rewrite system.

The quotient results use the actual observer-kernel quotient from
`ObserverKernel`. The collision-to-obstruction direction is constructive. The
reverse conversion from a negated universal statement to a collision uses
classical propositional reasoning, but requires neither decidable equality nor
inhabitance. Extending a decoder away from the image of an observer separately
requires `Nonempty Verdict`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

universe u v w

/-! ## Proof-bearing formation judgment for the reflected grammar -/

/-- A typed derivation tree for membership in the declared reflected direct
grammar.  Each constructor is one formation rule, and the result index records
the exact expression derived by that rule. -/
inductive DirectGrammarDerivation : MeasureExpr → Type where
  | counter : DirectGrammarDerivation MeasureExpr.counter
  | payload : DirectGrammarDerivation MeasureExpr.payload
  | const (n : Nat) : DirectGrammarDerivation (MeasureExpr.const n)
  | add {e f : MeasureExpr}
      (left : DirectGrammarDerivation e)
      (right : DirectGrammarDerivation f) :
      DirectGrammarDerivation (MeasureExpr.add e f)
  | mul {e f : MeasureExpr}
      (left : DirectGrammarDerivation e)
      (right : DirectGrammarDerivation f) :
      DirectGrammarDerivation (MeasureExpr.mul e f)
  | max {e f : MeasureExpr}
      (left : DirectGrammarDerivation e)
      (right : DirectGrammarDerivation f) :
      DirectGrammarDerivation (MeasureExpr.max e f)
  | smul (n : Nat) {e : MeasureExpr}
      (body : DirectGrammarDerivation e) :
      DirectGrammarDerivation (MeasureExpr.smul n e)

/-- Propositional interface to the typed derivation tree, suitable for the
`OperationalQuestion.derivable` field. -/
def DirectGrammarDerivable (e : MeasureExpr) : Prop :=
  Nonempty (DirectGrammarDerivation e)

/-- Structural coverage: recursion on an expression constructs its complete
formation derivation. -/
def directGrammarDerivation :
    (e : MeasureExpr) → DirectGrammarDerivation e
  | .counter => .counter
  | .payload => .payload
  | .const n => .const n
  | .add e f => .add (directGrammarDerivation e) (directGrammarDerivation f)
  | .mul e f => .mul (directGrammarDerivation e) (directGrammarDerivation f)
  | .max e f => .max (directGrammarDerivation e) (directGrammarDerivation f)
  | .smul n e => .smul n (directGrammarDerivation e)

/-- Every already formed `MeasureExpr` statement has a concrete formation
tree.  This is the coverage theorem used by the KO7 operational question. -/
theorem directGrammarDerivable_complete (e : MeasureExpr) :
    DirectGrammarDerivable e :=
  ⟨directGrammarDerivation e⟩

/-! ## Non-vacuous fixed-duplicator grammar separation -/

/-- A direct grammar expression uses the payload exactly when its denotation is
not payload-blind. -/
def UsesPayload (e : MeasureExpr) : Prop :=
  Not (PayloadBlind e.eval)

/-- Adequacy here means strict orientation of the exact counter-drop,
payload-duplicating step encoded by `OrientsDupStep`. -/
def AdequateForDupOrientation (e : MeasureExpr) : Prop :=
  OrientsDupStep e.eval

/-- The payload projection genuinely reads the payload coordinate. -/
theorem payload_usesPayload : UsesPayload MeasureExpr.payload :=
  unbounded_not_payload_blind MeasureExpr.payload payload_payloadUnbounded

/-- The payload projection does not orient the fixed duplicating step. -/
theorem payload_not_adequateForDupOrientation :
    Not (AdequateForDupOrientation MeasureExpr.payload) :=
  payload_blocked

/-- The counter projection orients the fixed duplicating step. -/
theorem counter_adequateForDupOrientation :
    AdequateForDupOrientation MeasureExpr.counter :=
  counter_orients

/-- The counter projection does not use the payload coordinate. -/
theorem counter_not_usesPayload : Not (UsesPayload MeasureExpr.counter) := by
  intro huses
  exact huses counter_is_payload_blind

/-- No expression in the generated direct grammar both reads the payload and
orients the exact fixed duplicating step. -/
theorem no_directGrammar_measure_usesPayload_and_orients :
    forall e : MeasureExpr,
      Not (UsesPayload e ∧ AdequateForDupOrientation e) := by
  intro e hboth
  exact hboth.1 (orients_implies_payload_blind e hboth.2)

/-- Soundness of the formation judgment for the direct-grammar boundary: a
derived grammar expression cannot simultaneously read the payload coordinate
and orient the duplicating step.  The derivation argument is the explicit
scope certificate for the statement. -/
theorem DirectGrammarDerivation.no_payload_orientation
    {e : MeasureExpr} (_derivation : DirectGrammarDerivation e) :
    Not (UsesPayload e ∧ AdequateForDupOrientation e) :=
  no_directGrammar_measure_usesPayload_and_orients e

/-- Prop-level soundness bridge used by `OperationalQuestion`: derivability
through a typed formation tree entails the direct-grammar separation. -/
theorem directGrammarDerivable_no_payload_orientation
    {e : MeasureExpr} (hDerivable : DirectGrammarDerivable e) :
    Not (UsesPayload e ∧ AdequateForDupOrientation e) := by
  obtain ⟨derivation⟩ := hDerivable
  exact derivation.no_payload_orientation

/-- The payload-sensitive side of the separation is inhabited by the grammar's
payload projection. -/
theorem payload_side_nonempty :
    exists e : MeasureExpr,
      UsesPayload e ∧ Not (AdequateForDupOrientation e) :=
  ⟨MeasureExpr.payload, payload_usesPayload,
    payload_not_adequateForDupOrientation⟩

/-- The orienting, payload-blind side of the separation is inhabited by the
grammar's counter projection. -/
theorem target_side_nonempty :
    exists e : MeasureExpr,
      AdequateForDupOrientation e ∧ Not (UsesPayload e) :=
  ⟨MeasureExpr.counter, counter_adequateForDupOrientation,
    counter_not_usesPayload⟩


/-! ## Observer-target core

The generic observer/target definitions and quotient-factorization theorems are provided by
`ObserverTargetCore.lean` and re-exported through this import. -/


/-! ## Transfer to another grammar

The universal reading of the boundary asks what happens to a direct-measure syntax other than
`MeasureExpr`. Two statements are available, and they carry different weight.

The presentational one quantifies over a predicate on `MeasureExpr` itself. Its hypothesis is
satisfied by every predicate that agrees with the derivability judgment, and
`directGrammarDerivable_complete` makes that judgment total, so the hypothesis constrains
nothing: the conclusion already holds for every expression. It is recorded because the paper's
transfer sentence is phrased that way.

The load-bearing one quantifies over an arbitrary carrier with an arbitrary denotation and asks
that every denotation be realized in the reflected grammar. That hypothesis is necessary:
`payloadSensitiveOrienter` reads the payload and orients the duplicating step, so a syntax that
denotes it escapes the boundary, and `denotational_subgrammar_premise_necessary` compiles the
failure of the unrestricted statement. -/

/-- A measure that reads the payload coordinate and still orients the duplicating step. It sits
outside the reflected grammar by `orients_implies_payload_blind`. -/
def payloadSensitiveOrienter : Nat → Nat → Nat :=
  fun c p => if p = 0 then 2 * c + 1 else 2 * c

theorem payloadSensitiveOrienter_orients : OrientsDupStep payloadSensitiveOrienter := by
  intro c p L hL
  unfold payloadSensitiveOrienter
  have hpL : p + L ≠ 0 := by omega
  simp only [hpL, if_false]
  by_cases hp : p = 0 <;> simp [hp]
  omega

theorem payloadSensitiveOrienter_not_payloadBlind :
    ¬ PayloadBlind payloadSensitiveOrienter := by
  intro h
  have := h 0 0 1
  unfold payloadSensitiveOrienter at this
  simp at this

/-- The witness is denotable in no reflected grammar expression. -/
theorem payloadSensitiveOrienter_not_grammar_denotable :
    ¬ ∃ e : MeasureExpr, e.eval = payloadSensitiveOrienter := by
  rintro ⟨e, he⟩
  have hor : OrientsDupStep e.eval := by rw [he]; exact payloadSensitiveOrienter_orients
  have hblind : PayloadBlind e.eval := orients_implies_payload_blind e hor
  rw [he] at hblind
  exact payloadSensitiveOrienter_not_payloadBlind hblind

/-- **Transfer, load-bearing form.** Any direct-measure syntax whose every denotation is realized
in the reflected grammar inherits the boundary: no expression of that syntax both reads the
payload and orients the duplicating step. -/
theorem no_payload_orientation_of_denotational_subgrammar
    {E : Type u} (ev : E → Nat → Nat → Nat)
    (hsub : ∀ x : E, ∃ e : MeasureExpr, ev x = e.eval) (x : E) :
    ¬ (¬ PayloadBlind (ev x) ∧ OrientsDupStep (ev x)) := by
  rintro ⟨hpay, hor⟩
  obtain ⟨e, he⟩ := hsub x
  rw [he] at hpay hor
  exact hpay (orients_implies_payload_blind e hor)

/-- The realization hypothesis of the transfer theorem is load-bearing: dropping it makes the
statement false, witnessed by `payloadSensitiveOrienter` on a one-point carrier. -/
theorem denotational_subgrammar_premise_necessary :
    ¬ ∀ (E : Type) (ev : E → Nat → Nat → Nat) (x : E),
        ¬ (¬ PayloadBlind (ev x) ∧ OrientsDupStep (ev x)) := by
  intro h
  exact h Unit (fun _ => payloadSensitiveOrienter) ()
    ⟨payloadSensitiveOrienter_not_payloadBlind, payloadSensitiveOrienter_orients⟩

/-- **Transfer, presentational form.** A predicate on grammar expressions that agrees with the
derivability judgment inherits the separation. The hypothesis is presentational: by
`directGrammarDerivable_complete` the judgment is total on `MeasureExpr`, so the conclusion holds
for every predicate. The statement with content is
`no_payload_orientation_of_denotational_subgrammar`. -/
theorem no_payload_orientation_of_same_grammar
    (D : MeasureExpr → Prop) (h : ∀ e, D e ↔ DirectGrammarDerivable e) :
    ∀ e : MeasureExpr, D e → ¬ (UsesPayload e ∧ AdequateForDupOrientation e) := by
  intro e he
  exact directGrammarDerivable_no_payload_orientation ((h e).1 he)

end OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
