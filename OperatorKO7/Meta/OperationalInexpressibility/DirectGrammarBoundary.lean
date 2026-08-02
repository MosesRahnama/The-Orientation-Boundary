import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

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

/-! ## Observer-fiber obstruction -/

/-- A verdict is determined by an observer when a total decoder recovers the
verdict on every observed world. Values of the decoder away from the observer
image remain part of the total function. -/
def VerdictDeterminedBy {World : Type u} {Observation : Type v}
    {Verdict : Type w} (observe : World -> Observation)
    (target : World -> Verdict) : Prop :=
  exists decide : Observation -> Verdict,
    forall world, decide (observe world) = target world

/-- A concrete collision: two worlds have the same observation and distinct
target verdicts. -/
def OperationallyInexpressibleAt {World : Type u} {Observation : Type v}
    {Verdict : Type w} (observe : World -> Observation)
    (target : World -> Verdict) (w1 w2 : World) : Prop :=
  observe w1 = observe w2 ∧ target w1 ≠ target w2

/-- A concrete observer collision constructively refutes fiber constancy. -/
theorem not_factorsThrough_of_collision
    {World : Type u} {Observation : Type v} {Verdict : Type w}
    {observe : World -> Observation} {target : World -> Verdict}
    {w1 w2 : World}
    (hcollision : OperationallyInexpressibleAt observe target w1 w2) :
    Not (FactorsThrough observe target) := by
  intro hfactor
  exact hcollision.2 (hfactor hcollision.1)

/-- Fiber non-constancy is equivalent to an explicit collision. The
right-to-left direction is constructive. The left-to-right direction is the
isolated classical normalization of a negated universal proposition. No
decidable-equality or inhabitance assumption is used. -/
theorem not_factorsThrough_iff_exists_collision
    {World : Type u} {Observation : Type v} {Verdict : Type w}
    (observe : World -> Observation) (target : World -> Verdict) :
    Not (FactorsThrough observe target) ↔
      exists w1 w2,
        OperationallyInexpressibleAt observe target w1 w2 := by
  classical
  constructor
  · intro hnot
    by_contra hcollision
    apply hnot
    intro x y hobserve
    by_contra htarget
    exact hcollision ⟨x, y, hobserve, htarget⟩
  · rintro ⟨w1, w2, hcollision⟩
    exact not_factorsThrough_of_collision hcollision

/-- Every total observation decoder makes the target constant on observer
fibers. -/
theorem factorsThrough_of_verdictDeterminedBy
    {World : Type u} {Observation : Type v} {Verdict : Type w}
    (observe : World -> Observation) (target : World -> Verdict) :
    VerdictDeterminedBy observe target -> FactorsThrough observe target := by
  rintro ⟨decide, hdecide⟩ x y hobserve
  calc
    target x = decide (observe x) := (hdecide x).symm
    _ = decide (observe y) := congrArg decide hobserve
    _ = target y := hdecide y

/-- Fiber constancy yields a total decoder once the verdict type supplies a
fallback value for observations outside the image. The choice of an image
representative is the explicitly classical step. -/
theorem verdictDeterminedBy_of_factorsThrough
    {World : Type u} {Observation : Type v} {Verdict : Type w}
    [Nonempty Verdict]
    (observe : World -> Observation) (target : World -> Verdict) :
    FactorsThrough observe target -> VerdictDeterminedBy observe target := by
  classical
  intro hfactor
  let decide : Observation -> Verdict := fun observation =>
    if himage : exists world, observe world = observation then
      target (Classical.choose himage)
    else
      Classical.choice (inferInstance : Nonempty Verdict)
  refine ⟨decide, ?_⟩
  intro world
  have himage : exists world', observe world' = observe world := ⟨world, rfl⟩
  simp only [decide, dif_pos himage]
  exact hfactor (Classical.choose_spec himage)

/-- With an inhabited verdict type, total decoder existence and observer-fiber
constancy coincide. -/
theorem verdictDeterminedBy_iff_factorsThrough
    {World : Type u} {Observation : Type v} {Verdict : Type w}
    [Nonempty Verdict]
    (observe : World -> Observation) (target : World -> Verdict) :
    VerdictDeterminedBy observe target ↔ FactorsThrough observe target := by
  constructor
  · exact factorsThrough_of_verdictDeterminedBy observe target
  · exact verdictDeterminedBy_of_factorsThrough observe target

/-! ## Actual quotient factorization -/

/-- Factorization through the actual observer-kernel quotient. Unlike a total
decoder on all observations, this interface contains only quotient classes
represented by worlds. -/
def QuotientFactorization {World : Type u} {Observation : Type v}
    {Verdict : Type w} (observe : World -> Observation)
    (target : World -> Verdict) : Prop :=
  exists decode : ObserverQuotient observe -> Verdict,
    forall world, decode (quotientMap observe world) = target world

/-- Quotient factorization is exactly observer-fiber constancy, with no
inhabitance assumption on the verdict type. -/
theorem quotientFactorization_iff_factorsThrough
    {World : Type u} {Observation : Type v} {Verdict : Type w}
    (observe : World -> Observation) (target : World -> Verdict) :
    QuotientFactorization observe target ↔ FactorsThrough observe target := by
  constructor
  · rintro ⟨decode, hdecode⟩ x y hobserve
    calc
      target x = decode (quotientMap observe x) := (hdecode x).symm
      _ = decode (quotientMap observe y) :=
        congrArg decode ((quotientMap_eq_iff observe x y).2 hobserve)
      _ = target y := hdecode y
  · intro hfactor
    refine ⟨factor observe target hfactor, ?_⟩
    intro world
    exact factor_quotientMap observe target hfactor world

/-- Failure of factorization through the actual observer quotient is exactly
the existence of an observer collision with distinct target verdicts. -/
theorem quotient_factorization_failure_iff_collision
    {World : Type u} {Observation : Type v} {Verdict : Type w}
    (observe : World -> Observation) (target : World -> Verdict) :
    Not (QuotientFactorization observe target) ↔
      exists w1 w2,
        OperationallyInexpressibleAt observe target w1 w2 := by
  constructor
  · intro hquotient
    apply (not_factorsThrough_iff_exists_collision observe target).1
    intro hfactor
    exact hquotient
      ((quotientFactorization_iff_factorsThrough observe target).2 hfactor)
  · intro hcollision hquotient
    have hfactor : FactorsThrough observe target :=
      (quotientFactorization_iff_factorsThrough observe target).1 hquotient
    exact ((not_factorsThrough_iff_exists_collision observe target).2
      hcollision) hfactor

/-! ## Regression fixture for the missing-inhabitance defect -/

/-- Empty-world observer from the blocking counterexample. -/
def emptyWorldObserve (world : Empty) : Unit :=
  Empty.elim world

/-- Empty-world verdict from the blocking counterexample. -/
def emptyWorldTarget (world : Empty) : Empty :=
  world

/-- The empty-world target is vacuously constant on observer fibers. -/
theorem emptyWorldTarget_factorsThrough :
    FactorsThrough emptyWorldObserve emptyWorldTarget := by
  intro x y _
  exact Empty.elim x

/-- There is no collision when the world type is empty. -/
theorem emptyWorldTarget_has_no_collision :
    Not (exists w1 w2,
      OperationallyInexpressibleAt emptyWorldObserve emptyWorldTarget w1 w2) := by
  rintro ⟨w1, w2, hcollision⟩
  exact Empty.elim w1

/-- Despite the absence of a collision, no total `Unit -> Empty` decoder
exists. This is the concrete regression witness showing why the decoder
biconditional needs `Nonempty Verdict`. -/
theorem emptyWorldTarget_not_verdictDeterminedBy :
    Not (VerdictDeterminedBy emptyWorldObserve emptyWorldTarget) := by
  rintro ⟨decide, _hdecide⟩
  exact Empty.elim (decide ())

end OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
