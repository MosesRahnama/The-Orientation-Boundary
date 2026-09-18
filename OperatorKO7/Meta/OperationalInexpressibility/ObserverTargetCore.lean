import OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

/-!
# Observer-target recovery core

This module contains the observer/target statements used by Operational Inexpressibility.
It depends only on the observer-kernel quotient layer and Mathlib through that layer.
Concrete rewrite systems and recursor rules are absent from this dependency path.

Relation: equality on observer fibers.
Property: target factorization, collision, and quotient recovery.
Trust: kernel-only; the classical collision normalization is isolated in its theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

universe u v w

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

/-- Fiber constancy yields a total decoder without any inhabitance hypothesis on the verdict
type when the observer is surjective.  Surjectivity removes the off-image branch that required a
fallback verdict in `verdictDeterminedBy_of_factorsThrough`. -/
theorem verdictDeterminedBy_of_factorsThrough_of_surjective
    {World : Type u} {Observation : Type v} {Verdict : Type w}
    (observe : World -> Observation) (target : World -> Verdict)
    (hsurjective : Function.Surjective observe) :
    FactorsThrough observe target -> VerdictDeterminedBy observe target := by
  classical
  intro hfactor
  let decide : Observation -> Verdict := fun observation =>
    target (Classical.choose (hsurjective observation))
  refine ⟨decide, ?_⟩
  intro world
  exact hfactor (Classical.choose_spec (hsurjective (observe world)))

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

/-- For a surjective observer, total decoder existence and observer-fiber constancy coincide with
no assumption on either carrier. -/
theorem verdictDeterminedBy_iff_factorsThrough_of_surjective
    {World : Type u} {Observation : Type v} {Verdict : Type w}
    (observe : World -> Observation) (target : World -> Verdict)
    (hsurjective : Function.Surjective observe) :
    VerdictDeterminedBy observe target ↔ FactorsThrough observe target := by
  constructor
  · exact factorsThrough_of_verdictDeterminedBy observe target
  · exact verdictDeterminedBy_of_factorsThrough_of_surjective observe target hsurjective

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
