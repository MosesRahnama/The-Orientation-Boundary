/-!
# Direct Barrier Scope (Phase A.5)

Scope-as-record layer for the direct orientation barrier.

This module turns the manuscript's scope paragraph into a checkable Lean record
together with concrete negative witnesses for each named exclusion. The point is
boundary classification, not deep metatheory: every scope caveat in Paper A is
realized by a concrete `DirectBarrierScope` sentinel with one positive field set
to `False`, paired with a theorem witnessing `¬ InScope` for that sentinel.

The six exclusions covered are:

- sharing-aware semantics (violates `treeSemantics`),
- binder-carrying / higher-order semantics (violates `firstOrder`),
- innermost-only strategy restriction (violates `fullRewriting`),
- nonmonotone co-order route, e.g. co-rewrite pairs / co-WPO (violates `monotoneObserver`),
- Tait-Girard computability route, e.g. HORPO+CC, CPO, sized types (violates `syntacticDirect`),
- AC / equational-quotient setting (violates `noEquationalQuotient`).

Existing schema, KO7, and barrier proofs are not touched. This file adds a
parallel boundary-classification layer only.
-/

namespace OperatorKO7.StepDuplicating

/--
The direct barrier scope contract.

Each field captures one positive scope condition that the direct-orientation
no-go theorem assumes. A concrete scope sets each field to `True` if the
corresponding scope condition holds for the scenario being modelled, or to
`False` if that scenario violates the condition. The `InScope` predicate
asserts that every field of a given `DirectBarrierScope` is `True`. -/
structure DirectBarrierScope where
  /-- A position oracle is available on the term carrier. -/
  hasPositions : Prop
  /-- An occurrence counter is available for variables and payload coordinates. -/
  hasOccurrenceCounter : Prop
  /-- The duplicating rule is firable on closed terms in the scope. -/
  hasFirabilityWitness : Prop
  /-- The rewrite semantics is tree-based; no sharing, graph reduction, or
  memoization is permitted to dissolve payload duplication. -/
  treeSemantics : Prop
  /-- The rewrite setting is first-order; binders are absent. -/
  firstOrder : Prop
  /-- Rewriting is full; no innermost-only or other strategy restriction blocks
  the duplicating step from firing. -/
  fullRewriting : Prop
  /-- The candidate observer is monotone in the carrier sense; nonmonotone
  co-orders violate this direct-class contract. -/
  monotoneObserver : Prop
  /-- The proof method is syntactic-direct; it does not internalize Tait-Girard
  computability or any other typed-semantic absorption of duplication. -/
  syntacticDirect : Prop
  /-- The term algebra is not quotiented by an AC or other equational theory. -/
  noEquationalQuotient : Prop

/-- `InScope S` asserts that every scope-contract field of `S` holds. -/
structure InScope (S : DirectBarrierScope) : Prop where
  hasPositions : S.hasPositions
  hasOccurrenceCounter : S.hasOccurrenceCounter
  hasFirabilityWitness : S.hasFirabilityWitness
  treeSemantics : S.treeSemantics
  firstOrder : S.firstOrder
  fullRewriting : S.fullRewriting
  monotoneObserver : S.monotoneObserver
  syntacticDirect : S.syntacticDirect
  noEquationalQuotient : S.noEquationalQuotient

/-- The canonical fully-in-scope sentinel. All scope conditions are `True`, so
`InScope fullScope` holds. Used as a positive control to certify that the
`InScope` predicate is not vacuously empty. -/
def fullScope : DirectBarrierScope where
  hasPositions := True
  hasOccurrenceCounter := True
  hasFirabilityWitness := True
  treeSemantics := True
  firstOrder := True
  fullRewriting := True
  monotoneObserver := True
  syntacticDirect := True
  noEquationalQuotient := True

/-- `fullScope` is in scope. -/
theorem fullScope_InScope : InScope fullScope where
  hasPositions := trivial
  hasOccurrenceCounter := trivial
  hasFirabilityWitness := trivial
  treeSemantics := trivial
  firstOrder := trivial
  fullRewriting := trivial
  monotoneObserver := trivial
  syntacticDirect := trivial
  noEquationalQuotient := trivial

/-! ## Concrete negative witnesses

Each named exclusion is realized by a concrete sentinel that flips exactly one
positive field to `False`. The paired `¬ InScope` theorem follows directly via
the structure projection on `InScope`. -/

/-- Sharing-aware (graph / pointer / memoizing) semantics violates the tree
condition that makes payload duplication observable. -/
def sharingScope : DirectBarrierScope where
  hasPositions := True
  hasOccurrenceCounter := True
  hasFirabilityWitness := True
  treeSemantics := False
  firstOrder := True
  fullRewriting := True
  monotoneObserver := True
  syntacticDirect := True
  noEquationalQuotient := True

/-- The sharing sentinel violates the direct barrier scope contract. -/
theorem sharingScope_not_InScope : ¬ InScope sharingScope :=
  fun h => h.treeSemantics

/-- Binder-carrying higher-order semantics violates the first-order condition. -/
def binderScope : DirectBarrierScope where
  hasPositions := True
  hasOccurrenceCounter := True
  hasFirabilityWitness := True
  treeSemantics := True
  firstOrder := False
  fullRewriting := True
  monotoneObserver := True
  syntacticDirect := True
  noEquationalQuotient := True

/-- The binder sentinel violates the direct barrier scope contract. -/
theorem binderScope_not_InScope : ¬ InScope binderScope :=
  fun h => h.firstOrder

/-- An innermost-only strategy restriction violates full rewriting. -/
def innermostOnlyScope : DirectBarrierScope where
  hasPositions := True
  hasOccurrenceCounter := True
  hasFirabilityWitness := True
  treeSemantics := True
  firstOrder := True
  fullRewriting := False
  monotoneObserver := True
  syntacticDirect := True
  noEquationalQuotient := True

/-- The innermost-only sentinel violates the direct barrier scope contract. -/
theorem innermostOnlyScope_not_InScope : ¬ InScope innermostOnlyScope :=
  fun h => h.fullRewriting

/-- A nonmonotone co-order route, such as co-rewrite pairs or co-WPO, violates
the monotone-observer condition. -/
def coOrderScope : DirectBarrierScope where
  hasPositions := True
  hasOccurrenceCounter := True
  hasFirabilityWitness := True
  treeSemantics := True
  firstOrder := True
  fullRewriting := True
  monotoneObserver := False
  syntacticDirect := True
  noEquationalQuotient := True

/-- The co-order sentinel violates the direct barrier scope contract. -/
theorem coOrderScope_not_InScope : ¬ InScope coOrderScope :=
  fun h => h.monotoneObserver

/-- A Tait-Girard / computability-closure route (HORPO with computability
closure, CPO, sized types) absorbs payload duplication at a typed semantic
level and violates the syntactic-direct condition. -/
def computabilityScope : DirectBarrierScope where
  hasPositions := True
  hasOccurrenceCounter := True
  hasFirabilityWitness := True
  treeSemantics := True
  firstOrder := True
  fullRewriting := True
  monotoneObserver := True
  syntacticDirect := False
  noEquationalQuotient := True

/-- The Tait-Girard / computability sentinel violates the direct barrier scope contract. -/
theorem computabilityScope_not_InScope : ¬ InScope computabilityScope :=
  fun h => h.syntacticDirect

/-- An AC / equational quotient setting (rewriting modulo an equational theory)
violates the no-equational-quotient condition. -/
def acQuotientScope : DirectBarrierScope where
  hasPositions := True
  hasOccurrenceCounter := True
  hasFirabilityWitness := True
  treeSemantics := True
  firstOrder := True
  fullRewriting := True
  monotoneObserver := True
  syntacticDirect := True
  noEquationalQuotient := False

/-- The AC / equational-quotient sentinel violates the direct barrier scope contract. -/
theorem acQuotientScope_not_InScope : ¬ InScope acQuotientScope :=
  fun h => h.noEquationalQuotient

end OperatorKO7.StepDuplicating
