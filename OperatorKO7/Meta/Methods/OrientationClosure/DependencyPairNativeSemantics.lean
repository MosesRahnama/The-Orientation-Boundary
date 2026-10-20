import OperatorKO7.Meta.Methods.DependencyPairTypedRows
import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
import Mathlib.Data.Prod.Lex

/-!
# Native dependency-pair semantics for ORI-4

The method data below separates extraction, pair processing and source
termination. Reduction pairs are relations with weak and strict laws. Two
concrete pairs induce different strict relations. A separate source bridge is
required to recover source termination, so dependency-pair descent alone does
not imply source termination.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.DependencyPairNativeSemantics

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.Methods.DependencyPairTypedRows
open OperatorKO7.HigherOrderRewritingSyntax

/-! ## Same-system extraction -/

/-- Source relation, transformed-call relation and an extractor binding every
pair edge to a source edge of the same problem. -/
structure SameSystemDPProblem (α : Type) where
  sourceStep : α -> α -> Prop
  pairStep : α -> α -> Prop
  extractedFromSource : forall {a c}, pairStep a c -> ∃ rhs, sourceStep a rhs

/-- KO7 pair extraction is tied to the actual recursor-successor root step. -/
def ko7SameSystemDPProblem : SameSystemDPProblem Trace where
  sourceStep := Step
  pairStep := DPPair
  extractedFromSource := by
    intro a c h
    cases h with
    | rec_succ b s n =>
        exact ⟨app s (recΔ b s n), Step.R_rec_succ b s n⟩

/-- The pair target is the recursive call; the source rewrite target is the
emitted application containing that call. -/
theorem ko7_pair_and_rewrite_targets_are_distinct :
    (recΔ void void void : Trace) ≠ app void (recΔ void void void) := by
  decide

/-- Extraction retains the recursive call and records the corresponding root
rewrite target separately. -/
theorem ko7_pair_has_same_system_source
    {a c : Trace} (h : DPPair a c) :
    ∃ rhs, Step a rhs :=
  ko7SameSystemDPProblem.extractedFromSource h

/-! ## Relation-valued reduction pairs -/

/-- A reduction pair with an actual weak relation and strict relation. -/
structure NativeReductionPair where
  weak : Trace -> Trace -> Prop
  strict : Trace -> Trace -> Prop
  weak_refl : Reflexive weak
  weak_trans : Transitive weak
  strict_trans : Transitive strict
  weak_strict : forall {a b c}, weak a b -> strict b c -> strict a c
  strict_weak : forall {a b c}, strict a b -> weak b c -> strict a c
  strict_reverse_wellFounded : WellFounded (fun a b => strict b a)
  rules_weak : forall {a b}, Step a b -> weak a b
  pairs_strict : forall {a b}, DPPair a b -> strict a b

/-- Polynomial weight decreases on every dependency pair by at least two. -/
theorem W_dppair_gap_two {a b : Trace} (h : DPPair a b) :
    OperatorKO7.PolyInterpretation.W b + 2 <=
      OperatorKO7.PolyInterpretation.W a := by
  cases h with
  | rec_succ base payload counter =>
      have hb := OperatorKO7.PolyInterpretation.W_pos base
      have hs := OperatorKO7.PolyInterpretation.W_pos payload
      simp only [OperatorKO7.PolyInterpretation.W]
      nlinarith

/-- Standard strict polynomial reduction pair. -/
def polynomialReductionPair : NativeReductionPair where
  weak := fun a b => OperatorKO7.PolyInterpretation.W b <= OperatorKO7.PolyInterpretation.W a
  strict := fun a b => OperatorKO7.PolyInterpretation.W b < OperatorKO7.PolyInterpretation.W a
  weak_refl := fun _ => le_rfl
  weak_trans := by
    intro a b c hab hbc
    exact hbc.trans hab
  strict_trans := by
    intro a b c hab hbc
    exact hbc.trans hab
  weak_strict := by
    intro a b c hab hbc
    exact hbc.trans_le hab
  strict_weak := by
    intro a b c hab hbc
    exact hbc.trans_lt hab
  strict_reverse_wellFounded :=
    InvImage.wf OperatorKO7.PolyInterpretation.W Nat.lt_wfRel.wf
  rules_weak := fun h => Nat.le_of_lt (OperatorKO7.PolyInterpretation.W_orients_step h)
  pairs_strict := by
    intro a b h
    have hg := W_dppair_gap_two h
    omega

/-- A second reduction pair requires a weight gap of at least two. It uses the
same weak order but a different strict relation. -/
def gapTwoReductionPair : NativeReductionPair where
  weak := fun a b => OperatorKO7.PolyInterpretation.W b <= OperatorKO7.PolyInterpretation.W a
  strict := fun a b => OperatorKO7.PolyInterpretation.W b + 2 <= OperatorKO7.PolyInterpretation.W a
  weak_refl := fun _ => le_rfl
  weak_trans := by
    intro a b c hab hbc
    exact hbc.trans hab
  strict_trans := by
    intro a b c hab hbc
    omega
  weak_strict := by
    intro a b c hab hbc
    omega
  strict_weak := by
    intro a b c hab hbc
    omega
  strict_reverse_wellFounded := by
    apply Subrelation.wf
      (r := fun a b : Trace => OperatorKO7.PolyInterpretation.W a <
        OperatorKO7.PolyInterpretation.W b)
    · intro a b h
      omega
    · exact InvImage.wf OperatorKO7.PolyInterpretation.W Nat.lt_wfRel.wf
  rules_weak := fun h => Nat.le_of_lt (OperatorKO7.PolyInterpretation.W_orients_step h)
  pairs_strict := W_dppair_gap_two

/-- The induced strict relations differ, rather than merely their rank
functions. -/
theorem nativeReductionPairs_relations_differ :
    polynomialReductionPair.strict (delta void) void ∧
      Not (gapTwoReductionPair.strict (delta void) void) := by
  constructor <;> simp [polynomialReductionPair, gapTwoReductionPair,
    OperatorKO7.PolyInterpretation.W]

/-- Every native reduction pair certifies well-foundedness of the transformed
pair problem by its own strict relation. -/
theorem pair_wellFounded_of_nativeReductionPair (R : NativeReductionPair) :
    WellFounded DPPairRev := by
  apply Subrelation.wf
    (r := fun a b : Trace => R.strict b a)
  · intro a b h
    exact R.pairs_strict h
  · exact R.strict_reverse_wellFounded

/-! ## Reduction triple -/

/-- A reduction triple adds an equivalence relation used for rules preserved
at equal weak value. -/
structure NativeReductionTriple extends NativeReductionPair where
  equiv : Trace -> Trace -> Prop
  equiv_refl : Reflexive equiv
  equiv_symm : Symmetric equiv
  equiv_trans : Transitive equiv
  equiv_sub_weak : forall {a b}, equiv a b -> weak a b

/-- Concrete triple based on syntactic equality and the polynomial pair. -/
def polynomialReductionTriple : NativeReductionTriple where
  toNativeReductionPair := polynomialReductionPair
  equiv := Eq
  equiv_refl := fun _ => rfl
  equiv_symm := by intro a b h; exact h.symm
  equiv_trans := by intro a b c h1 h2; exact h1.trans h2
  equiv_sub_weak := by rintro a _ rfl; exact le_rfl

/-! ## Source-termination bridge -/

/-- Additional source-step information needed to recover source termination.
This is independent of pair well-foundedness. -/
structure SourceLexBridge {α : Type} (P : SameSystemDPProblem α) where
  primary : α -> Nat
  secondary : α -> Nat
  source_decreases : forall {a b}, P.sourceStep a b ->
    Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
      (primary b, secondary b) (primary a, secondary a)

/-- A source bridge proves source strong normalization by a genuine
lexicographic measure. -/
theorem source_wellFounded_of_lexBridge
    {α : Type} {P : SameSystemDPProblem α} (B : SourceLexBridge P) :
    WellFounded (fun a b => P.sourceStep b a) := by
  have hlex : WellFounded
      (Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)) :=
    WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y))
      (fun a => (B.primary a, B.secondary a)))
  · intro a b h
    exact B.source_decreases h
  · exact InvImage.wf (fun a => (B.primary a, B.secondary a)) hlex

/-- Pair well-foundedness alone is insufficient: this toy problem has an empty
pair relation and a source self-loop. -/
def pairFreeSelfLoopProblem : SameSystemDPProblem Unit where
  sourceStep := fun _ _ => True
  pairStep := fun _ _ => False
  extractedFromSource := by intro a c h; exact False.elim h

/-- The transformed pair relation of the control problem is well founded. -/
theorem pairFreeSelfLoop_pair_wellFounded :
    WellFounded (fun a b : Unit => pairFreeSelfLoopProblem.pairStep b a) := by
  exact ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩

/-- Its source relation is not well founded. -/
theorem pairFreeSelfLoop_source_not_wellFounded :
    Not (WellFounded (fun a b : Unit => pairFreeSelfLoopProblem.sourceStep b a)) := by
  intro hwf
  have hloop : pairFreeSelfLoopProblem.sourceStep () () := trivial
  exact (hwf.asymmetric () () hloop) hloop

/-! ## Conditions and constrained rewriting controls -/

/-- A small conditional system with a live condition dimension. -/
inductive FixtureCondition
  | trueCondition
  | falseCondition
  deriving DecidableEq, Repr

/-- Interpreted truth of the two fixture conditions. -/
def fixtureConditionHolds : FixtureCondition -> Prop
  | .trueCondition => True
  | .falseCondition => False

inductive FixtureTwoDDimension
  | dependency
  | condition
  deriving DecidableEq, Repr

/-- Two-dimensional pair relation whose condition dimension is nonempty. -/
inductive FixtureTwoDDP : FixtureTwoDDimension -> Nat -> Nat -> Prop
  | dependency (n : Nat) : FixtureTwoDDP .dependency (n + 1) n
  | conditionTrue : fixtureConditionHolds .trueCondition ->
      FixtureTwoDDP .condition 1 0

/-- The condition dimension has a concrete edge. -/
theorem fixtureTwoDDP_condition_nonempty : FixtureTwoDDP .condition 1 0 :=
  FixtureTwoDDP.conditionTrue trivial

/-- The false condition cannot produce an edge. -/
theorem fixture_false_condition_rejected :
    Not (fixtureConditionHolds .falseCondition) := by
  simp [fixtureConditionHolds]

/-- The live KO7 integer constraint accepts a recursive source and rejects a
zero-counter non-source control. -/
theorem ko7Constraint_true_false_controls :
    ko7ConstrainedCertificate.constraint (recΔ void void (delta void)) ∧
      Not (ko7ConstrainedCertificate.constraint void) := by
  constructor
  · exact ko7ConstrainedCertificate.source_constrained void void void
  · simp [ko7ConstrainedCertificate, dpRank,
      OperatorKO7.CompositionalImpossibility.dpProjection]

/-! ## Higher-order substitution control -/

/-- The higher-order constrained row uses the repository's actual substitution
operation. This example records the known capture behavior on an open term. -/
theorem higherOrderSubstitution_open_capture_control :
    substitute 0 (.var 1) (.lam 1 (.var 0)) = .lam 1 (.var 1) := by
  rfl

/-- Closed atoms are unchanged by substitution. -/
theorem higherOrderSubstitution_closed_control :
    substitute 0 (.var 1) .atom = .atom := rfl

/-! ## ORI-4 package data -/

structure DependencyPairNativeBundle where
  problem : SameSystemDPProblem Trace
  pairOne : NativeReductionPair
  pairTwo : NativeReductionPair
  triple : NativeReductionTriple
  relationSeparation : pairOne.strict ≠ pairTwo.strict
  formativeExact : ∀ a b : Trace, (∃ tag, FormativePair tag a b) ↔ DPPair a b
  formativeWF : WellFounded (fun y x : Trace => ∃ tag, FormativePair tag x y)
  conditionEdge : FixtureTwoDDP .condition 1 0
  typedStep :
    SortedTransport.TypedRecSuccStep
      (.recur .base .stepZero (.succ .zero))
      (.wrap .stepZero (.recur .base .stepZero .zero))
  typedWF : WellFounded
    (fun y x : OperatorKO7.TypedBarrierSurvival.Term .res =>
      SortedTransport.TypedRecSuccStep x y)
  manySortedIdentity :
    OperatorKO7.ManySortedBarrierSurvival.MSort = OperatorKO7.TypedBarrierSurvival.Ty
  orderedPair : ∃ a b : OrderSortedTerm, OrderSortedDPPair a b
  orderedWF : WellFounded (fun y x : OrderSortedTerm => OrderSortedDPPair x y)
  replacement : ReplacementMap
  replacementPayloadFrozen : replacement.recurAllows 1 = false
  replacementCounterActive : replacement.recurAllows 2 = true
  contextSensitiveWF :
    WellFounded (fun a b : Trace => ContextSensitiveStep replacement Step b a)
  twoDConditionEmpty : ∀ a b : Trace, ¬ KO7TwoDDP .condition a b
  operationalConditionalWF : ∀ satisfies : Trace × Trace → Prop,
    WellFounded (fun a b : Trace => KO7ConditionalOperationalStep satisfies b a)
  constrained : ConstrainedCounterCertificate
  constrainedWF : WellFounded (fun a b : Trace => ConstrainedDPPair b a)
  higherOrderConstrainedWF : WellFounded
    (fun a b : OperatorKO7.HigherOrderRewritingSyntax.HOTerm =>
      HigherOrderConstrainedDPPair b a)

/-- Concrete ORI-4 method package. -/
def dependencyPairNativeBundle : DependencyPairNativeBundle where
  problem := ko7SameSystemDPProblem
  pairOne := polynomialReductionPair
  pairTwo := gapTwoReductionPair
  triple := polynomialReductionTriple
  relationSeparation := by
    intro h
    have hp := congrFun (congrFun h (delta void)) void
    have hpoly := nativeReductionPairs_relations_differ.1
    have hgap : gapTwoReductionPair.strict (delta void) void := by
      rw [← hp]
      exact hpoly
    exact nativeReductionPairs_relations_differ.2 hgap
  formativeExact := fun _ _ => formativePair_iff_dppair
  formativeWF := wf_FormativePairRev
  conditionEdge := fixtureTwoDDP_condition_nonempty
  typedStep := SortedTransport.typedRecSuccStep_nonempty
  typedWF := SortedTransport.typedRecSuccStep_wellFounded
  manySortedIdentity := rfl
  orderedPair := ⟨_, _, orderSortedDPPair_nonempty⟩
  orderedWF := orderSortedDPPair_wellFounded
  replacement := counterOnlyReplacement
  replacementPayloadFrozen := counterOnly_recur_payload_frozen
  replacementCounterActive := counterOnly_recur_counter_active
  contextSensitiveWF := contextSensitiveStep_wellFounded counterOnlyReplacement
  twoDConditionEmpty := fun _ _ => ko7TwoDDP_condition_empty
  operationalConditionalWF := ko7ConditionalOperationalTermination
  constrained := ko7ConstrainedCertificate
  constrainedWF := wf_ConstrainedDPPairRev
  higherOrderConstrainedWF := wf_HigherOrderConstrainedDPPairRev

end OperatorKO7.Methods.OrientationClosure.DependencyPairNativeSemantics
