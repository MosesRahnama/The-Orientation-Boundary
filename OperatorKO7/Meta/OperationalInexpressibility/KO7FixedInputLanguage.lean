import OperatorKO7.Meta.OperationalInexpressibility.FixedInputLanguage
import OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict

/-!
# Concrete KO7 fixed-input proof language

This module closes the non-vacuity obligation left by the generic
`FixedInputLanguageBoundary`. Both counterfactual worlds use one named KO7
trace input. They vary the actual relation system, agree on the complete
declared-candidate profile, and disagree on the independently justified global
strong-normalization verdict.

The admitted statement syntax contains two observation-only constant
statements. A third constructor denotes the semantic termination verdict but
is explicitly outside the derivable formation judgment. Thus neither
derivability nor target decision is stored as a constant epistemic predicate.
The target here is global relation termination, not accessibility of the named
trace; the fixed trace records the common input context only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.KO7FixedInputLanguage

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Meta.OperationalInexpressibility.FixedInputLanguage
open OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict

/-- Three explicit statements: two admitted observation-only constants and
one imported semantic-verdict statement. -/
inductive KO7Statement where
  | alwaysAccept
  | alwaysReject
  | importedTerminationVerdict
  deriving DecidableEq, Repr

/-- The common named KO7 input for both counterfactual systems. -/
def ko7FixedInput : Trace :=
  recΔ void void (delta void)

/-- Both counterfactual worlds are evaluated at the same named trace input. -/
def ko7WorldInput (_ : RelationSystem) : Trace :=
  ko7FixedInput

/-- Statement denotation on the actual two-system carrier. -/
def KO7Statement.denotes :
    KO7Statement -> RelationSystem -> Bool
  | .alwaysAccept, _ => true
  | .alwaysReject, _ => false
  | .importedTerminationVerdict, system => terminationVerdict system

/-- Formation judgment for the declared observation-only language. The
semantic-verdict constructor is a visible outside case, not silently admitted. -/
def KO7Statement.derivable : KO7Statement -> Prop
  | .alwaysAccept => True
  | .alwaysReject => True
  | .importedTerminationVerdict => False

/-- Closed KO7 inhabitant of the fixed-input interface. The observer is the
complete declared-candidate profile, not a selected Boolean. -/
def ko7FixedInputBoundary : FixedInputLanguageBoundary where
  Input := Trace
  Statement := KO7Statement
  World := RelationSystem
  Observation := Candidate -> Prop
  Dimension := RelationSystem
  Verdict := Bool
  fixedInput := ko7FixedInput
  worldInput := ko7WorldInput
  denotes := KO7Statement.denotes
  derivable := KO7Statement.derivable
  observe := directProfile
  dimension := fun system => system
  target := terminationVerdict
  sameContext := fun x y => ko7WorldInput x = ko7WorldInput y
  derivableFactors := by
    intro psi hderivable
    cases psi with
    | alwaysAccept =>
        exact ⟨fun _ => true, fun _ => rfl⟩
    | alwaysReject =>
        exact ⟨fun _ => false, fun _ => rfl⟩
    | importedTerminationVerdict =>
        exact hderivable.elim
  w1 := .recursor
  w2 := .selfEmbedding
  w1_at_fixedInput := rfl
  w2_at_fixedInput := rfl
  context_eq := rfl
  observation_eq := directProfile_recursor_eq_selfEmbedding
  dimension_ne := by decide
  target_ne := terminationVerdict_recursor_ne_selfEmbedding

/-- Closed fixed-input counterfactual with equal context and full observation,
but distinct system dimension and semantic termination verdict. -/
theorem ko7_fixedInput_counterfactual_witness :
    exists x y : ko7FixedInputBoundary.World,
      ko7FixedInputBoundary.worldInput x =
          ko7FixedInputBoundary.fixedInput ∧
        ko7FixedInputBoundary.worldInput y =
          ko7FixedInputBoundary.fixedInput ∧
        ko7FixedInputBoundary.sameContext x y ∧
        ko7FixedInputBoundary.observe x = ko7FixedInputBoundary.observe y ∧
        ko7FixedInputBoundary.dimension x ≠
          ko7FixedInputBoundary.dimension y ∧
        ko7FixedInputBoundary.target x ≠ ko7FixedInputBoundary.target y :=
  fixed_input_counterfactual_witness ko7FixedInputBoundary

/-- No statement admitted by the concrete KO7 observation-only formation
judgment decides semantic termination on both actual systems. -/
theorem ko7_no_derivable_statement_decides_termination
    {psi : KO7Statement} (hderivable : KO7Statement.derivable psi) :
    Not (DecidesTarget ko7FixedInputBoundary psi) :=
  no_derivable_statement_decides_target ko7FixedInputBoundary hderivable

/-- The visible imported statement would decide the target pointwise. -/
theorem ko7_importedTerminationVerdict_decides_target :
    DecidesTarget ko7FixedInputBoundary
      KO7Statement.importedTerminationVerdict := by
  intro system
  rfl

/-- The target-deciding imported statement is not admitted by the declared
observation-only language. -/
theorem ko7_importedTerminationVerdict_not_derivable :
    Not (KO7Statement.derivable
      KO7Statement.importedTerminationVerdict) := by
  intro h
  exact h

/-- At least one admitted statement exists, so the formation judgment is not
empty. -/
theorem ko7_derivable_statement_nonempty :
    exists psi : KO7Statement, KO7Statement.derivable psi :=
  ⟨.alwaysAccept, True.intro⟩

section AuditChecks

#check @ko7FixedInputBoundary
#check @ko7_fixedInput_counterfactual_witness
#check @ko7_no_derivable_statement_decides_termination
#check @ko7_importedTerminationVerdict_decides_target
#check @ko7_importedTerminationVerdict_not_derivable
#check @ko7_derivable_statement_nonempty

#print axioms ko7_fixedInput_counterfactual_witness
#print axioms ko7_no_derivable_statement_decides_termination
#print axioms ko7_importedTerminationVerdict_decides_target
#print axioms ko7_importedTerminationVerdict_not_derivable
#print axioms ko7_derivable_statement_nonempty

end AuditChecks

end OperatorKO7.Meta.OperationalInexpressibility.KO7FixedInputLanguage
