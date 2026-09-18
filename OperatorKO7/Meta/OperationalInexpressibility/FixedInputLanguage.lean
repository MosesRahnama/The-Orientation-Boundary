import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
import OperatorKO7.Meta.SchemaOperationalIncompleteness

/-!
# Fixed-input proof-language boundary

This module packages a fixed-input language whose derivable statements factor
through a declared observer. Its distinguished counterfactual pair holds the
outside context fixed, changes the named dimension, preserves the observation,
and changes the target verdict.

`DependsOnDimension` and `ConstrainsTarget` are semantic predicates derived
from denotation, context, dimension, and target agreement. They are not stored
as arbitrary fields. The bridge at the end instantiates the legacy abstract
`OperationallyIncomplete` predicate with these semantic definitions.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FixedInputLanguage

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary

universe uInput uStatement uWorld uObservation uDimension uVerdict

/-- A precise fixed-input proof-language boundary. `derivable` is a supplied
formation or derivation judgment; theorem certification, when intended by a
client, remains a separate client-side predicate. -/
structure FixedInputLanguageBoundary where
  Input : Type uInput
  Statement : Type uStatement
  World : Type uWorld
  Observation : Type uObservation
  Dimension : Type uDimension
  Verdict : Type uVerdict
  fixedInput : Input
  worldInput : World -> Input
  denotes : Statement -> World -> Verdict
  derivable : Statement -> Prop
  observe : World -> Observation
  dimension : World -> Dimension
  target : World -> Verdict
  sameContext : World -> World -> Prop
  derivableFactors :
    forall psi : Statement, derivable psi ->
      exists decode : Observation -> Verdict,
        forall world : World,
          denotes psi world = decode (observe world)
  w1 : World
  w2 : World
  w1_at_fixedInput : worldInput w1 = fixedInput
  w2_at_fixedInput : worldInput w2 = fixedInput
  context_eq : sameContext w1 w2
  observation_eq : observe w1 = observe w2
  dimension_ne : dimension w1 ≠ dimension w2
  target_ne : target w1 ≠ target w2

/-- The named dimension is present when two worlds share the outside context
but carry distinct dimension values. -/
def DimensionPresent (B : FixedInputLanguageBoundary) : Prop :=
  exists x y : B.World,
    B.sameContext x y ∧ B.dimension x ≠ B.dimension y

/-- A statement depends on the named dimension when its denotation changes on
an explicit same-context counterfactual pair whose dimension changes. -/
def DependsOnDimension (B : FixedInputLanguageBoundary)
    (psi : B.Statement) : Prop :=
  exists x y : B.World,
    B.sameContext x y ∧
      B.dimension x ≠ B.dimension y ∧
      B.denotes psi x ≠ B.denotes psi y

/-- A statement constrains the target when, inside a fixed outside context,
agreement of the statement's denotation forces agreement of the target. -/
def ConstrainsTarget (B : FixedInputLanguageBoundary)
    (psi : B.Statement) : Prop :=
  forall {x y : B.World},
    B.sameContext x y ->
      B.denotes psi x = B.denotes psi y ->
        B.target x = B.target y

/-- Pointwise target decision is the stronger statement that the denotation
equals the target verdict on every admissible world in the boundary. -/
def DecidesTarget (B : FixedInputLanguageBoundary)
    (psi : B.Statement) : Prop :=
  forall world : B.World, B.denotes psi world = B.target world

/-- The structure carries an explicit dimension-present witness. -/
theorem dimension_present (B : FixedInputLanguageBoundary) :
    DimensionPresent B :=
  ⟨B.w1, B.w2, B.context_eq, B.dimension_ne⟩

/-- The same-context, observation-collision counterfactual supplied by the
structure. -/
theorem fixed_counterfactual_witness (B : FixedInputLanguageBoundary) :
    exists x y : B.World,
      B.sameContext x y ∧
        B.observe x = B.observe y ∧
        B.dimension x ≠ B.dimension y ∧
        B.target x ≠ B.target y :=
  ⟨B.w1, B.w2, B.context_eq, B.observation_eq,
    B.dimension_ne, B.target_ne⟩

/-- Strong fixed-input form of the counterfactual: both worlds are explicitly
indexed by the boundary's named input. -/
theorem fixed_input_counterfactual_witness
    (B : FixedInputLanguageBoundary) :
    exists x y : B.World,
      B.worldInput x = B.fixedInput ∧
        B.worldInput y = B.fixedInput ∧
        B.sameContext x y ∧
        B.observe x = B.observe y ∧
        B.dimension x ≠ B.dimension y ∧
        B.target x ≠ B.target y :=
  ⟨B.w1, B.w2, B.w1_at_fixedInput, B.w2_at_fixedInput,
    B.context_eq, B.observation_eq, B.dimension_ne, B.target_ne⟩

/-- The distinguished worlds form a concrete observer collision for the target
verdict. -/
theorem target_collision (B : FixedInputLanguageBoundary) :
    OperationallyInexpressibleAt B.observe B.target B.w1 B.w2 :=
  ⟨B.observation_eq, B.target_ne⟩

/-- Every derivable statement's denotation is constant on observer fibers. -/
theorem derivable_denotation_factorsThrough
    (B : FixedInputLanguageBoundary) {psi : B.Statement}
    (hderivable : B.derivable psi) :
    FactorsThrough B.observe (B.denotes psi) := by
  obtain ⟨decode, hdecode⟩ := B.derivableFactors psi hderivable
  intro x y hobserve
  calc
    B.denotes psi x = decode (B.observe x) := hdecode x
    _ = decode (B.observe y) := congrArg decode hobserve
    _ = B.denotes psi y := (hdecode y).symm

/-- The supplied factor map is also a total decoder for each derivable
statement's own denotation. -/
theorem derivable_denotation_verdictDeterminedBy
    (B : FixedInputLanguageBoundary) {psi : B.Statement}
    (hderivable : B.derivable psi) :
    VerdictDeterminedBy B.observe (B.denotes psi) := by
  obtain ⟨decode, hdecode⟩ := B.derivableFactors psi hderivable
  exact ⟨decode, fun world => (hdecode world).symm⟩

/-- Equal observations force equal denotations for every derivable statement. -/
theorem derivable_denotation_eq_of_observation_eq
    (B : FixedInputLanguageBoundary) {psi : B.Statement}
    (hderivable : B.derivable psi) {x y : B.World}
    (hobserve : B.observe x = B.observe y) :
    B.denotes psi x = B.denotes psi y :=
  derivable_denotation_factorsThrough B hderivable hobserve

/-- Pointwise decision of the target implies the context-relative target
constraint predicate. -/
theorem decidesTarget_implies_constrainsTarget
    (B : FixedInputLanguageBoundary) {psi : B.Statement}
    (hdecides : DecidesTarget B psi) :
    ConstrainsTarget B psi := by
  intro x y _hcontext hdenotes
  calc
    B.target x = B.denotes psi x := (hdecides x).symm
    _ = B.denotes psi y := hdenotes
    _ = B.target y := hdecides y

/-- No derivable observation-only statement can constrain the target across
the distinguished same-context collision. -/
theorem no_derivable_constrainsTarget
    (B : FixedInputLanguageBoundary) {psi : B.Statement}
    (hderivable : B.derivable psi) :
    Not (ConstrainsTarget B psi) := by
  intro hconstrains
  apply B.target_ne
  exact hconstrains B.context_eq
    (derivable_denotation_eq_of_observation_eq
      B hderivable B.observation_eq)

/-- Consequently, no derivable observation-only statement decides the target
on every world. -/
theorem no_derivable_statement_decides_target
    (B : FixedInputLanguageBoundary) {psi : B.Statement}
    (hderivable : B.derivable psi) :
    Not (DecidesTarget B psi) := by
  intro hdecides
  exact (no_derivable_constrainsTarget B hderivable)
    (decidesTarget_implies_constrainsTarget B hdecides)

/-- The fixed pair proves that the target itself does not factor through the
language observer. -/
theorem target_not_factorsThrough (B : FixedInputLanguageBoundary) :
    Not (FactorsThrough B.observe B.target) :=
  not_factorsThrough_of_collision (target_collision B)

/-- Equivalently, the target has no factor through the actual observer-kernel
quotient. -/
theorem target_has_no_quotientFactorization
    (B : FixedInputLanguageBoundary) :
    Not (QuotientFactorization B.observe B.target) := by
  intro hquotient
  exact target_not_factorsThrough B
    ((quotientFactorization_iff_factorsThrough B.observe B.target).1
      hquotient)

/-! ## Bridge to the abstract operational-incompleteness interface -/

/-- The legacy abstract question instantiated with semantic, nonconstant
dimension and target predicates from this boundary. -/
def operationalQuestion (B : FixedInputLanguageBoundary) :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.OperationalQuestion
      B.Statement where
  derivable := B.derivable
  dependsOnDimension := DependsOnDimension B
  constrainsTarget := ConstrainsTarget B
  dimensionPresent := DimensionPresent B

/-- The fixed collision gives an `OperationallyIncomplete` instance whose
epistemic predicates are the semantic definitions above, not constant truth. -/
theorem operationalQuestion_operationallyIncomplete
    (B : FixedInputLanguageBoundary) :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.OperationallyIncomplete
      (operationalQuestion B) := by
  refine ⟨dimension_present B, ?_⟩
  intro psi hderivable hboth
  exact (no_derivable_constrainsTarget B hderivable) hboth.2

end OperatorKO7.Meta.OperationalInexpressibility.FixedInputLanguage
