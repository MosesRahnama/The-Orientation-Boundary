import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.StructuralComposition
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.TerminalMultiplicity

/-!
# Scoped semantic coordinates

A scope stores the relation and source used by terminal-support computations,
together with caller-supplied audit, normalization, witness-language, and grade
metadata. The structure imposes zero coherence laws between those metadata
fields and the relation.

## Formal scope

Relation: the relation stored in `SemanticScope`.
Closure: the scope's named closure coordinate and exact-length reachability.
Trust: kernel-only, with classical finite enumeration for terminal support.
Scope: relation-local semantic measurement.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

/-- Whether normalization is absent, local to the named source, or global.
This field is metadata; proof-requiring theorems still take the corresponding
normalization witness explicitly. -/
inductive NormalizationStatus
  | unassumed
  | local
  | global
  deriving DecidableEq, Repr

/-- The language in which a semantic witness is interpreted. -/
inductive WitnessLanguageKind
  | base
  | licensed
  | external
  deriving DecidableEq, Repr

/-- Full scope of one semantic measurement. -/
structure SemanticScope (A : ARS.{u}) where
  relation : A.Carrier → A.Carrier → Prop
  source : A.Carrier
  audit : RelationAuditScope
  normalization : NormalizationStatus
  witnessLanguage : WitnessLanguageKind
  witnessGrade : Nat

namespace SemanticScope

noncomputable section

/-- Raw-source semantic scope. -/
def raw (A : ARS.{u}) (source : A.Carrier)
    (normalization : NormalizationStatus := .unassumed)
    (witnessLanguage : WitnessLanguageKind := .base)
    (witnessGrade : Nat := 0) : SemanticScope A where
  relation := A.step
  source := source
  audit := A.scope
  normalization := normalization
  witnessLanguage := witnessLanguage
  witnessGrade := witnessGrade

/-- Licensed semantic scope for a partial morphism's admitted relation. -/
def licensed {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) (source : A.Carrier)
    (normalization : NormalizationStatus := .unassumed)
    (witnessLanguage : WitnessLanguageKind := .licensed)
    (witnessGrade : Nat := 1) : SemanticScope A where
  relation := F.admitted
  source := source
  audit := { A.scope with admission := .guarded }
  normalization := normalization
  witnessLanguage := witnessLanguage
  witnessGrade := witnessGrade

/-- Reachable normal forms in the relation named by the scope. -/
def terminalSupport {A : ARS.{u}} [Fintype A.Carrier]
    (S : SemanticScope A) : Finset A.Carrier :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalSupport
    S.relation S.source

/-- Number of reachable normal forms in the named semantic scope. -/
def terminalMultiplicity {A : ARS.{u}} [Fintype A.Carrier]
    (S : SemanticScope A) : Nat :=
  OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalMultiplicity
    S.relation S.source

/-- Hartley support entropy guarded against an empty terminal support. -/
def terminalHartley? {A : ARS.{u}} [Fintype A.Carrier]
    (S : SemanticScope A) : Option Real :=
  if terminalMultiplicity S = 0 then none
  else some (Real.logb 2 (terminalMultiplicity S : Real))

/-- The guarded Hartley coordinate equals `none` iff terminal support is empty. -/
theorem terminalHartley?_eq_none_iff
    {A : ARS.{u}} [Fintype A.Carrier] (S : SemanticScope A) :
    terminalHartley? S = none ↔ terminalMultiplicity S = 0 := by
  unfold terminalHartley?
  by_cases h : terminalMultiplicity S = 0 <;> simp [h]

/-- A local normalization witness makes the guarded Hartley coordinate total
and identifies it with the existing terminal-support entropy. -/
theorem terminalHartley?_eq_some_of_normalizingAt
    {A : ARS.{u}} [Fintype A.Carrier] (S : SemanticScope A)
    (hnorm : NormalizingAt S.relation S.source) :
    terminalHartley? S =
      some
        (OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalHartleyEntropy
          S.relation S.source) := by
  have hpos : 0 < terminalMultiplicity S :=
    terminalMultiplicity_pos_of_normalizingAt hnorm
  unfold terminalHartley?
  rw [if_neg (Nat.ne_of_gt hpos)]
  rfl

/-- The stored relation and source determine the scoped terminal multiplicity. -/
theorem terminalMultiplicity_eq_scoped
    {A : ARS.{u}} [Fintype A.Carrier] (S : SemanticScope A) :
    terminalMultiplicity S =
      OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalMultiplicity
        S.relation S.source :=
  rfl

/-! ## Finite fixture -/

/-- Raw two-state chain scope. -/
def chain_fixture : SemanticScope chainARS_fixture :=
  raw chainARS_fixture ChainNode.source .local .base 0

/-- The chain target is terminal in the scoped relation. -/
theorem chain_target_normal_fixture :
    NormalForm chain_fixture.relation ChainNode.target := by
  intro y h
  cases h

/-- The chain scope is locally normalizing. -/
theorem chain_normalizing_fixture :
    NormalizingAt chain_fixture.relation chain_fixture.source := by
  intro x hx
  rcases hx with ⟨n, hn⟩
  cases hn with
  | zero =>
      exact
        ⟨ChainNode.target,
          OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_step ChainStep.descend,
          chain_target_normal_fixture⟩
  | succ hstep rest =>
      cases hstep
      have hxTarget : x = ChainNode.target :=
        eq_of_normalForm_reach chain_target_normal_fixture ⟨_, rest⟩
      subst x
      exact
        ⟨ChainNode.target,
          OperatorKO7.Meta.DistinctionBoundary.Quantitative.reach_refl _,
          chain_target_normal_fixture⟩

theorem chain_terminalHartley_defined_fixture :
    ∃ h : Real,
      @terminalHartley? chainARS_fixture
        (by change Fintype ChainNode; infer_instance) chain_fixture = some h := by
  letI : Fintype chainARS_fixture.Carrier := by
    change Fintype ChainNode
    infer_instance
  refine
    ⟨OperatorKO7.Meta.DistinctionBoundary.Quantitative.terminalHartleyEntropy
        chain_fixture.relation chain_fixture.source, ?_⟩
  exact terminalHartley?_eq_some_of_normalizingAt chain_fixture chain_normalizing_fixture

#check @SemanticScope.raw
#check @SemanticScope.licensed
#check @SemanticScope.terminalHartley?_eq_none_iff
#check @SemanticScope.terminalHartley?_eq_some_of_normalizingAt
#check chain_terminalHartley_defined_fixture
#print axioms SemanticScope.terminalHartley?_eq_none_iff
#print axioms SemanticScope.terminalHartley?_eq_some_of_normalizingAt
#print axioms chain_normalizing_fixture
#print axioms chain_terminalHartley_defined_fixture

end
end SemanticScope
end OperatorKO7.Meta.LicensedBoundaryCalculus
