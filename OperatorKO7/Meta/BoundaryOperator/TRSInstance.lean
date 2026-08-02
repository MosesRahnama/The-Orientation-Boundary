import OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness
import OperatorKO7.Meta.BoundaryOperator.LicensedQuotient
import OperatorKO7.Meta.ConfessionMethod_UsableRulesConcrete
import OperatorKO7.Meta.SchemaForgettingWitness
import OperatorKO7.Meta.MetaHalt_Predicate

/-!
# Boundary Operator TRS Instance

This module provides the first theorem-backed boundary-operator instantiation
for the TRS lane. It lifts the existing usable-rules concrete witness into the
boundary-operator surface without claiming the still-missing usable-rules
soundness bridge.
-/

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.MetaHalt.Predicate

/-- The lifted confession-core witness used by the TRS boundary plug. -/
def trsConfessionCoreWitness : ConfessionCoreWitness ko7Schema :=
  usableRulesConcreteRouteCandidate.toConfessionCoreWitness
    usableRulesConcreteRouteCandidate.witness

/-- The lifted route evidence used by the TRS boundary plug. -/
def trsRouteEvidence : RouteEvidence ko7Schema :=
  usableRulesConcreteRouteCandidate.toRouteEvidence
    usableRulesConcreteRouteCandidate.witness

theorem trsConfessionCoreWitness_projects_core :
    trsConfessionCoreWitness.toProjectionRank = confessionProjectionCore := by
  simpa [trsConfessionCoreWitness] using usableRulesConcreteRouteCandidate.core_agrees

theorem trsRouteEvidence_projects_generic_route :
    trsRouteEvidence = confessionGenericRouteEvidence := by
  simpa [trsRouteEvidence] using usableRulesConcreteRouteCandidate.route_agrees

theorem trsRouteEvidence_projects_forgetting_rank :
    (ForgettingWitness.ofRouteEvidence trsRouteEvidence).rank = dpConfession.rank := by
  simpa [trsRouteEvidence] using
    usableRulesConcreteRouteCandidate_projects_forgetting_rank
      (C := usableRulesConcreteRouteCandidate)

/-- The payload tags distinguish the two live TRS inputs that collapse to the
same boundary verdict. -/
inductive TRSPayloadTag
  | direct
  | shadow
  deriving DecidableEq, Repr

/-- The TRS plug has one blocked outside-domain point and two live points. -/
inductive TRSPlugInput
  | blocked
  | direct
  | shadow
  deriving DecidableEq, Repr

/-- The live boundary verdict exported by the TRS plug. -/
def trsBoundaryVerdict : TypedOutput :=
  .T3_confession "dpConfession" "TRS" "wrapper" "usableRules"

/-- The nontrivial gauge action swaps the two live TRS payload tags. -/
def trsGaugeActionX : Z2 → TRSPlugInput → TRSPlugInput
  | .id, x => x
  | .flip, .blocked => .blocked
  | .flip, .direct => .shadow
  | .flip, .shadow => .direct

/-- The TRS plug is gauge-invariant at the output surface. -/
def trsGaugeActionY (_ : Z2) (y : TypedOutput) : TypedOutput := y

/-- Runtime channel for the TRS plug. -/
def trsChannel : Channel TRSPlugInput TypedOutput where
  send
    | .blocked => none
    | .direct => some trsBoundaryVerdict
    | .shadow => some trsBoundaryVerdict
  preserves_isolation := False

/-- The theorem-backed TRS boundary-operator plug. -/
noncomputable def TRS_BoundaryOperator : BoundaryOperator TRSPlugInput TypedOutput where
  domain
    | .blocked => False
    | .direct => True
    | .shadow => True
  apply _ _ := trsBoundaryVerdict
  gauge_group := Z2
  gauge_struct := inferInstance
  gauge_action_X := trsGaugeActionX
  gauge_action_Y := trsGaugeActionY
  channel := trsChannel
  Payload := TRSPayloadTag
  payload_extract
    | .blocked => .direct
    | .direct => .direct
    | .shadow => .shadow
  landauer_cost _ _ := Real.log 2
  kB := 1
  temperature := 1
  partiality := by
    intro hall
    exact hall .blocked
  irreversibility := by
    intro y
    by_cases hy : y = trsBoundaryVerdict
    · subst hy
      intro huniq
      rcases huniq with ⟨xh, hxout, hunique⟩
      let x0 : {x : TRSPlugInput // match x with | .blocked => False | .direct => True | .shadow => True} :=
        ⟨.direct, trivial⟩
      let x1 : {x : TRSPlugInput // match x with | .blocked => False | .direct => True | .shadow => True} :=
        ⟨.shadow, trivial⟩
      have hx0 : trsBoundaryVerdict = trsBoundaryVerdict := rfl
      have hx1 : trsBoundaryVerdict = trsBoundaryVerdict := rfl
      have hx0eq : x0 = xh := hunique x0 hx0
      have hx1eq : x1 = xh := hunique x1 hx1
      have hsame : x0 = x1 := hx0eq.trans hx1eq.symm
      have hvals : TRSPlugInput.direct = TRSPlugInput.shadow := congrArg Subtype.val hsame
      cases hvals
    · intro huniq
      rcases huniq with ⟨xh, hxout, _⟩
      cases xh with
      | mk x hx =>
          cases x with
          | blocked => cases hx
          | direct => exact hy hxout.symm
          | shadow => exact hy hxout.symm
  gaugeCovariance := by
    intro g x h h'
    rfl
  channelPreservation := by
    intro x h
    cases x <;> cases h <;> rfl
  payloadDiscarding := by
    intro hrecover
    rcases hrecover with ⟨recover, hrecover⟩
    have h0 := hrecover ⟨.direct, trivial⟩
    have h1 := hrecover ⟨.shadow, trivial⟩
    simp [trsBoundaryVerdict] at h0 h1
    have : TRSPayloadTag.direct = TRSPayloadTag.shadow := h0.symm.trans h1
    cases this
  landauerCost := by
    intro x h
    have hlog : 0 ≤ Real.log 2 := by
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith

theorem TRS_BoundaryOperator_inhabited :
    Nonempty (BoundaryOperator TRSPlugInput TypedOutput) :=
  ⟨TRS_BoundaryOperator⟩

theorem TRS_BoundaryOperator_typed_refusal_completeness :
    ∃ (Y_typed : Set TypedOutput) (refusal_classifier : TypedOutput → RefusalType),
      Y_typed = Set.univ ∧
      ∀ y, refusal_classifier y ∈ refusalTypeSupport :=
  TypedOutputBoundaryOperatorCompleteness TRS_BoundaryOperator

/-- The licensed quotient used by the TRS plug. The quotient collapses the live
TRS boundary states to one observable plug verdict. -/
def TRS_LicensedQuotient : LicensedQuotient TRSPlugInput where
  G := Z2
  group_struct := inferInstance
  action := trsGaugeActionX
  quotient := Unit
  proj := fun _ => ()
  proj_quotients := by
    intro g x
    rfl
  license := {
    obstruction := True
    holds := trivial
  }
  observable := fun _ => ⟨"trs-boundary-plug"⟩

/-- The TRS plug factors through the licensed quotient. -/
def TRS_BoundaryOperator_factorization :
    LicensedQuotientFactorizationCertificate TRS_BoundaryOperator where
  quotient := TRS_LicensedQuotient
  observe := fun _ => trsBoundaryVerdict
  factors := by
    intro x h
    rfl

theorem TRS_BoundaryOperator_has_licensed_quotient_factorization :
    ∃ (LQ : LicensedQuotient TRSPlugInput) (O : LQ.quotient → TypedOutput),
      ∀ x h, TRS_BoundaryOperator.apply x h = O (LQ.proj x) :=
  LicensedQuotientFactorization TRS_BoundaryOperator TRS_BoundaryOperator_factorization

end OperatorKO7.Meta.BoundaryOperator
