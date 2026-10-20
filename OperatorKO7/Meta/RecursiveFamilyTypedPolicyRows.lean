import OperatorKO7.Meta.TypedBarrierSurvival
import OperatorKO7.Meta.ManySortedBarrierSurvival
import OperatorKO7.Meta.HigherOrderRewriting_PolicyAudit
import OperatorKO7.Meta.HigherOrderRewriting_FullCaptureBoundary
import OperatorKO7.Meta.HigherOrderNoSharingBoundary
import OperatorKO7.Meta.HigherOrderRewriting_Closeout
import OperatorKO7.Meta.DirectBarrierScope

/-!
# Recursive Family Typed and Policy Rows (Phase E')

Phase E' surface layer. Existing typed / many-sorted / policy-indexed claims
are already mechanized in dedicated modules; Phase E' does not reopen those
proofs and does not introduce speculative new Lean content. Instead, this
module catalogs the existing surfaces as a single finite list of named rows
and records, per row, a projection witness onto an existing theorem-backed
identifier from the substrate.

The seven row identities and their backing substrate:

* `typedTransport` ->
  `OperatorKO7.TypedBarrierSurvival.no_additive_orients_typed_recSucc`.
* `manySortedTransport` ->
  `OperatorKO7.ManySortedBarrierSurvival.no_additive_orients_manySorted_recSucc`.
* `higherOrderPolicyAudit` ->
  `OperatorKO7.HigherOrderRewritingPolicyAudit.hoPolicyRows_length`
  (8-row audit catalog).
* `higherOrderClosure` ->
  `OperatorKO7.HigherOrderRewritingCloseout.hoCloseoutRows_length`
  (8-row closeout catalog).
* `noSharingBoundary` ->
  `OperatorKO7.HigherOrderNoSharingBoundary.no_sharing_hypothesis_is_required_for_tree_lift`.
* `fullCaptureBoundary` ->
  `OperatorKO7.HigherOrderRewritingFullCaptureBoundary.fullCaptureAvoidanceLaw_requiresBodyFreshness`.
* `strategyAndConstraintTrivialization` ->
  `OperatorKO7.StepDuplicating.innermostOnlyScope_not_InScope` (strategy
  trivialization) and `OperatorKO7.StepDuplicating.acQuotientScope_not_InScope`
  (constraint trivialization), via the `DirectBarrierScope` sentinels.

No proof placeholder is used, no top-level postulate is declared, and no
existing public name is touched.
-/

namespace OperatorKO7.StepDuplicating
namespace RecursiveFamilyTypedPolicyRows

open OperatorKO7
open OperatorKO7.TypedBarrierSurvival
open OperatorKO7.ManySortedBarrierSurvival
open OperatorKO7.HigherOrderRewritingPolicyAudit
open OperatorKO7.HigherOrderRewritingCloseout
open OperatorKO7.HigherOrderNoSharingBoundary
open OperatorKO7.HigherOrderRewritingFullCaptureBoundary

/-- Finite identity tag for each Phase E' typed-or-policy row surfaced from
the substrate. The seven constructors match the seven roadmap deliverables
(typed transport, many-sorted transport, tree-policy higher-order audit,
higher-order closure, sharing status, full-capture status, and the
strategy/constraint trivialization pair). -/
inductive RecursiveFamilyTypedPolicyRow
  | typedTransport
  | manySortedTransport
  | higherOrderPolicyAudit
  | higherOrderClosure
  | noSharingBoundary
  | fullCaptureBoundary
  | strategyAndConstraintTrivialization
  deriving DecidableEq, Repr

namespace RecursiveFamilyTypedPolicyRow

/-- Per-row status tag for Phase E'. Every row currently surfaced is a
theorem-backed transport from an existing module, hence `theoremBacked`.
The constructor is retained for symmetry with the other catalog surfaces
(`HOPolicyRowStatus`, `FullCaptureBoundaryRowStatus`, etc.) and to allow
later phases to add residual or status rows without breaking the
public surface. -/
inductive Status
  | theoremBacked
  deriving DecidableEq, Repr

/-- Status assignment for every Phase E' row. Every row is currently
theorem-backed via the projection lemma in
`typed_policy_rows_project_existing_surfaces`. -/
def status : RecursiveFamilyTypedPolicyRow → Status
  | _ => Status.theoremBacked

end RecursiveFamilyTypedPolicyRow

/-- Finite catalog of Phase E' typed / many-sorted / policy rows.

The order is fixed: typed transport, many-sorted transport, higher-order
policy audit, higher-order closure, no-sharing boundary, full-capture
boundary, strategy-and-constraint trivialization. -/
def recursiveFamilyTypedPolicyRows : List RecursiveFamilyTypedPolicyRow :=
  [ .typedTransport
  , .manySortedTransport
  , .higherOrderPolicyAudit
  , .higherOrderClosure
  , .noSharingBoundary
  , .fullCaptureBoundary
  , .strategyAndConstraintTrivialization ]

/-- The Phase E' row catalog has the expected length, is duplicate-free,
and covers every constructor of `RecursiveFamilyTypedPolicyRow`. -/
theorem typed_policy_rows_complete_exact :
    recursiveFamilyTypedPolicyRows.length = 7 ∧
      recursiveFamilyTypedPolicyRows.Nodup ∧
      (∀ row : RecursiveFamilyTypedPolicyRow,
        row ∈ recursiveFamilyTypedPolicyRows) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · decide
  · intro row
    cases row <;> decide

/-- Projection of every Phase E' row onto a concrete existing theorem
identifier from the substrate. Each branch returns a propositional witness
that the named substrate surface is reachable and theorem-backed. No new
content about KO7, the schema, or the higher-order layers is asserted; the
projection reuses the existing theorem applied to canonical arguments. -/
def typed_policy_rows_project_existing_surfaces :
    RecursiveFamilyTypedPolicyRow → Prop
  | .typedTransport =>
      ∀ (M : TypedBarrierSurvival.AdditiveMeasure),
        ¬ (∀ (b : TypedBarrierSurvival.Term .res)
            (s : TypedBarrierSurvival.Term .step)
            (n : TypedBarrierSurvival.Term .cnt),
          M.evalRes
              (TypedBarrierSurvival.Term.wrap s
                (TypedBarrierSurvival.Term.recur b s n)) <
            M.evalRes
              (TypedBarrierSurvival.Term.recur b s
                (TypedBarrierSurvival.Term.succ n)))
  | .manySortedTransport =>
      ∀ (M : ManySortedBarrierSurvival.AdditiveMeasure),
        ¬ (∀ (b : TypedBarrierSurvival.Term .res)
            (s : TypedBarrierSurvival.Term .step)
            (n : TypedBarrierSurvival.Term .cnt),
          M.evalRes
              (TypedBarrierSurvival.Term.wrap s
                (TypedBarrierSurvival.Term.recur b s n)) <
            M.evalRes
              (TypedBarrierSurvival.Term.recur b s
                (TypedBarrierSurvival.Term.succ n)))
  | .higherOrderPolicyAudit =>
      HigherOrderRewritingPolicyAudit.hoPolicyRows.length = 8
  | .higherOrderClosure =>
      HigherOrderRewritingCloseout.hoCloseoutRows.length = 8
  | .noSharingBoundary =>
      HigherOrderNoSharingBoundary.NoSharingLiftHypothesis
  | .fullCaptureBoundary =>
      HigherOrderRewritingFullCaptureBoundary.FullCaptureAvoidanceLawUpstreamObligation
  | .strategyAndConstraintTrivialization =>
      (¬ OperatorKO7.StepDuplicating.InScope
            OperatorKO7.StepDuplicating.innermostOnlyScope) ∧
        (¬ OperatorKO7.StepDuplicating.InScope
            OperatorKO7.StepDuplicating.acQuotientScope)

/-- Every Phase E' row's projection predicate is theorem-backed by an
existing substrate identifier. Each branch reuses the existing theorem
name and, where the row is a catalog-length or sentinel claim, reuses
the existing `*_length` / `*_not_InScope` theorems. No new Lean content
about the substrate is produced. -/
theorem typed_policy_rows_project_existing_surfaces_holds
    (row : RecursiveFamilyTypedPolicyRow) :
    typed_policy_rows_project_existing_surfaces row := by
  cases row with
  | typedTransport =>
      intro M
      exact TypedBarrierSurvival.no_additive_orients_typed_recSucc M
  | manySortedTransport =>
      intro M
      exact ManySortedBarrierSurvival.no_additive_orients_manySorted_recSucc M
  | higherOrderPolicyAudit =>
      exact HigherOrderRewritingPolicyAudit.hoPolicyRows_length
  | higherOrderClosure =>
      exact HigherOrderRewritingCloseout.hoCloseoutRows_length
  | noSharingBoundary =>
      exact no_sharing_hypothesis_is_required_for_tree_lift
  | fullCaptureBoundary =>
      exact fullCaptureAvoidanceLaw_requiresBodyFreshness
  | strategyAndConstraintTrivialization =>
      exact ⟨OperatorKO7.StepDuplicating.innermostOnlyScope_not_InScope,
             OperatorKO7.StepDuplicating.acQuotientScope_not_InScope⟩

/-- Phase E' closeout marker. The catalog is complete and exact, and every
row projects onto an existing theorem-backed substrate identifier. This is
the single public name reviewers reach for to confirm Phase E' closure.

No new manuscript or Lean claim is asserted beyond what the substrate
modules already establish; Phase E' is intentionally a surfacing pass. -/
theorem phaseEprime_typed_policy_rows_closed :
    (recursiveFamilyTypedPolicyRows.length = 7 ∧
        recursiveFamilyTypedPolicyRows.Nodup ∧
        (∀ row : RecursiveFamilyTypedPolicyRow,
          row ∈ recursiveFamilyTypedPolicyRows)) ∧
      (∀ row : RecursiveFamilyTypedPolicyRow,
        typed_policy_rows_project_existing_surfaces row) :=
  ⟨typed_policy_rows_complete_exact,
   typed_policy_rows_project_existing_surfaces_holds⟩

end RecursiveFamilyTypedPolicyRows
end OperatorKO7.StepDuplicating
