import OperatorKO7.Meta.SafeStep.BranchTransaction
import OperatorKO7.Meta.BoundaryOperator.TRSInstance

set_option autoImplicit false

/-!
# Semantic SafeStep confession bridge

The historical `safestep_is_meta_halt` theorem was layer-generic and did not
mention `SafeStep`.  This module instead requires concrete evidence at the KO7
diagonal: a retained safe branch, a refused raw branch, and the restored local
join.  A relation-level classifier branches on the independent proposition that
the raw relation has an edge refused by the licensed relation.  The concrete
SafeStep evidence proves that proposition before the classifier is shown to
return `T3_confession`; the output tag is not stored in the evidence object.

The comparison with the termination-axis TRS plug is explicit: both outputs use
the `T3_confession` constructor and therefore share its four-field payload
schema, but their payload values and proof chains differ.  No equality of the
full typed outputs is claimed.
-/

namespace OperatorKO7.Meta.SafeStep.SafeStepConfessionBridge

open OperatorKO7
open OperatorKO7.Trace
open MetaSN_KO7
open OperatorKO7.MetaHalt.Predicate
open OperatorKO7.Meta.SafeStep.BranchTransaction
open OperatorKO7.Meta.BoundaryOperator

/-- Concrete confluence-side evidence at the determined KO7 diagonal.  Every
field names the actual `Step`/`SafeStep` relations and the actual source and
targets; there is no generic boundary-operator parameter. -/
structure ConcreteSafeStepEvidence : Prop where
  selected_safe : SafeStep (eqW void void) void
  selected_raw : Step (eqW void void) void
  difference_raw :
    Step (eqW void void) (integrate (merge void void))
  difference_refused :
    ¬ SafeStep (eqW void void) (integrate (merge void void))
  restored_local_join : LocalJoinSafe (eqW void void)

/-- The existing branch transaction supplies the complete concrete evidence. -/
theorem concreteSafeStepEvidence : ConcreteSafeStepEvidence where
  selected_safe := diagonal_selected_licensed
  selected_raw := ko7_branchTransaction_selected_raw
  difference_raw := diagonal_forbiddenBranch.raw
  difference_refused := diagonal_forbiddenBranch.refused
  restored_local_join := ko7_branchTransaction.joinable

/-- A proof-carrying certificate that `Raw` has an edge refused by `Licensed`. -/
structure RefusedEdgeCertificate
    (Raw Licensed : Trace -> Trace -> Prop) where
  source : Trace
  target : Trace
  raw : Raw source target
  refused : ¬ Licensed source target

/-- Independent semantic property used by the classifier. -/
def HasRefusedEdge
    (Raw Licensed : Trace -> Trace -> Prop) : Prop :=
  Nonempty (RefusedEdgeCertificate Raw Licensed)

/-- Extract the exact refused diagonal edge from concrete SafeStep evidence. -/
def concreteSafeStepRefusedEdge
    (h : ConcreteSafeStepEvidence) :
    RefusedEdgeCertificate Step SafeStep where
  source := eqW void void
  target := integrate (merge void void)
  raw := h.difference_raw
  refused := h.difference_refused

/-- Concrete SafeStep evidence proves the classifier's independent semantic
premise. -/
theorem concreteSafeStepEvidence_has_refused_edge
    (h : ConcreteSafeStepEvidence) :
    HasRefusedEdge Step SafeStep :=
  ⟨concreteSafeStepRefusedEdge h⟩

/-- Proof-carrying confession evidence.  It retains the concrete guard evidence
and the exact semantic certificate, but stores neither an output nor an output
equality. -/
structure SafeStepConfessionEvidence where
  safeStepEvidence : ConcreteSafeStepEvidence
  refusedEdgeCertificate : RefusedEdgeCertificate Step SafeStep
  certificate_source_exact :
    refusedEdgeCertificate.source = eqW void void
  certificate_target_exact :
    refusedEdgeCertificate.target = integrate (merge void void)

/-- Package any concrete SafeStep evidence with the certificate extracted from
that same proof object. -/
def safeStepConfessionEvidenceOf
    (h : ConcreteSafeStepEvidence) : SafeStepConfessionEvidence where
  safeStepEvidence := h
  refusedEdgeCertificate := concreteSafeStepRefusedEdge h
  certificate_source_exact := rfl
  certificate_target_exact := rfl

/-- Canonical SafeStep-side confession evidence with the concrete diagonal
certificate retained in its type. -/
def ko7SafeStepConfessionEvidence : SafeStepConfessionEvidence where
  safeStepEvidence := concreteSafeStepEvidence
  refusedEdgeCertificate :=
    concreteSafeStepRefusedEdge concreteSafeStepEvidence
  certificate_source_exact := rfl
  certificate_target_exact := rfl

/-- Every confession-evidence package supplies the classifier premise through
its retained certificate. -/
theorem SafeStepConfessionEvidence.hasRefusedEdge
    (E : SafeStepConfessionEvidence) :
    HasRefusedEdge Step SafeStep :=
  ⟨E.refusedEdgeCertificate⟩

/-- Semantic classifier: confession is selected exactly on the refused-edge
property; absence of such an edge selects typed abstention. -/
noncomputable def safeStepSemanticClassifier : TypedOutput := by
  classical
  exact if HasRefusedEdge Step SafeStep then
    .T3_confession "SafeStep.diagonal_forbiddenBranch" "KO7.Confluence"
      "diagonalDifferenceBranch" "LocalJoinSafe"
  else
    .T4_abstention "noRefusedSafeStepEdge"
      ["KO7.Confluence"] ["T3_confession"]

/-- The positive semantic branch: a refused-edge witness forces confession. -/
theorem safeStepSemanticClassifier_eq_t3
    (h : HasRefusedEdge Step SafeStep) :
    safeStepSemanticClassifier =
      .T3_confession "SafeStep.diagonal_forbiddenBranch" "KO7.Confluence"
        "diagonalDifferenceBranch" "LocalJoinSafe" := by
  classical
  simp [safeStepSemanticClassifier, h]

/-- Falsifier branch for the classification rule: without any refused raw edge,
the same classifier emits typed abstention rather than confession. -/
theorem safeStepSemanticClassifier_eq_t4
    (h : ¬ HasRefusedEdge Step SafeStep) :
    safeStepSemanticClassifier =
      .T4_abstention "noRefusedSafeStepEdge"
        ["KO7.Confluence"] ["T3_confession"] := by
  classical
  simp [safeStepSemanticClassifier, h]

/-- Concrete bridge theorem: the independently proved refused-edge property
drives the classifier to confession, and the returned evidence retains exactly
the supplied SafeStep proof object. -/
theorem safestep_guard_emits_confession
    (h : ConcreteSafeStepEvidence) :
    ∃ E : SafeStepConfessionEvidence,
      E.safeStepEvidence = h ∧
      safeStepSemanticClassifier =
        .T3_confession "SafeStep.diagonal_forbiddenBranch" "KO7.Confluence"
          "diagonalDifferenceBranch" "LocalJoinSafe" := by
  refine ⟨safeStepConfessionEvidenceOf h, rfl, ?_⟩
  exact safeStepSemanticClassifier_eq_t3
    (concreteSafeStepEvidence_has_refused_edge h)

/-- Inhabited non-vacuity witness for the proof-carrying bridge. -/
theorem safestep_confession_nonempty :
    Nonempty SafeStepConfessionEvidence :=
  ⟨ko7SafeStepConfessionEvidence⟩

/-- Predicate exposing only the outer `T3_confession` constructor and its
four-field schema. -/
def IsT3Confession : TypedOutput -> Prop
| .T3_confession _ _ _ _ => True
| _ => False

/-- Both axes share the outer constructor and payload schema, but not the full
typed output.  Their theorem/certificate chains remain distinct. -/
theorem safestep_and_termination_share_t3_schema_not_full_output :
    IsT3Confession safeStepSemanticClassifier ∧
      IsT3Confession trsBoundaryVerdict ∧
      safeStepSemanticClassifier ≠ trsBoundaryVerdict := by
  have hT3 := safeStepSemanticClassifier_eq_t3
    ko7SafeStepConfessionEvidence.hasRefusedEdge
  refine ⟨?_, trivial, ?_⟩
  · rw [hT3]
    trivial
  · rw [hT3]
    decide

section AuditChecks

#check @ConcreteSafeStepEvidence
#check @concreteSafeStepEvidence
#check @RefusedEdgeCertificate
#check @HasRefusedEdge
#check @concreteSafeStepRefusedEdge
#check @concreteSafeStepEvidence_has_refused_edge
#check @SafeStepConfessionEvidence
#check @safeStepConfessionEvidenceOf
#check @ko7SafeStepConfessionEvidence
#check @SafeStepConfessionEvidence.hasRefusedEdge
#check @safeStepSemanticClassifier
#check @safeStepSemanticClassifier_eq_t3
#check @safeStepSemanticClassifier_eq_t4
#check @safestep_guard_emits_confession
#check @safestep_confession_nonempty
#check @safestep_and_termination_share_t3_schema_not_full_output

#print axioms concreteSafeStepEvidence
#print axioms concreteSafeStepEvidence_has_refused_edge
#print axioms safeStepSemanticClassifier_eq_t3
#print axioms safeStepSemanticClassifier_eq_t4
#print axioms safestep_guard_emits_confession
#print axioms safestep_confession_nonempty
#print axioms safestep_and_termination_share_t3_schema_not_full_output

end AuditChecks

end OperatorKO7.Meta.SafeStep.SafeStepConfessionBridge
