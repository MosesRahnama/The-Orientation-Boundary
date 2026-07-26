import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSSemanticDirectMeasure
import OperatorKO7.Meta.RDRSSemanticPayloadSensitivity
import OperatorKO7.Meta.RDRSSemanticCertificate
import OperatorKO7.Meta.RDRSSemanticLensPump
import OperatorKO7.Meta.RDRSSemanticProjectionTransaction

set_option autoImplicit false

/-!
# RDRS Semantic Classifier

## Formal Scope

The classifier is total only over its closed five-constructor input grammar. Construction, transform, and notDirect cases carry audit Strings rather than typed escape evidence; the unclassified label is unreachable by construction.
-/

namespace OperatorKO7.RDRSSemanticClassifier

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticCertificate
open OperatorKO7.RDRSSemanticLensPump
open OperatorKO7.RDRSSemanticProjectionTransaction

/-! ### Classifier labels -/

/--
Proves: closed enum of the six classifier labels mandated by S5.
Does not prove: any meaning of the labels beyond their identity;
  meaning is established by the soundness theorems below.
Relation: enum metadata; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed inductive over six constants.
-/
inductive SemanticCertificateClass where
  | SemanticPayloadSensitiveBlocked
  | SemanticProjectionTransactionEscape
  | SemanticConstructionEscape
  | SemanticTransformEscape
  | SemanticNotDirect
  | TEMPORARY_UNCLASSIFIED
  deriving DecidableEq, Repr

/-! ### Normalized semantic certificate (the classifier input type) -/

/--
Proves: a closed inductive with five tagged input shapes. The first two carry
  typed evidence; the final three carry audit Strings:

  * `blockedDescent D` -- a `SemanticPayloadSensitiveLensPumpDescent`
    package (S3); the lens-pump barrier guarantees `¬ Orients`.
  * `projectionEscape E` -- a `SemanticProjectionTransactionEscape`
    (S4) carrying positive projected-orientation evidence.
  * `construction note` -- a String tag for a construction-style case;
    no construction witness is stored.
  * `transform note` -- a String tag for a transformation-style case;
    no transformation witness is stored.
  * `notDirect note` -- a String tag for a case declared outside the
    direct-payload-sensitive grammar.

  No constructor for `TEMPORARY_UNCLASSIFIED` exists; the classifier
  CANNOT produce that label on any inhabitant.

Does not prove: that arbitrary Lean evidence fits into one of the
  five productive cases; the caller must convert raw evidence into
  the normalized shape before classification.
Relation: parametric over the source RDRS step pair `R`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: closed grammar over five productive constructors. No
  `Prop := True` fake-directness slot, no semantic quotient counted
  as projection escape, no bare-erasure projection inhabitant.
-/
inductive NormalizedSemanticCertificate
    {B S N T : Type} (R : RDRSStep B S N T) : Type 1 where
  | blockedDescent
      (D : SemanticPayloadSensitiveLensPumpDescent R)
  | projectionEscape
      (E : SemanticProjectionTransactionEscape R)
  | construction (note : String)
  | transform (note : String)
  | notDirect (note : String)

/-! ### The classifier -/

/--
Proves: deterministic total classifier from
  `NormalizedSemanticCertificate R` to `SemanticCertificateClass`.
  Each constructor maps to directly one label; the
  `TEMPORARY_UNCLASSIFIED` label is unreachable.
Does not prove: anything about arbitrary raw measures; this function
  is closed over the five productive constructors of the normalized
  certificate inductive.
Relation: structural projection on the normalized certificate
  inductive; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (definitional `match`).
Scope: closed enum.
-/
def semanticClassify {B S N T : Type} {R : RDRSStep B S N T} :
    NormalizedSemanticCertificate R → SemanticCertificateClass
  | .blockedDescent _   => .SemanticPayloadSensitiveBlocked
  | .projectionEscape _ => .SemanticProjectionTransactionEscape
  | .construction _     => .SemanticConstructionEscape
  | .transform _        => .SemanticTransformEscape
  | .notDirect _        => .SemanticNotDirect

/-! ### Required theorems -/

/--
Proves: **classifier totality.** Every inhabitant of
  `NormalizedSemanticCertificate R` is mapped to one of the five
  productive labels; the `TEMPORARY_UNCLASSIFIED` slot is never
  produced.
Does not prove: that arbitrary raw Lean functions admit a normalized
  certificate; the totality is over the closed inductive ONLY.
Relation: closed-enum partition.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (`cases` + definitional reduction; closed by
  `decide` on each constructor).
Scope: every `c : NormalizedSemanticCertificate R`.
-/
theorem semantic_classifier_total
    {B S N T : Type} {R : RDRSStep B S N T}
    (c : NormalizedSemanticCertificate R) :
    semanticClassify c = SemanticCertificateClass.SemanticPayloadSensitiveBlocked
      ∨ semanticClassify c =
          SemanticCertificateClass.SemanticProjectionTransactionEscape
      ∨ semanticClassify c =
          SemanticCertificateClass.SemanticConstructionEscape
      ∨ semanticClassify c =
          SemanticCertificateClass.SemanticTransformEscape
      ∨ semanticClassify c =
          SemanticCertificateClass.SemanticNotDirect := by
  cases c with
  | blockedDescent _ =>
      exact Or.inl rfl
  | projectionEscape _ =>
      exact Or.inr (Or.inl rfl)
  | construction _ =>
      exact Or.inr (Or.inr (Or.inl rfl))
  | transform _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | notDirect _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/--
Proves: **zero unclassified.** No inhabitant of
  `NormalizedSemanticCertificate R` is classified
  `TEMPORARY_UNCLASSIFIED`. The residual label is unreachable.
Does not prove: that no Lean object whatsoever could be tagged
  `TEMPORARY_UNCLASSIFIED`; only that the closed normalized
  certificate's classifier never produces it.
Relation: closed enum.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c : NormalizedSemanticCertificate R`.
-/
theorem semantic_temporary_unclassified_count_is_zero
    {B S N T : Type} {R : RDRSStep B S N T}
    (c : NormalizedSemanticCertificate R) :
    semanticClassify c ≠ SemanticCertificateClass.TEMPORARY_UNCLASSIFIED := by
  cases c <;> intro h <;> cases h

/--
Proves: **payload-sensitive-blocked soundness.** If the classifier
  routes a normalized certificate to
  `SemanticPayloadSensitiveBlocked`, then the certificate carries a
  decisive payload-sensitive lens-pump descent witness `D`, and
  hence (by S3's universal lens-pump barrier) the semantic measure
  attached to `D` does not orient `R`.
Does not prove: source-system SN. The lens-pump barrier produces
  `¬ Orients`, a single-step orientation refutation; SN closure is the
  separate K-check 7 layer.
Relation: source `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c` classified `SemanticPayloadSensitiveBlocked`.
-/
theorem semantic_payload_sensitive_blocked_sound
    {B S N T : Type} {R : RDRSStep B S N T}
    (c : NormalizedSemanticCertificate R)
    (h : semanticClassify c =
      SemanticCertificateClass.SemanticPayloadSensitiveBlocked) :
    ∃ D : SemanticPayloadSensitiveLensPumpDescent R,
      c = NormalizedSemanticCertificate.blockedDescent D ∧
        ¬ Orients R
            D.certificate.toSemanticOrientationCertificate.measure.μ
            D.certificate.toSemanticOrientationCertificate.measure.ltA := by
  cases c with
  | blockedDescent D =>
      refine ⟨D, rfl, ?_⟩
      exact no_orients_of_semantic_payload_sensitive_decisive_descent D
  | projectionEscape _ => cases h
  | construction _     => cases h
  | transform _        => cases h
  | notDirect _        => cases h

/--
Proves: **projection-transaction-escape soundness.** If the classifier
  routes a normalized certificate to
  `SemanticProjectionTransactionEscape`, then the certificate carries
  a `SemanticProjectionTransactionEscape E` whose `lifted_orients`
  delivers source-step orientation transport.
Does not prove: source-system SN. `lifted_orients` is single-step,
  not an SN theorem.
Relation: source `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c` classified `SemanticProjectionTransactionEscape`.
-/
theorem semantic_projection_transaction_escape_sound
    {B S N T : Type} {R : RDRSStep B S N T}
    (c : NormalizedSemanticCertificate R)
    (h : semanticClassify c =
      SemanticCertificateClass.SemanticProjectionTransactionEscape) :
    ∃ E : SemanticProjectionTransactionEscape R,
      c = NormalizedSemanticCertificate.projectionEscape E ∧
        Orients R E.liftedMeasure E.transaction.semanticMeasure.ltA := by
  cases c with
  | blockedDescent _ => cases h
  | projectionEscape E =>
      refine ⟨E, rfl, ?_⟩
      exact E.lifted_orients
  | construction _ => cases h
  | transform _    => cases h
  | notDirect _    => cases h

/--
Proves: **construction-escape is outside the direct branch.** If the
  classifier routes a normalized certificate to
  `SemanticConstructionEscape`, the certificate is a
  `construction note` constructor: it carries NO
  `SemanticPayloadSensitiveLensPumpDescent` witness and NO
  `SemanticProjectionTransactionEscape` witness, so by structural
  case analysis it is not a direct payload-sensitive descent or a
  projection-transaction escape.
Does not prove: arbitrary "construction" Lean evidence falls here;
  the caller normalizes evidence to the inductive constructor.
Relation: structural projection on the normalized certificate
  inductive.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c` classified `SemanticConstructionEscape`.
-/
theorem semantic_construction_escape_outside_direct
    {B S N T : Type} {R : RDRSStep B S N T}
    (c : NormalizedSemanticCertificate R)
    (h : semanticClassify c =
      SemanticCertificateClass.SemanticConstructionEscape) :
    ∃ note : String,
      c = NormalizedSemanticCertificate.construction note ∧
        (∀ D : SemanticPayloadSensitiveLensPumpDescent R,
          c ≠ NormalizedSemanticCertificate.blockedDescent D) ∧
        (∀ E : SemanticProjectionTransactionEscape R,
          c ≠ NormalizedSemanticCertificate.projectionEscape E) := by
  cases c with
  | blockedDescent _   => cases h
  | projectionEscape _ => cases h
  | construction note =>
      refine ⟨note, rfl, ?_, ?_⟩
      · intro D heq; cases heq
      · intro E heq; cases heq
  | transform _ => cases h
  | notDirect _ => cases h

/--
Proves: **transform-escape is outside the direct branch.** Same
  shape as `semantic_construction_escape_outside_direct`, for the
  `transform` constructor.
Does not prove: that arbitrary transformations satisfy the
  `transform` slot; the caller normalizes evidence first.
Relation: structural projection.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c` classified `SemanticTransformEscape`.
-/
theorem semantic_transform_escape_outside_direct
    {B S N T : Type} {R : RDRSStep B S N T}
    (c : NormalizedSemanticCertificate R)
    (h : semanticClassify c =
      SemanticCertificateClass.SemanticTransformEscape) :
    ∃ note : String,
      c = NormalizedSemanticCertificate.transform note ∧
        (∀ D : SemanticPayloadSensitiveLensPumpDescent R,
          c ≠ NormalizedSemanticCertificate.blockedDescent D) ∧
        (∀ E : SemanticProjectionTransactionEscape R,
          c ≠ NormalizedSemanticCertificate.projectionEscape E) := by
  cases c with
  | blockedDescent _   => cases h
  | projectionEscape _ => cases h
  | construction _     => cases h
  | transform note =>
      refine ⟨note, rfl, ?_, ?_⟩
      · intro D heq; cases heq
      · intro E heq; cases heq
  | notDirect _ => cases h

/--
Proves: **not-direct soundness.** If the classifier routes to
  `SemanticNotDirect`, the certificate is a `notDirect note`
  constructor: not a direct payload-sensitive descent, not a
  projection-transaction escape.
Does not prove: any positive statement about the underlying
  evidence; the `notDirect` slot is structurally inert.
Relation: structural projection.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c` classified `SemanticNotDirect`.
-/
theorem semantic_not_direct_sound
    {B S N T : Type} {R : RDRSStep B S N T}
    (c : NormalizedSemanticCertificate R)
    (h : semanticClassify c =
      SemanticCertificateClass.SemanticNotDirect) :
    ∃ note : String,
      c = NormalizedSemanticCertificate.notDirect note ∧
        (∀ D : SemanticPayloadSensitiveLensPumpDescent R,
          c ≠ NormalizedSemanticCertificate.blockedDescent D) ∧
        (∀ E : SemanticProjectionTransactionEscape R,
          c ≠ NormalizedSemanticCertificate.projectionEscape E) := by
  cases c with
  | blockedDescent _   => cases h
  | projectionEscape _ => cases h
  | construction _     => cases h
  | transform _        => cases h
  | notDirect note =>
      refine ⟨note, rfl, ?_, ?_⟩
      · intro D heq; cases heq
      · intro E heq; cases heq

/-! ### Audit anchor and reachability -/

/-- Audit anchor for the S5 classifier surface. -/
def rdrs_semantic_classifier_anchor : String :=
  "OperatorKO7.RDRSSemanticClassifier.semantic_classifier_total"

end OperatorKO7.RDRSSemanticClassifier
