import OperatorKO7.Meta.RDRSNonKO7Instances
import OperatorKO7.Meta.KO7RDRSAdapter

/-!
# Canonical Witness Universality

Phase A.3 of the recursive-family expansion roadmap.

This module packages generic `RightDuplicatingRecursorSchema` (RDRS) witness
facts into a `CanonicalRDRSWitness`, then instantiates the canonical witness
on every RDRS the roadmap names: KO7 itself (via the role-aware adapter in
`Meta/KO7RDRSAdapter.lean`), textbook duplication, the tagged-binary
recursor, and the depth-counter recursor.

The KO7 canonical witness is connected to the live KO7 kernel `Step.R_rec_succ`
rule by the adapter's projection lemma. The canonical witness layer exposes
the four full canonical witnesses required by the validation table together
with the same transfer lemmas through the generic `CanonicalRDRSWitness`
interface.
-/

namespace OperatorKO7.StepDuplicating
namespace CanonicalWitnessUniversality

open RDRSNonKO7Instances
open KO7RDRSAdapter
open RightDuplicatingRecursorSchema

/-- A canonical structural witness packages the RDRS-level facts already proved
for a right-duplicating recursor rule. This layer transfers only
payload-duplication facts that are immediate from the RDRS shell, not later
observer or measure-class theorems. -/
structure CanonicalRDRSWitness where
  schema : RightDuplicatingRecursorSchema
  gapPos : 1 ≤ schema.distinguishedDuplicationGap
  rhsStrict :
    schema.payloadCount schema.distinguishedPayload schema.lhs <
      schema.payloadCount schema.distinguishedPayload schema.rhs
  rhsPayloadPos :
    0 < schema.payloadCount schema.distinguishedPayload schema.rhs

/-- Every RDRS instance canonically yields the structural witness facts proved
in the schema shell. -/
def canonicalWitnessOfRDRS (S : RightDuplicatingRecursorSchema) : CanonicalRDRSWitness where
  schema := S
  gapPos := S.one_le_distinguishedDuplicationGap
  rhsStrict := S.rhs_count_gt_lhs_count
  rhsPayloadPos := S.distinguished_payload_count_rhs_pos

/-- The canonical witness remembers its source schema definitionally. -/
theorem canonicalWitnessOfRDRS_schema
    (S : RightDuplicatingRecursorSchema) :
    (canonicalWitnessOfRDRS S).schema = S := rfl

/-- Transfer the canonical witness's positive duplication gap back to its
underlying RDRS instance. -/
theorem canonicalWitnessTransferGapPos
    (W : CanonicalRDRSWitness) :
    1 ≤ W.schema.distinguishedDuplicationGap :=
  W.gapPos

/-- Transfer the strict rhs-vs-lhs payload inequality back to the underlying
RDRS instance. -/
theorem canonicalWitnessTransferRhsStrict
    (W : CanonicalRDRSWitness) :
    W.schema.payloadCount W.schema.distinguishedPayload W.schema.lhs <
      W.schema.payloadCount W.schema.distinguishedPayload W.schema.rhs :=
  W.rhsStrict

/-- Transfer rhs payload positivity back to the underlying RDRS instance. -/
theorem canonicalWitnessTransferRhsPayloadPos
    (W : CanonicalRDRSWitness) :
    0 < W.schema.payloadCount W.schema.distinguishedPayload W.schema.rhs :=
  W.rhsPayloadPos

/-- The canonical witness's tracked closed-firability predicate. -/
def CanonicalRDRSWitness.closedFirability (W : CanonicalRDRSWitness) : Prop :=
  W.schema.firesOnClosedTerms

/-- Canonical witness for KO7 via the role-aware adapter of
`Meta/KO7RDRSAdapter.lean`. The adapter projects to the live KO7 kernel
`Step.R_rec_succ` reduction for every role assignment, so this is a
full canonical witness, not a status surface. -/
def ko7CanonicalWitness : CanonicalRDRSWitness :=
  canonicalWitnessOfRDRS ko7RDRS

/-- Canonical witness for the textbook duplicating rule. -/
def textbookCanonicalWitness : CanonicalRDRSWitness :=
  canonicalWitnessOfRDRS textbookRDRS

/-- Canonical witness for the `Bit1` branch of the tagged-binary recursor. -/
def taggedBinaryCanonicalWitness : CanonicalRDRSWitness :=
  canonicalWitnessOfRDRS taggedBinaryRDRS

/-- Canonical witness for the depth-counter recursor. -/
def depthCounterCanonicalWitness : CanonicalRDRSWitness :=
  canonicalWitnessOfRDRS depthCounterRDRS

/-- The Phase A.3 universality surface is non-vacuous: it contains the three
non-KO7 witnesses preserved from the first honest layer. -/
def nonKO7CanonicalWitnesses : List CanonicalRDRSWitness :=
  [textbookCanonicalWitness, taggedBinaryCanonicalWitness, depthCounterCanonicalWitness]

theorem nonKO7CanonicalWitnesses_length :
    nonKO7CanonicalWitnesses.length = 3 := by
  rfl

/-- The full non-vacuity list: KO7 together with the three non-KO7
canonical witnesses. -/
def canonicalWitnesses : List CanonicalRDRSWitness :=
  [ko7CanonicalWitness, textbookCanonicalWitness,
   taggedBinaryCanonicalWitness, depthCounterCanonicalWitness]

theorem canonicalWitnesses_length :
    canonicalWitnesses.length = 4 := by
  rfl

theorem ko7CanonicalWitness_closedFirability :
    ko7CanonicalWitness.closedFirability := by
  trivial

theorem textbookCanonicalWitness_closedFirability :
    textbookCanonicalWitness.closedFirability := by
  trivial

theorem taggedBinaryCanonicalWitness_closedFirability :
    taggedBinaryCanonicalWitness.closedFirability := by
  trivial

theorem depthCounterCanonicalWitness_closedFirability :
    depthCounterCanonicalWitness.closedFirability := by
  trivial

/-- Transfer lemma: KO7 has positive duplication gap through the same
canonical-witness interface as the non-KO7 witnesses. -/
theorem ko7CanonicalWitness_gap_pos :
    1 ≤ ko7CanonicalWitness.schema.distinguishedDuplicationGap :=
  canonicalWitnessTransferGapPos ko7CanonicalWitness

/-- Transfer lemma: KO7 has strict rhs-vs-lhs payload growth through the
canonical-witness interface. -/
theorem ko7CanonicalWitness_rhs_strict :
    ko7CanonicalWitness.schema.payloadCount
        ko7CanonicalWitness.schema.distinguishedPayload
        ko7CanonicalWitness.schema.lhs <
      ko7CanonicalWitness.schema.payloadCount
        ko7CanonicalWitness.schema.distinguishedPayload
        ko7CanonicalWitness.schema.rhs :=
  canonicalWitnessTransferRhsStrict ko7CanonicalWitness

/-- Transfer lemma: KO7 has positive rhs payload occurrence count through
the canonical-witness interface. -/
theorem ko7CanonicalWitness_rhs_payload_pos :
    0 < ko7CanonicalWitness.schema.payloadCount
          ko7CanonicalWitness.schema.distinguishedPayload
          ko7CanonicalWitness.schema.rhs :=
  canonicalWitnessTransferRhsPayloadPos ko7CanonicalWitness

/-- KO7 is exposed as a canonical recursive-family witness through the same
RDRS interface as the textbook, tagged-binary, and depth-counter witnesses.
This is the public KO7-side packaging that the canonical-witness universality
layer was supposed to ship; it is now unconditional, with the live KO7
kernel `Step.R_rec_succ` connection proved in
`Meta/KO7RDRSAdapter.lean` (see `ko7RDRS_projects_to_kernel_step`). -/
theorem ko7_as_canonical_recursiveFamily_witness :
    ko7CanonicalWitness.schema = ko7RDRS := rfl

end CanonicalWitnessUniversality
end OperatorKO7.StepDuplicating
