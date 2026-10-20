import OperatorKO7.Meta.RDRSNonKO7Instances
import OperatorKO7.Meta.KO7RDRSAdapter

/-!
# Canonical Witness Universality

This module packages generic `RightDuplicatingRecursorSchema` (RDRS) witness
facts into a `CanonicalRDRSWitness`, then instantiates the canonical witness
for four RDRS instances: KO7 itself (via the role-aware adapter in
`Meta/KO7RDRSAdapter.lean`), textbook duplication, the tagged-binary
recursor, and the depth-counter recursor.

The KO7 canonical witness is connected to the kernel `Step.R_rec_succ` rule by
the adapter's projection lemma. The canonical witness layer exposes these four
witnesses together with transfer lemmas through the generic
`CanonicalRDRSWitness` interface.
-/

namespace OperatorKO7.StepDuplicating
namespace CanonicalWitnessUniversality

open RDRSNonKO7Instances
open KO7RDRSAdapter
open RightDuplicatingRecursorSchema

/-- A canonical structural witness packages the RDRS-level facts already proved
for a right-duplicating recursor rule. This layer transfers only
payload-duplication facts that are immediate from the RDRS shell, not later
  observer, measure-class, or operational firability theorems. -/
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

/-- The canonical witness's carrier-supplied firability declaration. This
projection is metadata and is not a rewrite-step witness. -/
def CanonicalRDRSWitness.declaredClosedFirability (W : CanonicalRDRSWitness) : Prop :=
  W.schema.declaredClosedFirability

/-- Canonical witness for KO7 via the role-aware adapter of
`Meta/KO7RDRSAdapter.lean`. The adapter projects to the KO7 kernel
`Step.R_rec_succ` reduction for every role assignment. -/
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

/-- The non-KO7 witness list contains the textbook, tagged-binary, and
depth-counter instances. -/
def nonKO7CanonicalWitnesses : List CanonicalRDRSWitness :=
  [textbookCanonicalWitness, taggedBinaryCanonicalWitness, depthCounterCanonicalWitness]

theorem nonKO7CanonicalWitnesses_length :
    nonKO7CanonicalWitnesses.length = 3 := by
  rfl

/-- The four structural witnesses: KO7 together with the three non-KO7
schema instances. -/
def canonicalWitnesses : List CanonicalRDRSWitness :=
  [ko7CanonicalWitness, textbookCanonicalWitness,
   taggedBinaryCanonicalWitness, depthCounterCanonicalWitness]

theorem canonicalWitnesses_length :
    canonicalWitnesses.length = 4 := by
  rfl

/-- The KO7 schema's declared firability marker. Operational firing is supplied
by `ko7CanonicalWitness_projects_to_kernel_step` below. -/
theorem ko7CanonicalWitness_declaredClosedFirability :
    ko7CanonicalWitness.declaredClosedFirability := by
  trivial

/-- The textbook schema's declared firability marker. No rewrite relation is
part of `RightDuplicatingRecursorSchema`. -/
theorem textbookCanonicalWitness_declaredClosedFirability :
    textbookCanonicalWitness.declaredClosedFirability := by
  trivial

/-- The tagged-binary schema's declared firability marker. No rewrite relation
is part of `RightDuplicatingRecursorSchema`. -/
theorem taggedBinaryCanonicalWitness_declaredClosedFirability :
    taggedBinaryCanonicalWitness.declaredClosedFirability := by
  trivial

/-- The depth-counter schema's declared firability marker. No rewrite relation
is part of `RightDuplicatingRecursorSchema`. -/
theorem depthCounterCanonicalWitness_declaredClosedFirability :
    depthCounterCanonicalWitness.declaredClosedFirability := by
  trivial

/-- Every concrete role assignment of the KO7 canonical witness projects to
the live kernel rule `Step.R_rec_succ`. Unlike the declaration above, this is an
operational rewrite-step theorem. -/
theorem ko7CanonicalWitness_projects_to_kernel_step (b s n : Trace) :
    Step
      (KO7RDRSTerm.project b s n ko7CanonicalWitness.schema.lhs)
      (KO7RDRSTerm.project b s n ko7CanonicalWitness.schema.rhs) := by
  simpa [ko7CanonicalWitness, canonicalWitnessOfRDRS] using
    ko7RDRS_projects_to_kernel_step b s n

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
The kernel `Step.R_rec_succ` connection is proved in
`Meta/KO7RDRSAdapter.lean` by `ko7RDRS_projects_to_kernel_step`. -/
theorem ko7_as_canonical_recursiveFamily_witness :
    ko7CanonicalWitness.schema = ko7RDRS := rfl

end CanonicalWitnessUniversality
end OperatorKO7.StepDuplicating
