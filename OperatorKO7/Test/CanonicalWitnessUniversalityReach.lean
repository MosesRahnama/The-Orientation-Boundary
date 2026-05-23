import OperatorKO7.Meta.CanonicalWitnessUniversality

/-!
# Reach tests for `Meta/CanonicalWitnessUniversality.lean`

Smoke-tests the Phase A.3 canonical-witness layer: generic packaging of RDRS
witness facts, the four required canonical witnesses (KO7 plus the three
non-KO7 instances), and the KO7-side adapter projection back to the live KO7
kernel `Step.R_rec_succ` reduction.
-/

namespace OperatorKO7.StepDuplicating
namespace CanonicalWitnessUniversality

#check @CanonicalRDRSWitness
#check @canonicalWitnessOfRDRS

#check @canonicalWitnessOfRDRS_schema
#check @canonicalWitnessTransferGapPos
#check @canonicalWitnessTransferRhsStrict
#check @canonicalWitnessTransferRhsPayloadPos

#check @ko7CanonicalWitness
#check @textbookCanonicalWitness
#check @taggedBinaryCanonicalWitness
#check @depthCounterCanonicalWitness

#check @nonKO7CanonicalWitnesses
#check @nonKO7CanonicalWitnesses_length
#check @canonicalWitnesses
#check @canonicalWitnesses_length

#check @ko7CanonicalWitness_closedFirability
#check @textbookCanonicalWitness_closedFirability
#check @taggedBinaryCanonicalWitness_closedFirability
#check @depthCounterCanonicalWitness_closedFirability

#check @ko7CanonicalWitness_gap_pos
#check @ko7CanonicalWitness_rhs_strict
#check @ko7CanonicalWitness_rhs_payload_pos
#check @ko7_as_canonical_recursiveFamily_witness

#check @KO7RDRSAdapter.ko7RDRS
#check @KO7RDRSAdapter.ko7RDRS_gap_pos
#check @KO7RDRSAdapter.ko7RDRS_rhs_strict
#check @KO7RDRSAdapter.ko7RDRS_rhs_payload_pos
#check @KO7RDRSAdapter.ko7RDRS_projects_to_kernel_step

example : ko7CanonicalWitness.schema = KO7RDRSAdapter.ko7RDRS := by
  simpa [ko7CanonicalWitness] using
    canonicalWitnessOfRDRS_schema KO7RDRSAdapter.ko7RDRS

example : textbookCanonicalWitness.schema = RDRSNonKO7Instances.textbookRDRS := by
  simpa [textbookCanonicalWitness] using
    canonicalWitnessOfRDRS_schema RDRSNonKO7Instances.textbookRDRS

example : taggedBinaryCanonicalWitness.schema = RDRSNonKO7Instances.taggedBinaryRDRS := by
  simpa [taggedBinaryCanonicalWitness] using
    canonicalWitnessOfRDRS_schema RDRSNonKO7Instances.taggedBinaryRDRS

example : depthCounterCanonicalWitness.schema = RDRSNonKO7Instances.depthCounterRDRS := by
  simpa [depthCounterCanonicalWitness] using
    canonicalWitnessOfRDRS_schema RDRSNonKO7Instances.depthCounterRDRS

example : 1 ≤ ko7CanonicalWitness.schema.distinguishedDuplicationGap := by
  exact canonicalWitnessTransferGapPos ko7CanonicalWitness

example : 1 ≤ textbookCanonicalWitness.schema.distinguishedDuplicationGap := by
  exact canonicalWitnessTransferGapPos textbookCanonicalWitness

example : 1 ≤ taggedBinaryCanonicalWitness.schema.distinguishedDuplicationGap := by
  exact canonicalWitnessTransferGapPos taggedBinaryCanonicalWitness

example : 1 ≤ depthCounterCanonicalWitness.schema.distinguishedDuplicationGap := by
  exact canonicalWitnessTransferGapPos depthCounterCanonicalWitness

example : canonicalWitnesses.length = 4 := canonicalWitnesses_length

example (b s n : OperatorKO7.Trace) :
    OperatorKO7.Step
      (KO7RDRSAdapter.KO7RDRSTerm.project b s n KO7RDRSAdapter.ko7RDRS.lhs)
      (KO7RDRSAdapter.KO7RDRSTerm.project b s n KO7RDRSAdapter.ko7RDRS.rhs) :=
  KO7RDRSAdapter.ko7RDRS_projects_to_kernel_step b s n

end CanonicalWitnessUniversality
end OperatorKO7.StepDuplicating
