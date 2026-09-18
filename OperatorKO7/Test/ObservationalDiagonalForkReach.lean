import OperatorKO7.Meta.DistinctionBoundary.ObservationalDiagonalFork

/-!
Reach check for `Meta/DistinctionBoundary/ObservationalDiagonalFork.lean`: every public
declaration is elaborated and its axiom inventory printed.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.ObservationalDiagonalForkReach

open OperatorKO7.Meta.DistinctionBoundary.ObservationalDiagonalFork
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

#check @MapCone
#check @MapConeStep
#check @stable_normal
#check @novel_normal
#check @mapCone_verdicts_unjoinable
#check @mapCone_not_confluentAt_diagonal
#check @mapConePointed
#check @fork3EquivMapCone
#check @fork3Step_iff_mapConeStep
#check @fork3MapConeIso
#check @canonicalHom_mapCone_bijective
#check @MapConeLicensed
#check @mapConeLicensed_sub
#check @fork3LicensedStep_iff_mapConeLicensed
#check @fork3MapConeLicensedIso
#check @mapConeLocalRawIso
#check @mapConeLocalLicensedIso
#check @mapConeToTrace
#check @mapConeStep_iff_ko7Step
#check @mapConeLicensed_iff_ko7SafeStep
#check @novelty_refused
#check @licensed_reach_diagonal
#check @licensed_confluentAt_diagonal
#check @licensed_never_reaches_novel

#print axioms MapCone
#print axioms MapConeStep
#print axioms stable_normal
#print axioms novel_normal
#print axioms mapCone_verdicts_unjoinable
#print axioms mapCone_not_confluentAt_diagonal
#print axioms mapConePointed
#print axioms fork3EquivMapCone
#print axioms fork3Step_iff_mapConeStep
#print axioms fork3MapConeIso
#print axioms canonicalHom_mapCone_bijective
#print axioms MapConeLicensed
#print axioms mapConeLicensed_sub
#print axioms fork3LicensedStep_iff_mapConeLicensed
#print axioms fork3MapConeLicensedIso
#print axioms mapConeLocalRawIso
#print axioms mapConeLocalLicensedIso
#print axioms mapConeToTrace
#print axioms mapConeStep_iff_ko7Step
#print axioms mapConeLicensed_iff_ko7SafeStep
#print axioms novelty_refused
#print axioms licensed_reach_diagonal
#print axioms licensed_confluentAt_diagonal
#print axioms licensed_never_reaches_novel

#check @pairObservation
#print axioms pairObservation

#check @RecordCorrect
#print axioms RecordCorrect

#check @recordCorrect_stable_iff
#print axioms recordCorrect_stable_iff

#check @recordCorrect_novel_iff
#print axioms recordCorrect_novel_iff

#check @recordCorrect_self_iff
#print axioms recordCorrect_self_iff

#check @RecordCorrect.unique
#print axioms RecordCorrect.unique

#check @intendedRecord
#print axioms intendedRecord

#check @intendedRecord_correct
#print axioms intendedRecord_correct

#check @recordCorrect_iff_intended
#print axioms recordCorrect_iff_intended

#check @ObservedDecoderCorrect
#print axioms ObservedDecoderCorrect

#check @ObservedDecoderCorrect.injective
#print axioms ObservedDecoderCorrect.injective

#check @observerDecoder
#print axioms observerDecoder

#check @observerDecoder_correct_of_injective
#print axioms observerDecoder_correct_of_injective

#check @observedDecoder_exists_iff_injective
#print axioms observedDecoder_exists_iff_injective

#check @collapsed_pair_decoder_failure
#print axioms collapsed_pair_decoder_failure

#check @intendedRecord_licensed_iff_injective
#print axioms intendedRecord_licensed_iff_injective

#check @joint_decoder_exists_iff_injective
#print axioms joint_decoder_exists_iff_injective

#check @novelty_requires_exogenous_distinction
#print axioms novelty_requires_exogenous_distinction

#check @TruthLicensed
#print axioms TruthLicensed

#check @RecordCorrect.raw_edge
#print axioms RecordCorrect.raw_edge

#check @RecordCorrect.raw_normal
#print axioms RecordCorrect.raw_normal

#check @truthLicensed_deterministic
#print axioms truthLicensed_deterministic

#check @truthLicensed_record_normal
#print axioms truthLicensed_record_normal

#check @truthLicensed_reach_diagonal
#print axioms truthLicensed_reach_diagonal

#check @truthLicensed_confluentAt_diagonal
#print axioms truthLicensed_confluentAt_diagonal

#check @truthLicensed_self_iff
#print axioms truthLicensed_self_iff

example (decoder : Unit × Unit → MapCone) :
    ¬ (RecordCorrect false false (decoder ((), ())) ∧
      RecordCorrect false true (decoder ((), ()))) :=
  collapsed_pair_decoder_failure (fun _ : Bool => ()) decoder rfl (by decide)

example : ObservedDecoderCorrect (fun x : Bool => x) observerDecoder :=
  observerDecoder_correct_of_injective _ (fun _ _ h => h)

example : RecordCorrect false true (intendedRecord false true) :=
  intendedRecord_correct false true

example : TruthLicensed false true .diagonal .novel := by
  exact ⟨MapConeStep.toNovel, (recordCorrect_novel_iff false true).mpr (by decide)⟩

example : ¬ TruthLicensed false true .diagonal .stable := by
  intro h
  exact Bool.noConfusion ((recordCorrect_stable_iff false true).mp h.2)

example : ConfluentAt (TruthLicensed false true) .diagonal :=
  truthLicensed_confluentAt_diagonal false true

end OperatorKO7.Test.ObservationalDiagonalForkReach
