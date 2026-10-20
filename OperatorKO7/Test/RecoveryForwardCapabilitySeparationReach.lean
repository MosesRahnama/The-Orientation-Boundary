import OperatorKO7.Meta.LicensedBoundaryCalculus.RecoveryForwardCapabilitySeparation

set_option autoImplicit false

open OperatorKO7.Meta.LicensedBoundaryCalculus

#check @RecoveryPolicy
#check @emptyRecoveryPolicy
#check @recoveryForwardStep
#check @ConfluentRecoveryPolicy
#check @emptyRecoveryPolicy_confluent
#check @rawRecoveryPolicy_not_confluent
#check @repairedRecoveryPolicy_confluent
#check @rawRecoveryForwardRequest
#check @repairedRecoveryForwardRequest
#check @rawRecoveryForward_boundary
#check @repairedRecoveryForward_safeRel
#check @repairedRecoveryForwardLicense
#check @rawRecoveryForwardRefusal
#check @ExternalRecoveryToken
#check @ExternalRecoveryToken.mk
#check @ExternalRecoveryToken.replay
#check @ExternalRecoveryToken.recover
#check @ExternalRecoveryToken.recover_replays
#check @rawHistoryRecoveryToken
#check @closedHistoryRecoveryToken
#check @same_record_multiple_histories
#check @confluenceRepair_no_global_left_inverse
#check @recovery_evidence_cannot_manufacture_forward_admission
#check @forward_admission_does_not_reconstruct_history
#check @recovery_role_is_not_forward_license

#print axioms RecoveryPolicy
#print axioms emptyRecoveryPolicy
#print axioms recoveryForwardStep
#print axioms ConfluentRecoveryPolicy
#print axioms emptyRecoveryPolicy_confluent
#print axioms rawRecoveryPolicy_not_confluent
#print axioms repairedRecoveryPolicy_confluent
#print axioms rawRecoveryForwardRequest
#print axioms repairedRecoveryForwardRequest
#print axioms rawRecoveryForward_boundary
#print axioms repairedRecoveryForward_safeRel
#print axioms repairedRecoveryForwardLicense
#print axioms rawRecoveryForwardRefusal
#print axioms ExternalRecoveryToken
#print axioms ExternalRecoveryToken.mk
#print axioms ExternalRecoveryToken.replay
#print axioms ExternalRecoveryToken.recover
#print axioms ExternalRecoveryToken.recover_replays
#print axioms rawHistoryRecoveryToken
#print axioms closedHistoryRecoveryToken
#print axioms same_record_multiple_histories
#print axioms confluenceRepair_no_global_left_inverse
#print axioms recovery_evidence_cannot_manufacture_forward_admission
#print axioms forward_admission_does_not_reconstruct_history
#print axioms recovery_role_is_not_forward_license
