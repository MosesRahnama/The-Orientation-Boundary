import OperatorKO7.Meta.DistinctionBoundary.WriteClosure

set_option autoImplicit false

open OperatorKO7.Meta.DistinctionBoundary.WriteClosure

#check @SelectionLE
#check @WriteClosed
#check @writeClosure
#check @writeClosure_extensive
#check @writeClosure_monotone
#check @writeClosure_recD_iff
#check @writeClosure_eqW_iff
#check @writeClosure_closed
#check @writeClosure_idempotent
#check @writeClosure_least
#check @freezeEqW
#check @confluenceRepair
#check @confluenceRepair_extends_nonEqW
#check @confluenceRepair_freezes_eqW
#check @confluenceRepair_writeClosed
#check @confluenceRepair_confluent
#check @confluenceRepair_least
#check @freezeEqW_idempotent
#check @freezeEqW_eq_self_of_eqW_frozen
#check @confluenceRepair_idempotent
#check @recDSeed
#check @writeClosure_recDSeed_exact
#check @confluenceRepair_recDSeed_eq_writeClosure
#check @recDSeed_ne_writeClosure
#check @recDSeed_two_histories_same_repair
#check @recDSeed_not_confluent
#check @writeClosure_recDSeed_confluent
#check @recDSeed_writeClosure_changes_outcome

#print axioms SelectionLE
#print axioms WriteClosed
#print axioms writeClosure
#print axioms writeClosure_extensive
#print axioms writeClosure_monotone
#print axioms writeClosure_recD_iff
#print axioms writeClosure_eqW_iff
#print axioms writeClosure_closed
#print axioms writeClosure_idempotent
#print axioms writeClosure_least
#print axioms freezeEqW
#print axioms confluenceRepair
#print axioms confluenceRepair_extends_nonEqW
#print axioms confluenceRepair_freezes_eqW
#print axioms confluenceRepair_writeClosed
#print axioms confluenceRepair_confluent
#print axioms confluenceRepair_least
#print axioms freezeEqW_idempotent
#print axioms freezeEqW_eq_self_of_eqW_frozen
#print axioms confluenceRepair_idempotent
#print axioms recDSeed
#print axioms writeClosure_recDSeed_exact
#print axioms confluenceRepair_recDSeed_eq_writeClosure
#print axioms recDSeed_ne_writeClosure
#print axioms recDSeed_two_histories_same_repair
#print axioms recDSeed_not_confluent
#print axioms writeClosure_recDSeed_confluent
#print axioms recDSeed_writeClosure_changes_outcome
