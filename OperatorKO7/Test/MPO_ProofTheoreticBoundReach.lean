import OperatorKO7.Meta.MPO_ProofTheoreticBound

/-! # MPO_ProofTheoreticBound reach and axiom check

Paired `#check @` and `#print axioms` for every public declaration of
`OperatorKO7/Meta/MPO_ProofTheoreticBound.lean`, including the comparison of the MPO envelope
`veblen 7 0` with the Feferman-Schuette ordinal `gamma0`.
-/

set_option autoImplicit false

#check @OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound
#print axioms OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound
#check @OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound_gt_one
#print axioms OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound_gt_one
#check @OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound_fixed
#print axioms OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound_fixed
#check @OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound_isSuccLimit
#print axioms OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound_isSuccLimit
#check @OperatorKO7.MPOProofTheoreticBound.rank_lt_seven
#print axioms OperatorKO7.MPOProofTheoreticBound.rank_lt_seven
#check @OperatorKO7.MPOProofTheoreticBound.rank_lt_seven_ord
#print axioms OperatorKO7.MPOProofTheoreticBound.rank_lt_seven_ord
#check @OperatorKO7.MPOProofTheoreticBound.veblen_lt_mpoVeblenBound_of_rank_lt
#print axioms OperatorKO7.MPOProofTheoreticBound.veblen_lt_mpoVeblenBound_of_rank_lt
#check @OperatorKO7.MPOProofTheoreticBound.mpoOrd_lt_mpoVeblenBound
#print axioms OperatorKO7.MPOProofTheoreticBound.mpoOrd_lt_mpoVeblenBound
#check @OperatorKO7.MPOProofTheoreticBound.wf_StepRev_mpo_below_veblen7
#print axioms OperatorKO7.MPOProofTheoreticBound.wf_StepRev_mpo_below_veblen7
#check @OperatorKO7.MPOProofTheoreticBound.gamma0
#print axioms OperatorKO7.MPOProofTheoreticBound.gamma0
#check @OperatorKO7.MPOProofTheoreticBound.gamma0_eq_gamma_zero
#print axioms OperatorKO7.MPOProofTheoreticBound.gamma0_eq_gamma_zero
#check @OperatorKO7.MPOProofTheoreticBound.veblen_gamma0_zero
#print axioms OperatorKO7.MPOProofTheoreticBound.veblen_gamma0_zero
#check @OperatorKO7.MPOProofTheoreticBound.gamma0_le_of_veblen_le
#print axioms OperatorKO7.MPOProofTheoreticBound.gamma0_le_of_veblen_le
#check @OperatorKO7.MPOProofTheoreticBound.seven_lt_epsilon0
#print axioms OperatorKO7.MPOProofTheoreticBound.seven_lt_epsilon0
#check @OperatorKO7.MPOProofTheoreticBound.veblen_seven_zero_lt_gamma0
#print axioms OperatorKO7.MPOProofTheoreticBound.veblen_seven_zero_lt_gamma0
#check @OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound_lt_gamma0
#print axioms OperatorKO7.MPOProofTheoreticBound.mpoVeblenBound_lt_gamma0
#check @OperatorKO7.MPOProofTheoreticBound.wf_StepRev_mpo_below_veblen7_below_gamma0
#print axioms OperatorKO7.MPOProofTheoreticBound.wf_StepRev_mpo_below_veblen7_below_gamma0
