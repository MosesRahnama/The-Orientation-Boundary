import OperatorKO7.Meta.DistinctionBoundary.GodelAcceptableNumbering

/-!
# Reach and axiom gate for the acceptable-numbering universalization
-/


set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

#check @pairArg
#check @IsUniversal
#check @EffectiveTransformer
#check @HasInternalSMN
#check @AcceptableNumbering
#check @AcceptableNumbering.mk
#check @AcceptableNumbering.universal
#check @AcceptableNumbering.smn
#check @pairProj
#check @pairSucc
#check @rightSpine
#check @compose_right_diverge_diverges
#check @not_convergesTo_of_diverges
#check @quote_pair_proj
#check @call_diverges_at_pair_proj
#check @decode_delta_none_of_not_void_chain
#check @pairProj_ne_void
#check @pairProj_ne_delta_void
#check @pairProj_ne_delta2_void
#check @deltaIter_pairProj_ne_void_chain
#check @quote_deltaIter_succ_pairProj
#check @call_diverges_at_deltaIter_succ_pairProj
#check @call_diverges_at_deltaIter_pairProj
#check @sizeOf_compose_assoc
#check @not_universal_at
#check @not_universal_on_proj_succ
#check @IsUniversal.forces_proj_succ
#check @no_universal_interpreter
#check @numbering_not_acceptable
#check @left_compose_any_has_extensional_fp
#check @freezeSuccOp_encode_diverge
#check @freezeSuccOp_encode_proj
#check @freezeSuccOp_encode_diverge_ne_proj
#check @freezeSuccOp_encode_is_app
#check @freezeOutDiverge
#check @freezeOutProj
#check @isCompoundB
#check @isCompound_iff_b
#check @compound_size_ge_three
#check @call_atom_not_compound
#check @freezeOutDiverge_is_compound
#check @freezeOutProj_is_compound
#check @not_two_distinct_compounds
#check @freezeSuccOp_not_effective
#check @freezeSucc_kill_compatible_with_missing_kleene_premises
#check @AccCode
#check @AccCode.embed
#check @AccCode.apply
#check @AccCode.cons
#check @AccCode.compose
#check @stepAcc
#check @convergesToAcc
#check @divergesAcc
#check @stepAcc_zero
#check @stepAcc_embed
#check @stepAcc_apply_app
#check @stepAcc_cons
#check @embed_tracks
#check @apply_is_universal
#check @InterpretsPartialCode
#check @apply_interprets_partialCode
#check @cons_pairs
#check @cons_pairs_embedded_code
#check @PartialCodeInterpreterExtension
#check @PartialCodeInterpreterExtension.mk
#check @PartialCodeInterpreterExtension.interpreter
#check @PartialCodeInterpreterExtension.pairing
#check @partialCode_interpreter_extension
#check @freezeSuccAcc
#check @freezeSuccOp_not_effective_on_embed
#print axioms pairArg
#print axioms IsUniversal
#print axioms EffectiveTransformer
#print axioms HasInternalSMN
#print axioms AcceptableNumbering
#print axioms AcceptableNumbering.mk
#print axioms AcceptableNumbering.universal
#print axioms AcceptableNumbering.smn
#print axioms pairProj
#print axioms pairSucc
#print axioms rightSpine
#print axioms compose_right_diverge_diverges
#print axioms not_convergesTo_of_diverges
#print axioms quote_pair_proj
#print axioms call_diverges_at_pair_proj
#print axioms decode_delta_none_of_not_void_chain
#print axioms pairProj_ne_void
#print axioms pairProj_ne_delta_void
#print axioms pairProj_ne_delta2_void
#print axioms deltaIter_pairProj_ne_void_chain
#print axioms quote_deltaIter_succ_pairProj
#print axioms call_diverges_at_deltaIter_succ_pairProj
#print axioms call_diverges_at_deltaIter_pairProj
#print axioms sizeOf_compose_assoc
#print axioms not_universal_at
#print axioms not_universal_on_proj_succ
#print axioms IsUniversal.forces_proj_succ
#print axioms no_universal_interpreter
#print axioms numbering_not_acceptable
#print axioms left_compose_any_has_extensional_fp
#print axioms freezeSuccOp_encode_diverge
#print axioms freezeSuccOp_encode_proj
#print axioms freezeSuccOp_encode_diverge_ne_proj
#print axioms freezeSuccOp_encode_is_app
#print axioms freezeOutDiverge
#print axioms freezeOutProj
#print axioms isCompoundB
#print axioms isCompound_iff_b
#print axioms compound_size_ge_three
#print axioms call_atom_not_compound
#print axioms freezeOutDiverge_is_compound
#print axioms freezeOutProj_is_compound
#print axioms not_two_distinct_compounds
#print axioms freezeSuccOp_not_effective
#print axioms freezeSucc_kill_compatible_with_missing_kleene_premises
#print axioms AccCode
#print axioms AccCode.embed
#print axioms AccCode.apply
#print axioms AccCode.cons
#print axioms AccCode.compose
#print axioms stepAcc
#print axioms convergesToAcc
#print axioms divergesAcc
#print axioms stepAcc_zero
#print axioms stepAcc_embed
#print axioms stepAcc_apply_app
#print axioms stepAcc_cons
#print axioms embed_tracks
#print axioms apply_is_universal
#print axioms InterpretsPartialCode
#print axioms apply_interprets_partialCode
#print axioms cons_pairs
#print axioms cons_pairs_embedded_code
#print axioms PartialCodeInterpreterExtension
#print axioms PartialCodeInterpreterExtension.mk
#print axioms PartialCodeInterpreterExtension.interpreter
#print axioms PartialCodeInterpreterExtension.pairing
#print axioms partialCode_interpreter_extension
#print axioms freezeSuccAcc
#print axioms freezeSuccOp_not_effective_on_embed

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
