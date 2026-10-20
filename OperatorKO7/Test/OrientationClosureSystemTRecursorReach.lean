import OperatorKO7.Meta.Methods.OrientationClosure.SystemTRecursor

/-! # SystemTRecursor reach and axiom check -/

#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.fvar
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.fvar
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.bvar
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.bvar
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.zero
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.zero
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.succ
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.succ
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.app
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.app
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.lam
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.lam
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.iter
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.iter
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.recR
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.recR
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.openAt
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TTerm.openAt
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.beta
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.beta
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itZero
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itZero
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itSucc
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itSucc
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recZero
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recZero
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recSucc
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recSucc
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.succ
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.succ
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.appL
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.appL
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.appR
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.appR
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.lam
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.lam
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itB
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itB
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itS
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itS
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itN
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.itN
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recB
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recB
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recS
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recS
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recN
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.TStep.recN
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iteratorSchema
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iteratorSchema
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.foldWith
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.foldWith
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold_eq_foldWith
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold_eq_foldWith
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.unfoldT
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.unfoldT
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.unfoldT_iterFold
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.unfoldT_iterFold
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold_injective
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold_injective
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.fvar
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.fvar
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.zero
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.zero
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.succ
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.succ
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.app
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.app
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.iter
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.IterFree.iter
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFree_iterFold
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFree_iterFold
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold_unfoldT
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold_unfoldT
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.mem_range_iterFold_iff
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.mem_range_iterFold_iff
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tStep_plug
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tStep_plug
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tStep_of_rootStep
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tStep_of_rootStep
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tStep_of_contextStep
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tStep_of_contextStep
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFree_step
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFree_step
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tStep_iterFold_closed
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tStep_iterFold_closed
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.contextStep_iff_tStep
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.contextStep_iff_tStep
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterEmbedding
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterEmbedding
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterRelIso
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterRelIso
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold_acc
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFold_acc
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFree_acc
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterFree_acc
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImageSchema
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImageSchema
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImageIso
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImageIso
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_orients_iff
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_orients_iff
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_exact_criterion
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_exact_criterion
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_coupling
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_coupling
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_barrier_cell
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_barrier_cell
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.mk
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.mk
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map_base
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map_base
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map_succ
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map_succ
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map_wrap
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map_wrap
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map_recur
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.map_recur
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.foldWithHom
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.foldWithHom
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.foldWithHom_var
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.foldWithHom_var
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaHom_eq_foldWith
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaHom_eq_foldWith
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.var_irreducible
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.var_irreducible
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.betaAssignment_not_reflecting
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.betaAssignment_not_reflecting
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.mk
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.mk
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.boundedBoundedOrienter
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.boundedBoundedOrienter
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.boundedBoundedNonorienter
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.boundedBoundedNonorienter
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.unboundedUnboundedOrienter
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.unboundedUnboundedOrienter
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.unboundedUnboundedNonorienter
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.unboundedUnboundedNonorienter
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.boundedUnboundedOrienter
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.boundedUnboundedOrienter
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.boundedUnboundedNonorienter
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.boundedUnboundedNonorienter
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.wrapBoundedAt_pullback
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.wrapBoundedAt_pullback
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.gainBoundedAt_pullback
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.gainBoundedAt_pullback
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.wrapUnboundedAt_pullback
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.wrapUnboundedAt_pullback
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.gainUnboundedAt_pullback
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.gainUnboundedAt_pullback
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.orients_pullback
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.orients_pullback
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.not_orients_pullback
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.SchemaHom.not_orients_pullback
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.pullback
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.NonBarrierCellVerdicts.pullback
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.freeSchema_empty_nonBarrierCellVerdicts
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.freeSchema_empty_nonBarrierCellVerdicts
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.closeVarsHom
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.closeVarsHom
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.closeVarsHom_surjective
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.closeVarsHom_surjective
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.freeSchema_nonBarrierCellVerdicts
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.freeSchema_nonBarrierCellVerdicts
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaIsoSymmHom
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaIsoSymmHom
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_nonbarrier_cells_have_both_verdicts
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_nonbarrier_cells_have_both_verdicts
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_four_cells
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterImage_four_cells
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.fill2
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.fill2
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterator_wrapper_realizes
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.iterator_wrapper_realizes
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.fill2With
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.fill2With
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tTermSize
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tTermSize
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.fill2With_indep_or_size_le
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.fill2With_indep_or_size_le
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_two_hole_context_realizes_recursor
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_two_hole_context_realizes_recursor
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_two_hole_context_with_free_variables_realizes_recursor
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_two_hole_context_with_free_variables_realizes_recursor
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.liftHoles
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.liftHoles
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.fill2With_liftHoles
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.fill2With_liftHoles
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_two_hole_wrapper_realizes_recursor
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_two_hole_wrapper_realizes_recursor
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.mk
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.mk
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.T
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.T
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.base
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.base
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.succ
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.succ
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.wrap3
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.wrap3
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.recur
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.CounterWrapSchema.recur
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.recursorSchema
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.recursorSchema
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.recursorSchema_rule
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.recursorSchema_rule
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.counterBlind
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.counterBlind
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.counterBlind_rule
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.counterBlind_rule
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.wrapperCost3Z
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.wrapperCost3Z
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.counterGain3Z
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.counterGain3Z
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.orients3_all_iff
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.orients3_all_iff
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.retained_wrapper3_forces_counter_coupled_gain
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.retained_wrapper3_forces_counter_coupled_gain
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_orientation3_of_counter_bounded_gain
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_orientation3_of_counter_bounded_gain
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_orientation3_of_payload_bounded_gain
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.no_orientation3_of_payload_bounded_gain
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight_orients_iterator
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight_orients_iterator
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight_recursor_iff
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight_recursor_iff
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.numeral
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.numeral
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight_numeral
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight_numeral
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight_not_orients_recursor
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.schemaWeight_not_orients_recursor
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tWeight
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tWeight
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tWeight_orients_recursor
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tWeight_orients_recursor
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tWeight_retains3_and_gain
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.tWeight_retains3_and_gain
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.fvar
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.fvar
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.bvar
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.bvar
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.zero
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.zero
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.succ
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.succ
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.app
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.app
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.iter
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.iter
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.recR
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.LamFree.recR
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.lamFree_step
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.lamFree_step
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.lamFree_acc_aux
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.lamFree_acc_aux
#check @OperatorKO7.Methods.OrientationClosure.SystemTRecursor.lamFree_acc
#print axioms OperatorKO7.Methods.OrientationClosure.SystemTRecursor.lamFree_acc

namespace OrientationClosureSystemTRecursorReach

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.SystemTRecursor

/-! Node C16: the four-cell theorem on the iterator image at closed terms and at natural-number
variables. -/

example : NonBarrierCellVerdicts (iterImageSchema Empty) :=
  iterImage_nonbarrier_cells_have_both_verdicts Empty

example : NonBarrierCellVerdicts (iterImageSchema Nat) :=
  (iterImage_four_cells Nat).2.2

example : NonBarrierCellVerdicts (freeSchema Bool) :=
  freeSchema_nonBarrierCellVerdicts Bool

/-! Node C17: the general statement at another target type and another type of further variables,
the free-variable form, and the closed two-hole statement as its instance. -/

example : ¬ ∃ W : TTerm (Bool ⊕ Bool), ∀ b s n : TTerm Empty,
    fill2With (fun _ => TTerm.zero) s (.recR b s n) W = .app (.app s n) (.recR b s n) :=
  no_two_hole_context_realizes_recursor _

example : ¬ ∃ W : TTerm (Bool ⊕ String), ∀ b s n : TTerm String,
    fill2With TTerm.fvar s (.recR b s n) W = .app (.app s n) (.recR b s n) :=
  no_two_hole_context_with_free_variables_realizes_recursor

example : ¬ ∃ W : TTerm Bool, ∀ b s n : TTerm Nat,
    fill2 s (.recR b s n) W = .app (.app s n) (.recR b s n) :=
  fun ⟨W, hW⟩ => no_two_hole_context_realizes_recursor (κ := Empty) (ν := Nat) Empty.elim
    ⟨liftHoles W, fun b s n => (fill2With_liftHoles Empty.elim s (.recR b s n) W).trans (hW b s n)⟩

/-! Non-vacuity of the context class: a context with a further variable realizes the iterator
rule, and one that reads the further variable in the counter position matches the recursor rule at
the counter `zero`; only the quantification over every counter fails. -/

example : ∃ W : TTerm (Bool ⊕ Unit), ∀ b s n : TTerm Nat,
    fill2With (fun _ => TTerm.zero) s (.iter b s n) W = .app s (.iter b s n) :=
  ⟨.app (.fvar (.inl false)) (.fvar (.inl true)), fun _ _ _ => rfl⟩

example : fill2With (fun _ : Unit => (TTerm.zero : TTerm Nat)) .zero (.recR .zero .zero .zero)
    (.app (.app (.fvar (.inl false)) (.fvar (.inr ()))) (.fvar (.inl true))) =
      .app (.app .zero .zero) (.recR .zero .zero .zero) :=
  rfl

end OrientationClosureSystemTRecursorReach
