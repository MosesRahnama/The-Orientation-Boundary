import OperatorKO7.Meta.UniqueNormalization.ConditionalDerivationData

/-!
# Reach and axiom check for `Meta/UniqueNormalization/ConditionalDerivationData.lean`

Pins every public declaration, structure constructor, field and parent projection, and
inductive constructor of the paired module, each with a paired axiom query, followed by the
package controls. Baseline axioms only. -/

#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.forward
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.forward
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.backward
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.backward
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.nil
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.nil
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.snoc
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.snoc
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.FaithfulData
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.FaithfulData
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.flip
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.flip
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.map
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.map
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.weight
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.SignedData.weight
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.append
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.append
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.cons
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.cons
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.map
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.map
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.mapIdx
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.mapIdx
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.sumWeights
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.sumWeights
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.steps
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.steps
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_append
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_append
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_cons
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_cons
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_map
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_map
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_mapIdx
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_mapIdx
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.steps_length
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.steps_length
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.sound
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.sound
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.reverse
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.reverse
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_reverse
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.TraceData.length_reverse
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.traceData_faithful
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.traceData_faithful
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.signedData_faithful
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.signedData_faithful
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.convData_faithful
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.convData_faithful
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_occurrence_reuse
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_occurrence_reuse
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.mk
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.rule
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.rule
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.mem
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.mem
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.subst
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.subst
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.src
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.src
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.tgt
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.tgt
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.history
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.GuardedRootData.history
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData.root
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData.root
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData.arg
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData.arg
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.LevelStepData
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.LevelStepData
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.contextStepData_faithful
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.contextStepData_faithful
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.levelStepData_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.levelStepData_iff
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.levelConvData_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.levelConvData_iff
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.cconv_exists_level
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.cconv_exists_level
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.conditionalHistory_iff_cconv
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.conditionalHistory_iff_cconv
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData.mapHistory
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData.mapHistory
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData.weight
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ContextStepData.weight
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.LevelStepData.liftSucc
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.LevelStepData.liftSucc
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.LevelStepData.liftLE
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.LevelStepData.liftLE
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.LevelStepData.occurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.LevelStepData.occurrences
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory.length
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory.length
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory.totalOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory.totalOccurrences
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory.reverse
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory.reverse
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory.append
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.ConditionalHistory.append
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_reverse
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_reverse
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_append
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_append
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_length_append
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_length_append
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.occurrences_pos
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.occurrences_pos
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.length_le_totalOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.length_le_totalOccurrences
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.stepBC
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.stepBC
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.stepFBCA
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.stepFBCA
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.historyFBCA
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.historyFBCA
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_totalOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_totalOccurrences
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.emptyAtB
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.emptyAtB
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.loopAtB
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.loopAtB
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_erasure_not_injective
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.history_erasure_not_injective
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.liftArgTrace
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.liftArgTrace
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.context_history_projection
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.context_history_projection
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.rootOnly
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.rootOnly
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.rootOnly_c_isolated
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.rootOnly_c_isolated
#check @OperatorKO7.Meta.UniqueNormalization.ConditionHistory.root_history_projection_fails
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionHistory.root_history_projection_fails

open OperatorKO7.Meta.Rewriting OperatorKO7.Meta.UniqueNormalization OperatorKO7.Meta.UniqueNormalization.ConditionHistory

/-! Controls: an inhabited level-two history, its occurrence count, and the root-step
projection control. -/

example : Nonempty (ConditionalHistory CondExample.demoCTRS
    (.app 2 [.app 0 [], .app 1 []]) (.app 3 [])) := ⟨historyFBCA⟩

example : historyFBCA.totalOccurrences = 2 := history_totalOccurrences.2.1

example : cconv CondExample.demoCTRS (.app 2 [.app 0 [], .app 1 []]) (.app 3 []) :=
  (conditionalHistory_iff_cconv _ _ _).1 ⟨historyFBCA⟩

example : ¬ cconv rootOnly (.app 1 []) (.app 2 []) := root_history_projection_fails.2
