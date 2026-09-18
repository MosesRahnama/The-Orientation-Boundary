import OperatorKO7.Meta.UniqueNormalization.ConditionalDecreasingAdapter

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @CStepMinimal
#check @CStep.exists_minimal
#check @CStepMinimal.unique
#check @CStepMinimal.ne_zero
#check @minimalLevelStep
#check @unlabelled_minimalLevelStep_iff
#check @minimalLevelStep_label_unique
#check @ConditionalLabelRefinement
#check @ConditionalLabelRefinement.mk
#check @ConditionalLabelRefinement.sound
#check @ConditionalLabelRefinement.complete
#check @minimalLevelStep_refinement
#check @ConditionalLabelRefinement.unlabelled_iff
#check @reflTransGen_mono
#check @ConditionalLabelRefinement.confluent_iff
#check @cconfluent_of_localDecreasing
#check @cconfluent_of_minimalLevel_localDecreasing
#check @UNconv_of_linearization_localDecreasing
#check @UNred_of_linearization_localDecreasing

#print axioms OperatorKO7.Meta.UniqueNormalization.CStepMinimal
#print axioms OperatorKO7.Meta.UniqueNormalization.CStep.exists_minimal
#print axioms OperatorKO7.Meta.UniqueNormalization.CStepMinimal.unique
#print axioms OperatorKO7.Meta.UniqueNormalization.CStepMinimal.ne_zero
#print axioms OperatorKO7.Meta.UniqueNormalization.minimalLevelStep
#print axioms OperatorKO7.Meta.UniqueNormalization.unlabelled_minimalLevelStep_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.minimalLevelStep_label_unique
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement.sound
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement.complete
#print axioms OperatorKO7.Meta.UniqueNormalization.minimalLevelStep_refinement
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement.unlabelled_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.reflTransGen_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.ConditionalLabelRefinement.confluent_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.cconfluent_of_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.cconfluent_of_minimalLevel_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linearization_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_linearization_localDecreasing
