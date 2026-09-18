import OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
import OperatorKO7.Meta.DistinctionBoundary.DiscriminatorExtension
import OperatorKO7.Meta.DistinctionBoundary.RepairCompleteness
import OperatorKO7.Meta.DistinctionBoundary.ContextualClassification
import OperatorKO7.Meta.DistinctionBoundary.TranslationTheorems

/-!
# Reach and axiom gate: Sprint A modules S2, S3, S4

Covers every public declaration of `ObserverExpressivity`,
`DiscriminatorExtension`, `RepairCompleteness`, and `ContextualClassification`,
including inductive constructors and structure projections.

`#check` and `#print axioms` commands only. No `sorry`, no `axiom`, no new
declarations.
-/

namespace OperatorKO7.Test.DistinctionBoundarySprintAReach

open OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
open OperatorKO7.Meta.DistinctionBoundary.DiscriminatorExtension
open OperatorKO7.Meta.DistinctionBoundary.RepairCompleteness
open OperatorKO7.Meta.DistinctionBoundary.ContextualClassification
open OperatorKO7.Meta.DistinctionBoundary.TranslationTheorems

/-! ## S3a: ObserverExpressivity (T-E, T-FS) -/

#check @IsDiscriminator
#check @NaturalUnder
#check @not_discriminator_of_natural_under_noninjective
#check @discriminator_forces_injective_on_pair
#check @endomorphismHypotheses_nonvacuous
#check @dpow
#check @dpow_injective
#check @FiniteStateObserver
#check @FiniteStateObserver.mk
#check @FiniteStateObserver.state
#check @FiniteStateObserver.parent
#check @RecognisesDiagonal
#check @no_finiteState_observer_recognises_diagonal
#check @equalityTest_decides_diagonal
#check @finiteState_boundary_is_about_state_finiteness

#print axioms IsDiscriminator
#print axioms NaturalUnder
#print axioms not_discriminator_of_natural_under_noninjective
#print axioms discriminator_forces_injective_on_pair
#print axioms endomorphismHypotheses_nonvacuous
#print axioms dpow
#print axioms dpow_injective
#print axioms FiniteStateObserver
#print axioms FiniteStateObserver.mk
#print axioms FiniteStateObserver.state
#print axioms FiniteStateObserver.parent
#print axioms RecognisesDiagonal
#print axioms no_finiteState_observer_recognises_diagonal
#print axioms equalityTest_decides_diagonal
#print axioms finiteState_boundary_is_about_state_finiteness

/-! ## S3b: DiscriminatorExtension (T-F) -/

#check @structEq
#check @structEq_correct
#check @structEq_sound
#check @structEq_complete
#check @structEq_false_iff_ne
#check @discOp
#check @discOp_isDiscriminator
#check @StepStructGuarded
#check @StepStructGuarded.R_int_delta
#check @StepStructGuarded.R_merge_void_left
#check @StepStructGuarded.R_merge_void_right
#check @StepStructGuarded.R_merge_cancel
#check @StepStructGuarded.R_rec_zero
#check @StepStructGuarded.R_rec_succ
#check @StepStructGuarded.R_eq_refl
#check @StepStructGuarded.R_eq_diff
#check @stepStructGuarded_iff_eqGuardedStep
#check @extension_without_discriminator_preserves_no_go
#check @ExtensionGrammar
#check @ExtensionGrammar.none
#check @ExtensionGrammar.comparator
#check @Supplies
#check @comparator_supplies
#check @comparator_is_minimal_in_grammar
#check @structEq_nonvacuous
#check @stepStructGuarded_nonvacuous
#check @discOp_separates

#print axioms structEq
#print axioms structEq_correct
#print axioms structEq_sound
#print axioms structEq_complete
#print axioms structEq_false_iff_ne
#print axioms discOp
#print axioms discOp_isDiscriminator
#print axioms StepStructGuarded
#print axioms StepStructGuarded.R_eq_refl
#print axioms StepStructGuarded.R_eq_diff
#print axioms stepStructGuarded_iff_eqGuardedStep
#print axioms extension_without_discriminator_preserves_no_go
#print axioms ExtensionGrammar
#print axioms Supplies
#print axioms comparator_supplies
#print axioms comparator_is_minimal_in_grammar
#print axioms structEq_nonvacuous
#print axioms stepStructGuarded_nonvacuous
#print axioms discOp_separates

/-! ## S2: RepairCompleteness -/

#check @retains_both_edges_forces_join
#check @repair_dichotomy
#check @restriction_cannot_join
#check @restriction_must_refuse
#check @RepairMode
#check @RepairGrammar
#check @mode
#check @grammar_classification
#check @grammar_modes_inhabited
#check @grammar_relative_completeness
#check @Verdict
#check @Compatible
#check @IsClique
#check @clique_with_refl_is_reflSingleton
#check @reflSingleton_isClique
#check @unique_maximal_clique_with_refl
#check @completion_adds_step_at_every_diagonal
#check @uniform_completion_collapses_integrate
#check @dichotomy_refusal_side_inhabited
#check @grammar_modes_separate

#print axioms retains_both_edges_forces_join
#print axioms repair_dichotomy
#print axioms restriction_cannot_join
#print axioms restriction_must_refuse
#print axioms RepairMode
#print axioms RepairGrammar
#print axioms mode
#print axioms grammar_classification
#print axioms grammar_modes_inhabited
#print axioms grammar_relative_completeness
#print axioms Verdict
#print axioms Compatible
#print axioms IsClique
#print axioms clique_with_refl_is_reflSingleton
#print axioms reflSingleton_isClique
#print axioms unique_maximal_clique_with_refl
#print axioms completion_adds_step_at_every_diagonal
#print axioms uniform_completion_collapses_integrate
#print axioms dichotomy_refusal_side_inhabited
#print axioms grammar_modes_separate

/-! ## S4: ContextualClassification -/

#check @JoinCtx
#check @joinCtx_void_iff_ctxStar_void
#check @ctxStar_integrate
#check @ctxStar_mergeL
#check @ctxStar_mergeR
#check @diagonal_ctx_joins_of_reaches_delta
#check @diagonal_ctx_joins_at_delta
#check @diagonal_ctx_fails_at_void
#check @contextual_scope_proven
#check @contextual_scope_nonvacuous
#check @strengthening_is_proper

#print axioms JoinCtx
#print axioms joinCtx_void_iff_ctxStar_void
#print axioms ctxStar_integrate
#print axioms ctxStar_mergeL
#print axioms ctxStar_mergeR
#print axioms diagonal_ctx_joins_of_reaches_delta
#print axioms diagonal_ctx_joins_at_delta
#print axioms diagonal_ctx_fails_at_void
#print axioms contextual_scope_proven
#print axioms contextual_scope_nonvacuous
#print axioms strengthening_is_proper

/-! ## S4: the contextual classifier (both directions) -/

#check @IntegrateCone
#check @integrateCone_step
#check @integrateCone_ctxStar
#check @ctxStar_integrate_void_imp
#check @MergeCone
#check @mergeCone_step
#check @mergeCone_ctxStar
#check @ctxStar_merge_self_delta_imp
#check @diagonal_ctx_joins_iff_reaches_delta
#check @classifier_partitions

#print axioms IntegrateCone
#print axioms integrateCone_step
#print axioms integrateCone_ctxStar
#print axioms ctxStar_integrate_void_imp
#print axioms MergeCone
#print axioms mergeCone_step
#print axioms mergeCone_ctxStar
#print axioms ctxStar_merge_self_delta_imp
#print axioms diagonal_ctx_joins_iff_reaches_delta
#print axioms classifier_partitions

/-! ## Translation theorems -/

#check @sem
#check @sem_merge_void_left
#check @sem_merge_void_right
#check @sem_merge_cancel
#check @sem_merge_comm
#check @sem_merge_assoc
#check @merge_presents_bounded_semilattice
#check @sem_sound_on_merge_rules
#check @merge_not_commutative_in_kernel
#check @iterApp
#check @ctxStar_appR
#check @recD_reduces_to_iterApp
#check @no_root_rule_for_app
#check @app_free
#check @sem_nonvacuous
#check @iterApp_nonvacuous

#print axioms sem
#print axioms sem_merge_void_left
#print axioms sem_merge_void_right
#print axioms sem_merge_cancel
#print axioms sem_merge_comm
#print axioms sem_merge_assoc
#print axioms merge_presents_bounded_semilattice
#print axioms sem_sound_on_merge_rules
#print axioms merge_not_commutative_in_kernel
#print axioms iterApp
#print axioms ctxStar_appR
#print axioms recD_reduces_to_iterApp
#print axioms no_root_rule_for_app
#print axioms app_free
#print axioms sem_nonvacuous
#print axioms iterApp_nonvacuous

end OperatorKO7.Test.DistinctionBoundarySprintAReach
