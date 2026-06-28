import OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization
import OperatorKO7.Meta.DistinctionBoundary.Pillar
import OperatorKO7.Meta.DistinctionBoundary.SharedRoot
import OperatorKO7.Meta.DistinctionBoundary.CostDual
import OperatorKO7.Meta.DistinctionBoundary.SemanticsPreservingMaximality
import OperatorKO7.Meta.DistinctionBoundary.RepairRoutes
import OperatorKO7.Meta.SafeStep.GuardNecessity
import OperatorKO7.Meta.SafeStep.DistinctionControls
import OperatorKO7.Meta.SafeStep.BranchTransaction
import OperatorKO7.Meta.SafeStep.BranchEntropy
import OperatorKO7.Meta.SafeStep.NonlinearityDichotomy
import OperatorKO7.Meta.SafeStep.DistinctionAscentProfile
import OperatorKO7.Meta.SafeStep.FaithfulnessNoGo
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import OperatorKO7.Meta.SafeStep.DistinctionInexpressible
import OperatorKO7.Meta.ComparatorNecessity
import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord
import OperatorKO7.Meta.InformationalIncompleteness.ConfluenceForcedTrilemma
import OperatorKO7.Meta.Rewriting.CriticalPairComplete
import OperatorKO7.Meta.Rewriting.ParallelReductionConfluence
import OperatorKO7.Meta.ReverseMath.NewmanComplexity
import OperatorKO7.Meta.ReverseMath.ConfluenceOrderType

/-!
# Distinction Boundary public claim-liveness gate

One consolidated reach gate over the manuscript's public theorem package: every
headline anchor of the confluence-axis development is `#check`-ed here, and
`#print axioms` confirms each depends only on the baseline whitelist
`{propext, Classical.choice, Quot.sound}` or no axioms. A reviewer builds this
single module against the public release to confirm that the cited anchors exist
with the claimed types and trusted base. Every module referenced here is in the
public Lean release (the engine-coupled meta-halt bridge is excluded by design).

No `sorry`, no `axiom`; this file only `#check`s and `#print axioms` existing
declarations.
-/

namespace OperatorKO7.Test.DistinctionBoundaryClaimLiveness

-- The local breaker, completeness, and global confluence (the closed axis).
#check @OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.eqW_void_void_admits_two_normal_forms
#check @OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction
#check @OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_globally_confluent

-- Portability and the schema-level boundary.
#check @OperatorKO7.Meta.SafeStep.GenericDiagonalFork.localConfluence_fails_at_diagonal
#check @OperatorKO7.Meta.SafeStep.DistinctionWitnessBoundary.diagonal_localConfluence_iff_verdictsJoin
#check @OperatorKO7.Meta.SafeStep.DistinctionControls.nonLeftLinearity_necessary_not_sufficient

-- Inexpressibility, the shared root, the witness order, the comparator.
#check @OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional
#check @OperatorKO7.Meta.DistinctionBoundary.SharedRoot.two_nonderivabilities_share_one_root
#check @OperatorKO7.Meta.SafeStep.DistinctionInexpressible.ko7_confluence_witnessOrder_nonzero
#check @OperatorKO7.Meta.ComparatorNecessity.exactComparator_decidableEq

-- Repair, guard, branch transaction, record legality, branch entropy.
#check @OperatorKO7.Meta.SafeStep.GuardNecessity.guard_is_the_satisfier
#check @OperatorKO7.Meta.DistinctionBoundary.RepairRoutes.confluent_inert
#check @OperatorKO7.Meta.SafeStep.BranchTransaction.ko7_branchTransaction
#check @OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord.equality_record_inert
#check @OperatorKO7.Meta.SafeStep.BranchEntropy.eqW_void_void_branchEntropy_collapse

-- Duality and the no-go; the confluence-axis safety statement.
#check @OperatorKO7.Meta.SafeStep.DistinctionAscentProfile.distinctionBoundary_has_dp_structural_identity
#check @OperatorKO7.Meta.SafeStep.FaithfulnessNoGo.not_payloadFaithful_of_covers
#check @OperatorKO7.Meta.SafeStep.NonlinearityDichotomy.ko7_raw_mechanism_correspondence
#check @OperatorKO7.Meta.InformationalIncompleteness.ConfluenceForcedTrilemma.diagonal_emission_is_false_formal_legitimacy

-- Cost-side duality of verdict-retaining licensed routes.
#check @OperatorKO7.Meta.DistinctionBoundary.CostDual.totalCharge_append
#check @OperatorKO7.Meta.DistinctionBoundary.CostDual.orientation_totalCharge_eq_cumulativeCarrier
#check @OperatorKO7.Meta.DistinctionBoundary.CostDual.orientation_totalCharge_doubled_eq_confessedBurdenDoubled
#check @OperatorKO7.Meta.DistinctionBoundary.CostDual.cumulativeCarrier_doubled_eq_confessedBurdenDoubled
#check @OperatorKO7.Meta.DistinctionBoundary.CostDual.distinction_matches_refLoad_batch
#check @OperatorKO7.Meta.DistinctionBoundary.CostDual.retained_route_magnitudes_separate
#check @OperatorKO7.Meta.DistinctionBoundary.CostDual.inert_route_zero_retained_charge
#check @OperatorKO7.Meta.DistinctionBoundary.CostDual.verdict_retaining_cost_dual_nonvacuous

-- Comparison-interface classification and SafeStep maximality.
#check @OperatorKO7.Meta.DistinctionBoundary.equalityMode_canDiagonalFork_iff
#check @OperatorKO7.Meta.DistinctionBoundary.confluence_forces_no_diagonal_diff
#check @OperatorKO7.Meta.DistinctionBoundary.semantics_preserving_subrel_subset_safestep
#check @OperatorKO7.Meta.DistinctionBoundary.semantics_preserving_subrel_eq_safestep
#check @OperatorKO7.Meta.DistinctionBoundary.safeStep_is_maximal_semantics_preserving_repair

-- The generic first-order Critical Pair Lemma library and the metatheoretic calibration.
#check @OperatorKO7.Meta.Rewriting.critical_pair_lemma
#check @OperatorKO7.Meta.Rewriting.weaklyOrthogonal_shallow_stepStar_confluent

-- The equality-witness generalization (the scoped universality).
#check @OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.fork_iff_verdicts_not_join
#check @OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.comparison_diagonal_no_difference
#check @OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.ComparisonInterface.toDecidableEq
#check @OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.guarded_interfaces_refute_universal_failure
-- The necessity bridge: every distinction generator is a comparison interface.
#check @OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.DistinctionGenerator.toComparisonInterface
#check @OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.DistinctionGenerator.toDecidableEq
#check @OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.distinctionGenerator_diagonal_inert
-- Evaluation gap closures: KO7 diagonal determinacy, exact witness order, repair exhaustiveness.
#check @OperatorKO7.Meta.SafeStep.DistinctionWitnessBoundary.ko7_diagonal_determined
#check @OperatorKO7.Meta.SafeStep.DistinctionWitnessBoundary.ko7_diagonal_localConfluence_iff_verdictsJoin
#check @OperatorKO7.Meta.SafeStep.DistinctionInexpressible.kappaDist_eq_one
#check @OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.diagonal_repair_exhaustive

-- Baseline-axiom inventory on the headline theorems (each ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction
#print axioms OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_globally_confluent
#print axioms OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional
#print axioms OperatorKO7.Meta.SafeStep.GuardNecessity.guard_is_the_satisfier
#print axioms OperatorKO7.Meta.InformationalIncompleteness.ConfluenceForcedTrilemma.diagonal_emission_is_false_formal_legitimacy
#print axioms OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.fork_iff_verdicts_not_join
#print axioms OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization.comparison_diagonal_no_difference
#print axioms OperatorKO7.Meta.DistinctionBoundary.CostDual.orientation_totalCharge_doubled_eq_confessedBurdenDoubled
#print axioms OperatorKO7.Meta.DistinctionBoundary.CostDual.distinction_matches_refLoad_batch
#print axioms OperatorKO7.Meta.DistinctionBoundary.CostDual.retained_route_magnitudes_separate
#print axioms OperatorKO7.Meta.DistinctionBoundary.CostDual.inert_route_zero_retained_charge
#print axioms OperatorKO7.Meta.DistinctionBoundary.CostDual.verdict_retaining_cost_dual_nonvacuous
#print axioms OperatorKO7.Meta.DistinctionBoundary.confluence_forces_no_diagonal_diff
#print axioms OperatorKO7.Meta.DistinctionBoundary.semantics_preserving_subrel_subset_safestep
#print axioms OperatorKO7.Meta.DistinctionBoundary.semantics_preserving_subrel_eq_safestep
#print axioms OperatorKO7.Meta.DistinctionBoundary.safeStep_is_maximal_semantics_preserving_repair

end OperatorKO7.Test.DistinctionBoundaryClaimLiveness
