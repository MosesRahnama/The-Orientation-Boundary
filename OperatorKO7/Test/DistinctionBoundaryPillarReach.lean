import OperatorKO7.Meta.DistinctionBoundary.Pillar

set_option autoImplicit false

/-!
# Distinction Boundary Pillar reach gate

Reach/audit module for the distinction (confluence) pillar front door
`OperatorKO7.Meta.DistinctionBoundary.Pillar`. Any rename, namespace drift, or
trust-surface regression on the pillar's load-bearing anchors breaks this file.

It pins:
* the completeness headline (the `eqW` diagonal is the unique root obstruction),
* the canonical-witness corollary,
* global confluence of `SafeStep` and `SafeStepCtx`,
* the axis-end-to-end bridge,
* guard necessity and the object-level critical pair,
* and the depth modules' own headline names (via fully-qualified `#check`).

`#print axioms` on each headline must report a subset of
`{propext, Classical.choice, Quot.sound}`.
-/

open OperatorKO7 Trace

/-! ## Pillar front-door surface -/

#check @OperatorKO7.Meta.DistinctionBoundary.Pillar.eqW_diagonal_is_the_unique_root_obstruction
#check @OperatorKO7.Meta.DistinctionBoundary.Pillar.eqW_void_void_is_canonical_root_obstruction
#check @OperatorKO7.Meta.DistinctionBoundary.Pillar.safeStep_globally_confluent
#check @OperatorKO7.Meta.DistinctionBoundary.Pillar.safeStepCtx_globally_confluent
#check @OperatorKO7.Meta.DistinctionBoundary.Pillar.safeStep_confluent_and_obstruction_complete
#check @OperatorKO7.Meta.DistinctionBoundary.Pillar.eqW_guards_are_confluence_necessary
#check @OperatorKO7.Meta.DistinctionBoundary.Pillar.local_confluence_fails_at_eqW_void_void
#check @OperatorKO7.Meta.DistinctionBoundary.Pillar.nonLeftLinearity_necessary_not_sufficient

/-! ## Depth-module headlines (direct) -/

#check @OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.eqW_diagonal_is_the_unique_root_obstruction
#check @OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.localJoinStep_of_not_diagonal
#check @OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.not_localJoinStep_of_diagonal
#check @OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.merge_void_void_joins
#check @OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.rec_rules_no_root_overlap
#check @OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_strongly_normalizing
#check @OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_locally_confluent
#check @OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_confluent_via_newman
#check @OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_unique_normal_forms

/-! ## Axiom audit (must be subset of {propext, Classical.choice, Quot.sound}) -/

#print axioms OperatorKO7.Meta.DistinctionBoundary.Pillar.eqW_diagonal_is_the_unique_root_obstruction
#print axioms OperatorKO7.Meta.DistinctionBoundary.Pillar.eqW_void_void_is_canonical_root_obstruction
#print axioms OperatorKO7.Meta.DistinctionBoundary.Pillar.safeStep_globally_confluent
#print axioms OperatorKO7.Meta.DistinctionBoundary.Pillar.safeStepCtx_globally_confluent
#print axioms OperatorKO7.Meta.DistinctionBoundary.Pillar.safeStep_confluent_and_obstruction_complete
#print axioms OperatorKO7.Meta.DistinctionBoundary.Pillar.eqW_guards_are_confluence_necessary
#print axioms OperatorKO7.Meta.DistinctionBoundary.Pillar.local_confluence_fails_at_eqW_void_void
#print axioms OperatorKO7.Meta.DistinctionBoundary.Pillar.nonLeftLinearity_necessary_not_sufficient
#print axioms OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.localJoinStep_of_not_diagonal
#print axioms OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness.not_localJoinStep_of_diagonal
#print axioms OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_strongly_normalizing
