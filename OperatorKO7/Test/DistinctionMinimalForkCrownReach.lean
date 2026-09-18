import OperatorKO7.Meta.DistinctionBoundary.DistinctionBoundaryCrown
import OperatorKO7.Meta.DistinctionBoundary.PublicCapstone
import OperatorKO7.Meta.DistinctionBoundary.Pillar

/-!
# Reach gate: complete schema-first Distinction Boundary crown

This final reach gate imports the stable API and all public integration surfaces.
Its proof-bearing bundle is the conjunction of the complete legacy crown and the
new `MinimalForkCrown`; neither component is replaced or weakened.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.DistinctionMinimalForkCrownReach

open OperatorKO7.Meta.DistinctionBoundary.MinimalFork
open OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API
open OperatorKO7.Meta.DistinctionBoundary.Quantitative

#check @minimal_distinction_boundary_crown
#check @distinction_minimal_cardinality
#check @distinction_fork3_initial
#check @distinction_exact_schema_contains_fork3
#check @distinction_minimal_eqW_terminates_not_confluent
#check @distinction_ko7_localCone_is_fork3
#check @distinction_guarded_root_vs_context_scope
#check @distinction_one_bit_terminal_collapse
#check @distinction_semanticFork_iff_unguardedTotalizedRewrite
#check @OperatorKO7.Meta.DistinctionBoundary.DistinctionBoundaryCrown.distinction_boundary_crown
#check @OperatorKO7.Meta.DistinctionBoundary.DistinctionBoundaryCrown.distinctionBoundaryCrown_extended
#check @OperatorKO7.Meta.DistinctionBoundary.PublicCapstone.schema_first_minimal_distinction_crown
#check @OperatorKO7.Meta.DistinctionBoundary.Pillar.minimal_fork_crown

#print axioms minimal_distinction_boundary_crown
#print axioms distinction_minimal_cardinality
#print axioms distinction_fork3_initial
#print axioms distinction_exact_schema_contains_fork3
#print axioms distinction_minimal_eqW_terminates_not_confluent
#print axioms distinction_ko7_localCone_is_fork3
#print axioms distinction_guarded_root_vs_context_scope
#print axioms distinction_one_bit_terminal_collapse
#print axioms distinction_semanticFork_iff_unguardedTotalizedRewrite
#print axioms OperatorKO7.Meta.DistinctionBoundary.DistinctionBoundaryCrown.distinctionBoundaryCrown_extended

/-- All seven dedicated reach gates converge on this real proof-bearing crown. -/
theorem all_minimalFork_reach_gates : MinimalForkCrown :=
  minimal_distinction_boundary_crown

example : MinimalForkCrown := all_minimalFork_reach_gates

end OperatorKO7.Test.DistinctionMinimalForkCrownReach
