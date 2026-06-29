import OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness
import OperatorKO7.Meta.DistinctionBoundary.CriticalPairLemmaKO7

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.SingleBadCriticalPair

open OperatorKO7 Trace

/-
Finite certificate that one named nonjoinable critical source refutes local
confluence for the root relation.
-/
structure SingleBadRootSource where
  src : Trace
  bad : ¬ MetaSN_KO7.LocalJoinStep src
  complete : ∀ a, ¬ MetaSN_KO7.LocalJoinStep a ->
    CriticalPairCompleteness.IsEqWDiagonal a

def ko7_singleBadRootSource : SingleBadRootSource where
  src := eqW void void
  bad := CriticalPairCompleteness.eqW_void_void_is_canonical_root_obstruction.1
  complete := CriticalPairCompleteness.eqW_void_void_is_canonical_root_obstruction.2

theorem single_bad_root_source_refutes_local_confluence :
    ¬ MetaSN_KO7.LocalJoinStep ko7_singleBadRootSource.src :=
  ko7_singleBadRootSource.bad

theorem every_root_nonjoinability_is_eqW_diagonal
    {a : Trace} (h : ¬ MetaSN_KO7.LocalJoinStep a) :
    CriticalPairCompleteness.IsEqWDiagonal a :=
  ko7_singleBadRootSource.complete a h

theorem ko7_single_bad_pair_package :
    ¬ MetaSN_KO7.LocalJoinStep (eqW void void) ∧
      ∀ a, ¬ MetaSN_KO7.LocalJoinStep a ->
        CriticalPairCompleteness.IsEqWDiagonal a :=
  CriticalPairCompleteness.eqW_void_void_is_canonical_root_obstruction

#print axioms single_bad_root_source_refutes_local_confluence
#print axioms every_root_nonjoinability_is_eqW_diagonal
#print axioms ko7_single_bad_pair_package

end OperatorKO7.Meta.DistinctionBoundary.SingleBadCriticalPair
