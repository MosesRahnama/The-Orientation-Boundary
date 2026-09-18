import OperatorKO7.Meta.TupleInterpretationDecomposition

/-!
# Reach test for `OperatorKO7.Meta.TupleInterpretationDecomposition`

Forces elaboration of every public declaration in the tuple-interpretation
decomposition module.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.TupleInterpretationDecompositionReach

open OperatorKO7.Meta.TupleInterpretationDecomposition

-- carriers and classifiers
#check TupleInterpretationRow
#check tupleInterpretationRows
#check tupleInterpretationRows_length
#check tupleInterpretationRows_nodup
#check TupleBoundaryClass
#check familyOf
#check boundaryClassOf
#check RowHypothesis

-- hypothesis projections and scalar-component surface
#check arityOf
#check strictIndexOf
#check strictIndex_lt_arity_of
#check higherOrderFlagOf?
#check scalarComponentKind

-- decomposition package
#check TupleInterpretationDecomposition
#check TupleInterpretationDecomposition.arity
#check TupleInterpretationDecomposition.strictIndex
#check TupleInterpretationDecomposition.strictIndex_lt_arity
#check TupleInterpretationDecomposition.componentKind
#check TupleInterpretationDecomposition.components_are_scalar
#check TupleInterpretationDecomposition.higherOrderFlag?
#check TupleInterpretationDecomposition.boundaryClass
#check TupleInterpretationDecomposition.boundaryClass_eq
#check TupleInterpretationDecomposition.universeStatus_eq

-- constructors and theorems
#check tupleStrictSDecomposition
#check higherOrderTupleDecomposition
#check decompositionOf
#check tuple_rows_have_conditional_barrier_status
#check tuple_interpretation_decomposition_unconditional
#check audit_theory_expansion_tuple_interpretation_decomposition_module_anchor

#print axioms tuple_interpretation_decomposition_unconditional

end OperatorKO7.Test.TupleInterpretationDecompositionReach
