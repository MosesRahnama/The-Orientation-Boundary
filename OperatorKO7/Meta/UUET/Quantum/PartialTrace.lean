import OperatorKO7.Meta.UUET.Quantum.DensityMatrix

set_option autoImplicit false

/-!
# Finite partial trace

Relation: equality under finite subsystem contraction.
Closure: tracing a product-index operator over either finite factor.
Trust: kernel-checked finite sums.
Scope: explicit product-index matrices; no implicit tensor equivalence is assumed.
-/

namespace OperatorKO7.Meta.UUET.Quantum

open Matrix

/-- Partial trace over the right subsystem. -/
noncomputable def partialTraceRight {ι κ : Type} [Fintype κ]
    (M : BipartiteOperator ι κ) : Operator ι :=
  Matrix.of fun i j => ∑ a : κ, M (i, a) (j, a)

/-- Partial trace over the left subsystem. -/
noncomputable def partialTraceLeft {ι κ : Type} [Fintype ι]
    (M : BipartiteOperator ι κ) : Operator κ :=
  Matrix.of fun a b => ∑ i : ι, M (i, a) (i, b)

/-- Partial trace preserves the total trace. -/
theorem partialTraceRight_trace {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : BipartiteOperator ι κ) :
    (partialTraceRight M).trace = M.trace := by
  simp [partialTraceRight, Matrix.trace, Fintype.sum_prod_type]

/-- Positive fixture: tracing the zero operator gives zero. -/
theorem partialTraceRight_zero {ι κ : Type} [Fintype κ] :
    partialTraceRight (0 : BipartiteOperator ι κ) = 0 := by
  ext i j
  simp [partialTraceRight]

/-! Imported NameGate and TypeGate. -/
#check @Fintype.sum_prod_type
#check @Matrix.trace
#check @partialTraceRight
#check @partialTraceLeft

#check @partialTraceRight_trace
#print axioms partialTraceRight_trace
#check @partialTraceRight_zero
#print axioms partialTraceRight_zero

end OperatorKO7.Meta.UUET.Quantum
