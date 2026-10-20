import OperatorKO7.Meta.UUET.Probability.FiniteDistribution

set_option autoImplicit false

/-!
# Finite local parametric families

Relation: a normalized finite law and its tangent at one real parameter value.
Closure: tangent mass sums to zero and support is strictly positive.
Trust: kernel-only finite algebra.
Scope: local finite statistical models; no syntax bridge is implicit.
-/

namespace OperatorKO7.Meta.UUET.Statistics

open scoped BigOperators

/-- A regular finite statistical family at one parameter value. -/
structure ParametricFamily (Ω : Type) [Fintype Ω] where
  parameter : ℝ
  probability : Ω -> ℝ
  tangent : Ω -> ℝ
  probability_nonnegative : forall ω, 0 <= probability ω
  probability_total : (∑ ω, probability ω) = 1
  tangent_total_zero : (∑ ω, tangent ω) = 0
  positive_support : forall ω, 0 < probability ω

/-- A parameter-insensitive fair binary family. -/
noncomputable def constantBinaryFamily : ParametricFamily (Fin 2) where
  parameter := 0
  probability := fun _ => 1 / 2
  tangent := fun _ => 0
  probability_nonnegative := by intro ω; norm_num
  probability_total := by norm_num [Fin.sum_univ_two]
  tangent_total_zero := by simp
  positive_support := by intro ω; norm_num

theorem constantBinaryFamily_tangent_zero (ω : Fin 2) :
    constantBinaryFamily.tangent ω = 0 := rfl

/-- Negative fixture: a nonzero constant tangent cannot satisfy normalization. -/
theorem no_constant_one_tangent_family :
    Not (exists F : ParametricFamily (Fin 2), forall ω, F.tangent ω = 1) := by
  rintro ⟨F, h⟩
  have hz := F.tangent_total_zero
  rw [Fin.sum_univ_two, h 0, h 1] at hz
  norm_num at hz

/-! Imported NameGate and TypeGate. -/
#check @Finset.sum
#check @Fintype
#check @ParametricFamily.probability
#check @ParametricFamily.tangent

#check @constantBinaryFamily_tangent_zero
#check @no_constant_one_tangent_family
#print axioms constantBinaryFamily_tangent_zero
#print axioms no_constant_one_tangent_family

end OperatorKO7.Meta.UUET.Statistics
