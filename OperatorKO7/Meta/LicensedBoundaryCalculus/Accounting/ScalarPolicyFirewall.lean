import OperatorKO7.Meta.LicensedBoundaryCalculus.Accounting.AdditiveValuation

/-!
# Scalar-policy firewall

## Formal Scope

The firewall result concerns two named policies that disagree on one mixed fixture. It does not establish a no-go theorem for every policy-independent scalarization.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

/-- Pointwise order retains resource dimensions. -/
def ResourceVectorLE (left right : ResourceVector) : Prop :=
  forall kind, left kind ≤ right kind

/-- Scalarization is explicitly optional and policy supplied. -/
abbrev ScalarPolicy := ResourceVector -> Option Rat

def ScalarPolicyMonotone (policy : ScalarPolicy) : Prop :=
  forall left right, ResourceVectorLE left right ->
    forall leftValue rightValue,
      policy left = some leftValue -> policy right = some rightValue ->
        leftValue ≤ rightValue

def ScalarPolicyNonzero (policy : ScalarPolicy) : Prop :=
  exists resources value, policy resources = some value ∧ value ≠ 0

/-- Count only the bit coordinate. -/
def bitScalarPolicy : ScalarPolicy := fun resources =>
  some (resources .bit : Rat)

/-- Count only the joule coordinate. -/
def jouleScalarPolicy : ScalarPolicy := fun resources =>
  some (resources .joule : Rat)

theorem bitScalarPolicy_monotone : ScalarPolicyMonotone bitScalarPolicy := by
  intro left right hle leftValue rightValue hleft hright
  simp [bitScalarPolicy] at hleft hright
  subst leftValue
  subst rightValue
  exact_mod_cast hle .bit

theorem jouleScalarPolicy_monotone :
    ScalarPolicyMonotone jouleScalarPolicy := by
  intro left right hle leftValue rightValue hleft hright
  simp [jouleScalarPolicy] at hleft hright
  subst leftValue
  subst rightValue
  exact_mod_cast hle .joule

theorem bitScalarPolicy_nonzero : ScalarPolicyNonzero bitScalarPolicy := by
  refine ⟨bitJoule_resource_fixture, 1, ?_, by norm_num⟩
  simp [bitScalarPolicy, bitJoule_resource_fixture]

theorem jouleScalarPolicy_nonzero : ScalarPolicyNonzero jouleScalarPolicy := by
  refine ⟨bitJoule_resource_fixture, 2, ?_, by norm_num⟩
  simp [jouleScalarPolicy, bitJoule_resource_fixture]

/-- Two admissible policies disagree on one fixed typed vector. -/
theorem monotone_nonzero_scalar_policies_disagree :
    ScalarPolicyMonotone bitScalarPolicy ∧
      ScalarPolicyMonotone jouleScalarPolicy ∧
      ScalarPolicyNonzero bitScalarPolicy ∧
      ScalarPolicyNonzero jouleScalarPolicy ∧
      bitScalarPolicy bitJoule_resource_fixture = some 1 ∧
      jouleScalarPolicy bitJoule_resource_fixture = some 2 ∧
      bitScalarPolicy bitJoule_resource_fixture ≠
        jouleScalarPolicy bitJoule_resource_fixture := by
  refine
    ⟨bitScalarPolicy_monotone, jouleScalarPolicy_monotone,
      bitScalarPolicy_nonzero, jouleScalarPolicy_nonzero, ?_, ?_, ?_⟩
  · simp [bitScalarPolicy, bitJoule_resource_fixture]
  · simp [jouleScalarPolicy, bitJoule_resource_fixture]
  · simp [bitScalarPolicy, jouleScalarPolicy, bitJoule_resource_fixture]

/-- There is no scalar value on the mixed fixture invariant under both of the
explicit admissible policies. -/
theorem no_policy_independent_scalar_on_mixed_fixture :
    ¬ exists value : Rat,
      bitScalarPolicy bitJoule_resource_fixture = some value ∧
        jouleScalarPolicy bitJoule_resource_fixture = some value := by
  rintro ⟨value, hbit, hjoule⟩
  have hbitValue : value = 1 := by
    simpa [bitScalarPolicy, bitJoule_resource_fixture] using hbit.symm
  have hjouleValue : value = 2 := by
    simpa [jouleScalarPolicy, bitJoule_resource_fixture] using hjoule.symm
  rw [hbitValue] at hjouleValue
  norm_num at hjouleValue

#check monotone_nonzero_scalar_policies_disagree
#check no_policy_independent_scalar_on_mixed_fixture
#print axioms bitScalarPolicy_monotone
#print axioms jouleScalarPolicy_monotone
#print axioms monotone_nonzero_scalar_policies_disagree
#print axioms no_policy_independent_scalar_on_mixed_fixture

end OperatorKO7.Meta.LicensedBoundaryCalculus
