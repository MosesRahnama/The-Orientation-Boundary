import OperatorKO7.Meta.BoundaryObserver.EchoEvidence

/-!
# Full-support nuisance-bit counterexample

A fair target and an independent fair nuisance bit form the object. The answer
and the deterministic output return the nuisance coordinate. The object answer
is nonconstant on the full support, while actual target-output information is
zero.

Relation: finite source laws and the answer-indexed output channel.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.EchoEvidence.NuisanceFixture

open scoped BigOperators
open ProtocolResolution

/-- Uniform probability law on the two Boolean values. -/
noncomputable def fairLaw : FiniteLaw Bool where
  mass _ := 1 / 2
  nonnegative _ := by norm_num
  total := by norm_num [Fintype.sum_bool]

/-- The first coordinate records the target; the second is a fair nuisance bit. -/
noncomputable def conditionalObjectLaw (z : Bool) : FiniteLaw (Bool × Bool) where
  mass o := if o.1 = z then 1 / 2 else 0
  nonnegative o := by
    split_ifs <;> norm_num
  total := by
    cases z <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The output returns its answer index deterministically. -/
noncomputable def deterministicOutputLaw (a : Bool) : FiniteLaw Bool where
  mass y := if y = a then 1 else 0
  nonnegative y := by
    split_ifs <;> norm_num
  total := by
    cases a <;> norm_num [Fintype.sum_bool]

/-- One source and channel for both the structural and probabilistic claims. -/
noncomputable def experiment : Experiment Unit Bool (Bool × Bool) Bool Bool where
  initial := unitLaw
  target _ := fairLaw
  object _ := conditionalObjectLaw
  answer _ o := o.2
  output _ := deterministicOutputLaw

/-- The source marginal of the object, calculated through the actual target law. -/
noncomputable def objectMarginal (o : Bool × Bool) : ℝ :=
  ∑ z, (experiment.target ()).mass z * (experiment.object () z).mass o

theorem objectMarginal_eq_quarter (o : Bool × Bool) :
    objectMarginal o = 1 / 4 := by
  rcases o with ⟨b, n⟩
  cases b <;>
    norm_num [objectMarginal, experiment, fairLaw, conditionalObjectLaw, Fintype.sum_bool]

theorem objectMarginal_positive (o : Bool × Bool) :
    0 < objectMarginal o := by
  rw [objectMarginal_eq_quarter]
  norm_num

/-- Marginalizing the object leaves a fair output at either target value. -/
theorem outputMass_eq_half (z y : Bool) :
    outputMass experiment () z y = 1 / 2 := by
  cases z <;> cases y <;>
    norm_num [outputMass, experiment, conditionalObjectLaw, deterministicOutputLaw,
      Fintype.sum_prod_type, Fintype.sum_bool]

/-- The target-output law is the product of the actual fair marginals. -/
theorem targetOutputLaw_eq_product :
    (targetOutputLaw experiment ()).mass =
      fun zy : Bool × Bool => fairLaw.mass zy.1 * fairLaw.mass zy.2 := by
  funext zy
  change (1 / 2 : ℝ) * outputMass experiment () zy.1 zy.2 = (1 / 2) * (1 / 2)
  rw [outputMass_eq_half]

theorem targetOutputLaw_mass_eq_quarter (zy : Bool × Bool) :
    (targetOutputLaw experiment ()).mass zy = 1 / 4 := by
  rw [targetOutputLaw_eq_product]
  norm_num [fairLaw]

theorem targetOutputLaw_positive (zy : Bool × Bool) :
    0 < (targetOutputLaw experiment ()).mass zy := by
  rw [targetOutputLaw_mass_eq_quarter]
  norm_num

/-- The same product law has zero target-output information. -/
theorem informationAt_zero :
    jointMI (targetOutputLaw experiment ()).mass = 0 := by
  rw [targetOutputLaw_eq_product]
  exact jointMI_product_eq_zero fairLaw fairLaw

theorem conditionalMI_zero : conditionalMI experiment = 0 := by
  unfold conditionalMI
  apply Finset.sum_eq_zero
  intro w _
  cases w
  rw [informationAt_zero, mul_zero]

/-- Both separating objects have positive source mass by objectMarginal_positive. -/
theorem answer_nonconstant :
    ∃ o o', experiment.answer () o ≠ experiment.answer () o' := by
  refine ⟨(false, false), (false, true), ?_⟩
  intro h
  change false = true at h
  cases h

theorem not_echoAt : ¬ EchoAt experiment () := by
  intro he
  obtain ⟨o, o', hne⟩ := answer_nonconstant
  exact hne (he o o')

/-- Full-support target and nuisance bits refute the converse from zero
conditional information to pairwise structural echo. -/
theorem nuisance_counterexample :
    ¬ EchoAt experiment () ∧ conditionalMI experiment = 0 ∧
      (∀ o, 0 < objectMarginal o) ∧
      (∀ zy, 0 < (targetOutputLaw experiment ()).mass zy) :=
  ⟨not_echoAt, conditionalMI_zero, objectMarginal_positive, targetOutputLaw_positive⟩

#check @fairLaw
#print axioms fairLaw
#check @conditionalObjectLaw
#print axioms conditionalObjectLaw
#check @deterministicOutputLaw
#print axioms deterministicOutputLaw
#check @experiment
#print axioms experiment
#check @objectMarginal
#print axioms objectMarginal
#check @objectMarginal_eq_quarter
#print axioms objectMarginal_eq_quarter
#check @objectMarginal_positive
#print axioms objectMarginal_positive
#check @outputMass_eq_half
#print axioms outputMass_eq_half
#check @targetOutputLaw_eq_product
#print axioms targetOutputLaw_eq_product
#check @targetOutputLaw_mass_eq_quarter
#print axioms targetOutputLaw_mass_eq_quarter
#check @targetOutputLaw_positive
#print axioms targetOutputLaw_positive
#check @informationAt_zero
#print axioms informationAt_zero
#check @conditionalMI_zero
#print axioms conditionalMI_zero
#check @answer_nonconstant
#print axioms answer_nonconstant
#check @not_echoAt
#print axioms not_echoAt
#check @nuisance_counterexample
#print axioms nuisance_counterexample

end OperatorKO7.Meta.BoundaryObserver.EchoEvidence.NuisanceFixture

