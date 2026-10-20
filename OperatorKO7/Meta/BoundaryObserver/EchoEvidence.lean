import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-!
# Conditional target information through an object answer

The source law consists of an initial record, a target conditional on that record,
an object conditional on both, and an output law indexed by the record and the
object answer. Every component is a normalized nonnegative finite law.

Relation: finite probability laws and their conditional channels.
Trust: ordinary entropy algebra and the standard classical analysis baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.EchoEvidence

open scoped BigOperators
open ProtocolResolution
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-- The output interface factors through the object answer and initial record. -/
structure Experiment (W Z O A Y : Type)
    [Fintype W] [Fintype Z] [Fintype O] [Fintype Y] where
  initial : FiniteLaw W
  target : W → FiniteLaw Z
  object : W → Z → FiniteLaw O
  answer : W → O → A
  output : W → A → FiniteLaw Y

section Source
variable {W Z O A Y : Type}
variable [Fintype W] [Fintype Z] [Fintype O] [Fintype Y]

/-- Actual output mass after marginalizing the conditional object law. -/
noncomputable def outputMass (E : Experiment W Z O A Y)
    (w : W) (z : Z) (y : Y) : ℝ :=
  ∑ o, (E.object w z).mass o * (E.output w (E.answer w o)).mass y

theorem outputMass_nonnegative (E : Experiment W Z O A Y)
    (w : W) (z : Z) (y : Y) : 0 ≤ outputMass E w z y := by
  apply Finset.sum_nonneg
  intro o _
  exact mul_nonneg ((E.object w z).nonnegative o)
    ((E.output w (E.answer w o)).nonnegative y)

theorem outputMass_total (E : Experiment W Z O A Y)
    (w : W) (z : Z) : ∑ y, outputMass E w z y = 1 := by
  unfold outputMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FiniteLaw.total, mul_one]
  exact (E.object w z).total

/-- The marginalized output row is a probability law. -/
noncomputable def outputLaw (E : Experiment W Z O A Y)
    (w : W) (z : Z) : FiniteLaw Y where
  mass := outputMass E w z
  nonnegative := outputMass_nonnegative E w z
  total := outputMass_total E w z

/-- The conditional joint law uses the same target and the derived output row. -/
noncomputable def targetOutputLaw (E : Experiment W Z O A Y)
    (w : W) : FiniteLaw (Z × Y) where
  mass zy := (E.target w).mass zy.1 * outputMass E w zy.1 zy.2
  nonnegative zy := mul_nonneg ((E.target w).nonnegative zy.1)
    (outputMass_nonnegative E w zy.1 zy.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, outputMass_total, mul_one]
    exact (E.target w).total

/-- The full initial-record/target-output joint law. -/
noncomputable def jointLaw (E : Experiment W Z O A Y) :
    FiniteLaw (W × (Z × Y)) where
  mass wzy := E.initial.mass wzy.1 * (targetOutputLaw E wzy.1).mass wzy.2
  nonnegative wzy := mul_nonneg (E.initial.nonnegative wzy.1)
    ((targetOutputLaw E wzy.1).nonnegative wzy.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteLaw.total, mul_one]
    exact E.initial.total

theorem jointLaw_initial_marginal (E : Experiment W Z O A Y) (w : W) :
    ∑ zy, (jointLaw E).mass (w, zy) = E.initial.mass w := by
  change (∑ zy, E.initial.mass w * (targetOutputLaw E w).mass zy) =
    E.initial.mass w
  rw [← Finset.mul_sum, FiniteLaw.total, mul_one]

/-- Conditional mutual information of the source target and output, in bits. -/
noncomputable def conditionalMI (E : Experiment W Z O A Y) : ℝ :=
  ∑ w, E.initial.mass w * jointMI (targetOutputLaw E w).mass

/-- Summing a normalized object law leaves the common answer-indexed row. -/
theorem outputMass_eq_of_constant (E : Experiment W Z O A Y)
    (w : W) (a : A) (ha : ∀ o, E.answer w o = a) (z : Z) (y : Y) :
    outputMass E w z y = (E.output w a).mass y := by
  unfold outputMass
  simp_rw [ha]
  rw [← Finset.sum_mul, FiniteLaw.total, one_mul]

end Source

/-- The native mutual-information functional vanishes on an actual product law. -/
theorem jointMI_product_eq_zero {Z Y : Type} [Fintype Z] [Fintype Y]
    (p : FiniteLaw Z) (q : FiniteLaw Y) :
    jointMI (fun zy : Z × Y => p.mass zy.1 * q.mass zy.2) = 0 := by
  have hl : (fun z => ∑ y, p.mass z * q.mass y) = p.mass := by
    funext z
    rw [← Finset.mul_sum, q.total, mul_one]
  have hr : (fun y => ∑ z, p.mass z * q.mass y) = q.mass := by
    funext y
    rw [← Finset.sum_mul, p.total, one_mul]
  change entropy (fun z => ∑ y, p.mass z * q.mass y) +
    entropy (fun y => ∑ z, p.mass z * q.mass y) -
    entropy (fun zy : Z × Y => p.mass zy.1 * q.mass zy.2) = 0
  rw [hl, hr]
  simp only [entropy_eq_HBits]
  rw [HBits_product p.mass q.mass p.total q.total]
  ring

section Echo
variable {W Z O A Y : Type}
variable [Fintype W] [Fintype Z] [Fintype O] [Fintype Y]

/-- A constant answer gives a product joint law at the specified initial cell. -/
theorem informationAt_eq_zero_of_constant (E : Experiment W Z O A Y)
    (w : W) (a : A) (ha : ∀ o, E.answer w o = a) :
    jointMI (targetOutputLaw E w).mass = 0 := by
  have hmass : (targetOutputLaw E w).mass =
      fun zy : Z × Y => (E.target w).mass zy.1 * (E.output w a).mass zy.2 := by
    funext zy
    change (E.target w).mass zy.1 * outputMass E w zy.1 zy.2 = _
    rw [outputMass_eq_of_constant E w a ha]
  rw [hmass]
  exact jointMI_product_eq_zero (E.target w) (E.output w a)

/-- Constant object answers on positive initial cells give zero conditional
target-output mutual information under the declared channel factorization. -/
theorem conditionalMI_eq_zero_of_echo (E : Experiment W Z O A Y)
    (he : ∀ w, 0 < E.initial.mass w → ∃ a, ∀ o, E.answer w o = a) :
    conditionalMI E = 0 := by
  unfold conditionalMI
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : E.initial.mass w = 0
  · simp [hw]
  · have hp : 0 < E.initial.mass w :=
      lt_of_le_of_ne (E.initial.nonnegative w) (Ne.symm hw)
    obtain ⟨a, ha⟩ := he w hp
    rw [informationAt_eq_zero_of_constant E w a ha, mul_zero]

end Echo

/-- A normalized finite law has a nonempty carrier. -/
theorem finiteLaw_nonempty {X : Type} [Fintype X] (p : FiniteLaw X) :
    Nonempty X := by
  classical
  by_contra hn
  have hz : (∑ x, p.mass x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact False.elim (hn ⟨x⟩)
  have htotal := p.total
  rw [hz] at htotal
  norm_num at htotal

section PairwiseEcho
variable {W Z O A Y : Type}
variable [Fintype W] [Fintype Z] [Fintype O] [Fintype Y]

/-- Structural echo is equality of the answer on every object pair. -/
def EchoAt (E : Experiment W Z O A Y) (w : W) : Prop :=
  ∀ o o', E.answer w o = E.answer w o'

/-- The normalized source laws supply the object needed to select a common answer. -/
theorem exists_answer_of_echo (E : Experiment W Z O A Y)
    (w : W) (he : EchoAt E w) : ∃ a, ∀ o, E.answer w o = a := by
  obtain ⟨z⟩ := finiteLaw_nonempty (E.target w)
  obtain ⟨o₀⟩ := finiteLaw_nonempty (E.object w z)
  exact ⟨E.answer w o₀, fun o => he o o₀⟩

/-- Pairwise echo gives zero target information under the answer-indexed interface. -/
theorem informationAt_eq_zero_of_echo (E : Experiment W Z O A Y)
    (w : W) (he : EchoAt E w) :
    jointMI (targetOutputLaw E w).mass = 0 := by
  obtain ⟨a, ha⟩ := exists_answer_of_echo E w he
  exact informationAt_eq_zero_of_constant E w a ha

/-- Pairwise echo on positive initial cells gives zero conditional information. -/
theorem conditionalMI_eq_zero_of_pairwise_echo (E : Experiment W Z O A Y)
    (he : ∀ w, 0 < E.initial.mass w → EchoAt E w) :
    conditionalMI E = 0 := by
  apply conditionalMI_eq_zero_of_echo E
  intro w hw
  exact exists_answer_of_echo E w (he w hw)

end PairwiseEcho

#check @Experiment
#print axioms Experiment
#check @Experiment.mk
#print axioms Experiment.mk
#check @Experiment.initial
#print axioms Experiment.initial
#check @Experiment.target
#print axioms Experiment.target
#check @Experiment.object
#print axioms Experiment.object
#check @Experiment.answer
#print axioms Experiment.answer
#check @Experiment.output
#print axioms Experiment.output
#check @outputMass
#print axioms outputMass
#check @outputLaw
#print axioms outputLaw
#check @targetOutputLaw
#print axioms targetOutputLaw
#check @jointLaw
#print axioms jointLaw
#check @conditionalMI
#print axioms conditionalMI
#check @finiteLaw_nonempty
#print axioms finiteLaw_nonempty
#check @EchoAt
#print axioms EchoAt
#check @exists_answer_of_echo
#print axioms exists_answer_of_echo
#check @informationAt_eq_zero_of_echo
#print axioms informationAt_eq_zero_of_echo
#check @conditionalMI_eq_zero_of_pairwise_echo
#print axioms conditionalMI_eq_zero_of_pairwise_echo

#check @outputMass_nonnegative
#print axioms outputMass_nonnegative
#check @outputMass_total
#print axioms outputMass_total
#check @jointLaw_initial_marginal
#print axioms jointLaw_initial_marginal
#check @outputMass_eq_of_constant
#print axioms outputMass_eq_of_constant
#check @jointMI_product_eq_zero
#print axioms jointMI_product_eq_zero
#check @informationAt_eq_zero_of_constant
#print axioms informationAt_eq_zero_of_constant
#check @conditionalMI_eq_zero_of_echo
#print axioms conditionalMI_eq_zero_of_echo

end OperatorKO7.Meta.BoundaryObserver.EchoEvidence

