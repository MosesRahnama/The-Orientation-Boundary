import OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
import OperatorKO7.Meta.BoundaryObserver.AcceptedCertificate
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Persistent binary evidence without a uniform positive discrimination floor

Every state carries actual binaryKernelLaw output rows. Their discrimination
is computed from those rows. The modal property uses AcceptedCertificate.Path
and AcceptedCertificate.Persistent on the successor-state relation.

Relation: n to n+1; finite binary source laws.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.PersistentBinaryEvidence

open scoped BigOperators Topology
open Filter
open ProtocolResolution
open AcceptedCertificate

/-- Positive binary-channel bias at state n. -/
noncomputable def epsilon (n : ℕ) : ℝ := (1 / 4) * (1 / 2) ^ n

theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by
  exact mul_pos (by norm_num) (pow_pos (by norm_num) n)

theorem epsilon_succ (n : ℕ) : epsilon (n + 1) = epsilon n * (1 / 2) := by
  simp only [epsilon, pow_succ]
  ring

theorem epsilon_eq_half_pow (n : ℕ) :
    epsilon n = (1 / 2 : ℝ) ^ (n + 2) := by
  simp only [epsilon, pow_add, pow_two]
  ring

theorem epsilon_le_quarter (n : ℕ) : epsilon n ≤ 1 / 4 := by
  have hpow : (1 / 2 : ℝ) ^ n ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  unfold epsilon
  nlinarith

theorem epsilon_le_half (n : ℕ) : epsilon n ≤ 1 / 2 := by
  have h := epsilon_le_quarter n
  linarith

theorem epsilon_abs_le_half (n : ℕ) : |epsilon n| ≤ 1 / 2 := by
  rw [abs_of_pos (epsilon_pos n)]
  exact epsilon_le_half n

/-- The same bias supplies the exponential scaling used in the frozen-state cost bound. -/
theorem epsilon_sq_mul_four_pow (n : ℕ) :
    epsilon n ^ 2 * (4 : ℝ) ^ n = 1 / 16 := by
  induction n with
  | zero => norm_num [epsilon]
  | succ n ih =>
      rw [epsilon_succ, pow_succ (4 : ℝ) n]
      calc
        (epsilon n * (1 / 2)) ^ 2 * ((4 : ℝ) ^ n * 4)
            = epsilon n ^ 2 * (4 : ℝ) ^ n := by ring
        _ = 1 / 16 := ih

theorem epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Tendsto (fun n : ℕ => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0)
  simpa only [mul_zero] using hpow.const_mul (1 / 4 : ℝ)

/-- The answer is the actual conditional output row for the specified object bit. -/
noncomputable def answer (n : ℕ) (z : Bool) : Bool → ℝ :=
  (binaryKernelLaw (epsilon n) (epsilon_abs_le_half n) z).mass

theorem answer_total (n : ℕ) (z : Bool) : ∑ y, answer n z y = 1 :=
  binaryKernel_total (epsilon n) z

theorem answer_positive (n : ℕ) (z y : Bool) : 0 < answer n z y := by
  have hp := epsilon_pos n
  have hu := epsilon_le_quarter n
  change 0 < binaryKernel (epsilon n) z y
  unfold binaryKernel
  split_ifs <;> linarith

theorem exogenous (n : ℕ) : Exogenous answer n := by
  refine ⟨false, true, ?_⟩
  intro h
  have hc : (1 / 2 : ℝ) + epsilon n = (1 / 2 : ℝ) - epsilon n := by
    simpa [answer, binaryKernelLaw, binaryKernel] using congrFun h false
  have hp := epsilon_pos n
  linarith

/-- The state transition advances one place in the decay sequence. -/
def step (n m : ℕ) : Prop := m = n + 1

theorem reachable_from_zero (n : ℕ) : Path step 0 n := by
  induction n with
  | zero => exact AcceptedCertificate.Path.refl 0
  | succ n ih => exact AcceptedCertificate.Path.step ih rfl

theorem persistent (n : ℕ) : Persistent step answer n := by
  intro m _
  exact exogenous m

/-- Triangular discrimination of the actual two normalized binary output rows. -/
noncomputable def discrimination (n : ℕ) : ℝ :=
  ∑ y : Bool, (answer n false y - answer n true y) ^ 2 /
    (answer n false y + answer n true y)

theorem discrimination_denominator (n : ℕ) (y : Bool) :
    answer n false y + answer n true y = 1 := by
  cases y <;> simp [answer, binaryKernelLaw, binaryKernel] <;> ring

theorem discrimination_eq_eight_mul_sq (n : ℕ) :
    discrimination n = 8 * epsilon n ^ 2 := by
  unfold discrimination
  rw [Fintype.sum_bool]
  simp only [discrimination_denominator, div_one]
  change ((1 / 2 - epsilon n) - (1 / 2 + epsilon n)) ^ 2 +
    ((1 / 2 + epsilon n) - (1 / 2 - epsilon n)) ^ 2 = 8 * epsilon n ^ 2
  ring

theorem discrimination_pos (n : ℕ) : 0 < discrimination n := by
  rw [discrimination_eq_eight_mul_sq]
  exact mul_pos (by norm_num) (pow_pos (epsilon_pos n) 2)

theorem discrimination_tendsto_zero :
    Tendsto discrimination atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => discrimination n) atTop (𝓝 0)
  simp_rw [discrimination_eq_eight_mul_sq]
  simpa using
    (epsilon_tendsto_zero.pow 2).const_mul (8 : ℝ)

theorem no_uniform_positive_discrimination :
    ¬ ∃ d : ℝ, 0 < d ∧ ∀ n, d ≤ discrimination n := by
  rintro ⟨d, hd, hbound⟩
  have hz : d ≤ 0 := ge_of_tendsto' discrimination_tendsto_zero hbound
  exact (not_le_of_gt hd) hz

theorem no_uniform_reachable_discrimination :
    ¬ ∃ d : ℝ, 0 < d ∧ ∀ n, Path step 0 n → d ≤ discrimination n := by
  rintro ⟨d, hd, hbound⟩
  apply no_uniform_positive_discrimination
  exact ⟨d, hd, fun n => hbound n (reachable_from_zero n)⟩

/-- The actual joint law uses a fair target and the same state's binary kernel. -/
noncomputable def fairJointLaw (n : ℕ) : FiniteLaw (Bool × Bool) :=
  binaryJointLaw (1 / 2) (epsilon n) (by norm_num) (by norm_num)
    (epsilon_abs_le_half n)

theorem fair_information_pos (n : ℕ) :
    0 < jointMI (fairJointLaw n).mass := by
  change 0 < jointMI (binaryJoint (1 / 2) (epsilon n))
  rw [binaryJoint_information_fair]
  have hne : (1 / 2 : ℝ) + epsilon n ≠ 2⁻¹ := by
    have hp := epsilon_pos n
    norm_num
    linarith
  have hent : Real.binEntropy (1 / 2 + epsilon n) < Real.log 2 :=
    Real.binEntropy_lt_log_two.mpr hne
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  exact sub_pos.mpr ((div_lt_one hlog).mpr hent)

/-- One concrete family is persistent and informative but has no positive
discrimination floor over its reachable states. -/
theorem persistence_without_uniform_floor :
    Persistent step answer 0 ∧
      (∀ n, 0 < jointMI (fairJointLaw n).mass) ∧
      ¬ ∃ d : ℝ, 0 < d ∧ ∀ n, Path step 0 n → d ≤ discrimination n :=
  ⟨persistent 0, fair_information_pos, no_uniform_reachable_discrimination⟩

#check @epsilon
#print axioms epsilon
#check @epsilon_pos
#print axioms epsilon_pos
#check @epsilon_succ
#print axioms epsilon_succ
#check @epsilon_eq_half_pow
#print axioms epsilon_eq_half_pow
#check @epsilon_le_quarter
#print axioms epsilon_le_quarter
#check @epsilon_le_half
#print axioms epsilon_le_half
#check @epsilon_abs_le_half
#print axioms epsilon_abs_le_half
#check @epsilon_sq_mul_four_pow
#print axioms epsilon_sq_mul_four_pow
#check @epsilon_tendsto_zero
#print axioms epsilon_tendsto_zero
#check @answer
#print axioms answer
#check @answer_total
#print axioms answer_total
#check @answer_positive
#print axioms answer_positive
#check @exogenous
#print axioms exogenous
#check @step
#print axioms step
#check @reachable_from_zero
#print axioms reachable_from_zero
#check @persistent
#print axioms persistent
#check @discrimination
#print axioms discrimination
#check @discrimination_denominator
#print axioms discrimination_denominator
#check @discrimination_eq_eight_mul_sq
#print axioms discrimination_eq_eight_mul_sq
#check @discrimination_pos
#print axioms discrimination_pos
#check @discrimination_tendsto_zero
#print axioms discrimination_tendsto_zero
#check @no_uniform_positive_discrimination
#print axioms no_uniform_positive_discrimination
#check @no_uniform_reachable_discrimination
#print axioms no_uniform_reachable_discrimination
#check @fairJointLaw
#print axioms fairJointLaw
#check @fair_information_pos
#print axioms fair_information_pos
#check @persistence_without_uniform_floor
#print axioms persistence_without_uniform_floor

end OperatorKO7.Meta.BoundaryObserver.PersistentBinaryEvidence

