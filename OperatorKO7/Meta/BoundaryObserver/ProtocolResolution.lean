import OperatorKO7.Meta.BoundaryObserver.StochasticGraph
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.List.Induction
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

/-!
# Protocol information from finite probability laws

Graph: notes/universal-roadmap/UNIVERSAL-OBSERVATION-PROOF-GRAPH.md, M3_1, M3_2, M3_3 and M3_5.
Contract: UniversalObservationSpec.lean, namespace Protocol; no specification import.
Entropy uses the native BitDivision functional, converted from nats to bits.
The binary joint mass is prior times the signed-bias channel, not a supplied gain.
The algebraic identities extend to real weights; binaryJointLaw supplies the probability domain.
Later sections add the adaptive, stopped and unbounded bounds and the M3.5 resource frontier.
Relation: finite joint probability laws. External trust: none.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ProtocolResolution

open scoped BigOperators

/-- A normalized, nonnegative mass function on the stated finite carrier. -/
structure FiniteLaw (A : Type) [Fintype A] where
  mass : A → ℝ
  nonnegative : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

/-- Native finite entropy in bits. -/
noncomputable def entropy {A : Type} [Fintype A] (p : A → ℝ) : ℝ :=
  BitDivision.entropy p / Real.log 2

/-- Mutual information from the two marginals and the same joint mass, in bits. -/
noncomputable def jointMI {A B : Type} [Fintype A] [Fintype B]
    (p : A × B → ℝ) : ℝ :=
  entropy (fun a => ∑ b, p (a, b)) + entropy (fun b => ∑ a, p (a, b)) - entropy p

/-- The native HBits functional and the production entropy have the same source. -/
theorem entropy_eq_HBits {A : Type} [Fintype A] (p : A → ℝ) :
    entropy p =
      OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy.HBits p := rfl

/-- The specification's explicit zero-mass convention agrees with native entropy. -/
theorem entropy_eq_source_formula {A : Type} [Fintype A] (p : A → ℝ) :
    entropy p = - ∑ a, if p a = 0 then 0 else p a * Real.log (p a) / Real.log 2 := by
  classical
  unfold entropy BitDivision.entropy
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : p a = 0
  · simp [h]
  · simp only [h, if_false, Real.negMulLog]
    ring

/-- The entropy chain identity is derived by expanding each joint cell. -/
theorem native_entropy_joint_kernel {Z Y : Type} [Fintype Z] [Fintype Y]
    (p : Z → ℝ) (K : Z → Y → ℝ) (hK : ∀ z, ∑ y, K z y = 1) :
    BitDivision.entropy (fun zy : Z × Y => p zy.1 * K zy.1 zy.2) =
      BitDivision.entropy p + ∑ z, p z * BitDivision.entropy (K z) := by
  unfold BitDivision.entropy
  rw [Fintype.sum_prod_type]
  simp only [Real.negMulLog_mul]
  calc
    (∑ z, ∑ y, (K z y * Real.negMulLog (p z) + p z * Real.negMulLog (K z y))) =
        ∑ z, (Real.negMulLog (p z) + p z * ∑ y, Real.negMulLog (K z y)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hK z, one_mul]
    _ = _ := Finset.sum_add_distrib

/-- The same law-derived chain identity in bits. -/
theorem entropy_joint_kernel {Z Y : Type} [Fintype Z] [Fintype Y]
    (p : Z → ℝ) (K : Z → Y → ℝ) (hK : ∀ z, ∑ y, K z y = 1) :
    entropy (fun zy : Z × Y => p zy.1 * K zy.1 zy.2) =
      entropy p + ∑ z, p z * entropy (K z) := by
  unfold entropy
  rw [native_entropy_joint_kernel p K hK]
  simp only [add_div, Finset.sum_div, mul_div_assoc]

/-- The true label has prior mass q; false has mass 1-q. -/
noncomputable def binaryPrior (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

/-- Signed bias delta gives agreement probability 1/2+delta. -/
noncomputable def binaryKernel (δ : ℝ) (b y : Bool) : ℝ :=
  if y = b then 1 / 2 + δ else 1 / 2 - δ

/-- The source joint mass for an arbitrary prior and a signed-bias binary channel. -/
noncomputable def binaryJoint (q δ : ℝ) (by_ : Bool × Bool) : ℝ :=
  binaryPrior q by_.1 * binaryKernel δ by_.1 by_.2

theorem binaryPrior_total (q : ℝ) : ∑ b, binaryPrior q b = 1 := by
  simp [binaryPrior]

theorem binaryPrior_nonnegative (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) :
    0 ≤ binaryPrior q b := by
  cases b
  · exact sub_nonneg.mpr hq1
  · exact hq0

theorem binaryKernel_total (δ : ℝ) (b : Bool) : ∑ y, binaryKernel δ b y = 1 := by
  simpa only [binaryKernel, Fintype.sum_bool] using BitDivision.readingWeight_sum δ b

theorem binaryKernel_nonnegative (δ : ℝ) (hδ : |δ| ≤ 1 / 2) (b y : Bool) :
    0 ≤ binaryKernel δ b y := by
  obtain ⟨hl, hu⟩ := abs_le.mp hδ
  unfold binaryKernel
  split_ifs <;> linarith

/-- The binary kernel is a native channel at every bias in [-1/2,1/2]. -/
noncomputable def binaryChannel (δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    StochasticGraph.Channel Bool Bool where
  prob := binaryKernel δ
  nonneg := binaryKernel_nonnegative δ hδ
  row_sum := binaryKernel_total δ

noncomputable def binaryPriorLaw (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    FiniteLaw Bool where
  mass := binaryPrior q
  nonnegative := binaryPrior_nonnegative q hq0 hq1
  total := binaryPrior_total q

theorem binaryJoint_input_marginal (q δ : ℝ) (b : Bool) :
    ∑ y, binaryJoint q δ (b, y) = binaryPrior q b := by
  change (∑ y, binaryPrior q b * binaryKernel δ b y) = binaryPrior q b
  rw [← Finset.mul_sum, binaryKernel_total, mul_one]

theorem binaryJoint_output_marginal (q δ : ℝ) (y : Bool) :
    ∑ b, binaryJoint q δ (b, y) = binaryPrior (1 / 2 - δ + 2 * δ * q) y := by
  cases y <;> simp [binaryJoint, binaryPrior, binaryKernel] <;> ring

theorem binaryJoint_total (q δ : ℝ) : ∑ by_, binaryJoint q δ by_ = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [binaryJoint_input_marginal]
  exact binaryPrior_total q

/-- The actual joint probability law, including zero prior masses and deterministic endpoints. -/
noncomputable def binaryJointLaw (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) : FiniteLaw (Bool × Bool) where
  mass := binaryJoint q δ
  nonnegative by_ := mul_nonneg (binaryPrior_nonnegative q hq0 hq1 by_.1)
    (binaryKernel_nonnegative δ hδ by_.1 by_.2)
  total := binaryJoint_total q δ

/-- The joint-law constructor uses precisely the native channel and the same prior. -/
theorem binaryJointLaw_source (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (b y : Bool) :
    (binaryJointLaw q δ hq0 hq1 hδ).mass (b, y) =
      (binaryPriorLaw q hq0 hq1).mass b * (binaryChannel δ hδ).prob b y := rfl

/-- The fair-prior source specializes to the existing readingJoint, cell by cell. -/
theorem binaryJoint_fair_source (δ : ℝ) (b y : Bool) :
    binaryJoint (1 / 2) δ (b, y) = BitDivision.readingJoint δ b y := by
  cases b <;> norm_num [binaryJoint, binaryPrior, binaryKernel, BitDivision.readingJoint]

theorem binaryPrior_entropy (q : ℝ) :
    BitDivision.entropy (binaryPrior q) = Real.binEntropy q := by
  simp [BitDivision.entropy, binaryPrior,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem binaryKernel_entropy (δ : ℝ) (b : Bool) :
    BitDivision.entropy (binaryKernel δ b) = Real.binEntropy (1 / 2 + δ) := by
  simpa only [BitDivision.entropy, binaryKernel, Fintype.sum_bool] using
    BitDivision.readingWeight_entropy δ b

/-- Joint entropy is derived from the input law and each normalized channel row. -/
theorem binaryJoint_entropy (q δ : ℝ) :
    BitDivision.entropy (binaryJoint q δ) =
      Real.binEntropy q + Real.binEntropy (1 / 2 + δ) := by
  unfold binaryJoint
  rw [native_entropy_joint_kernel (binaryPrior q) (binaryKernel δ) (binaryKernel_total δ)]
  simp only [binaryPrior_entropy, binaryKernel_entropy]
  rw [← Finset.sum_mul, binaryPrior_total, one_mul]

/-- The all-prior information formula follows from the actual joint mass and both marginals. -/
theorem binaryJoint_information (q δ : ℝ) :
    jointMI (binaryJoint q δ) =
      (Real.binEntropy (1 / 2 - δ + 2 * δ * q) - Real.binEntropy (1 / 2 + δ)) /
        Real.log 2 := by
  have hi : (fun b => ∑ y, binaryJoint q δ (b, y)) = binaryPrior q :=
    funext (binaryJoint_input_marginal q δ)
  have ho : (fun y => ∑ b, binaryJoint q δ (b, y)) =
      binaryPrior (1 / 2 - δ + 2 * δ * q) :=
    funext (binaryJoint_output_marginal q δ)
  unfold jointMI entropy
  rw [hi, ho]
  simp only [binaryPrior_entropy, binaryJoint_entropy]
  ring

/-- The fair prior attains the binary symmetric channel capacity in bits. -/
theorem binaryJoint_information_fair (δ : ℝ) :
    jointMI (binaryJoint (1 / 2) δ) =
      1 - Real.binEntropy (1 / 2 + δ) / Real.log 2 := by
  have ho : (1 / 2 - δ + 2 * δ * (1 / 2) : ℝ) = 1 / 2 := by ring
  have hh : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  rw [binaryJoint_information, ho, hh, sub_div,
    div_self (Real.log_pos one_lt_two).ne']

/-- Every input prior has information at most the fair-prior value.
The inequality also holds for real weights; binaryJointLaw supplies normalized probabilities. -/
theorem binaryJoint_information_le_fair (q δ : ℝ) :
    jointMI (binaryJoint q δ) ≤ jointMI (binaryJoint (1 / 2) δ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    jointMI (binaryJoint q δ) =
        (Real.binEntropy (1 / 2 - δ + 2 * δ * q) - Real.binEntropy (1 / 2 + δ)) /
          Real.log 2 := binaryJoint_information q δ
    _ ≤ (Real.log 2 - Real.binEntropy (1 / 2 + δ)) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog).mpr
        (sub_le_sub_right Real.binEntropy_le_log_two _)
    _ = jointMI (binaryJoint (1 / 2) δ) := by
      rw [binaryJoint_information_fair, sub_div, div_self hlog.ne']

/-- Capacity is an attained upper bound, not an assumed gain equation. -/
theorem binaryJoint_information_le_capacity (q δ : ℝ) :
    jointMI (binaryJoint q δ) ≤
      1 - Real.binEntropy (1 / 2 + δ) / Real.log 2 := by
  calc
    jointMI (binaryJoint q δ) ≤ jointMI (binaryJoint (1 / 2) δ) :=
      binaryJoint_information_le_fair q δ
    _ = _ := binaryJoint_information_fair δ

/-- Reversing the bias only relabels the reported bit and preserves information. -/
theorem binaryJoint_information_neg_bias (q δ : ℝ) :
    jointMI (binaryJoint q (-δ)) = jointMI (binaryJoint q δ) := by
  have ho : (1 / 2 - (-δ) + 2 * (-δ) * q : ℝ) =
      1 - (1 / 2 - δ + 2 * δ * q) := by ring
  have hn : (1 / 2 + (-δ) : ℝ) = 1 - (1 / 2 + δ) := by ring
  simp only [binaryJoint_information, ho, hn, Real.binEntropy_one_sub]

/-- The quadratic bound covers both signs and both deterministic channel endpoints. -/
theorem binaryJoint_information_le_quadratic (q δ : ℝ) (hδ : |δ| ≤ 1 / 2) :
    jointMI (binaryJoint q δ) ≤ 4 * δ ^ 2 := by
  have hscaled : |2 * δ| ≤ 1 := by
    rw [abs_mul, abs_two]
    linarith
  have hgap := FourTestTables.one_sub_binEntropy_le_sq (2 * δ) hscaled
  have he : (1 + 2 * δ) / 2 = (1 / 2 + δ : ℝ) := by ring
  rw [he] at hgap
  calc
    jointMI (binaryJoint q δ) ≤ 1 - Real.binEntropy (1 / 2 + δ) / Real.log 2 :=
      binaryJoint_information_le_capacity q δ
    _ ≤ (2 * δ) ^ 2 := hgap
    _ = 4 * δ ^ 2 := by ring

/-- Every channel with absolute bias at most epsilon obeys the same information ceiling. -/
theorem binaryJoint_information_le_envelope (q δ ε : ℝ)
    (hδε : |δ| ≤ ε) (hε : ε ≤ 1 / 2) :
    jointMI (binaryJoint q δ) ≤ 4 * ε ^ 2 := by
  have hs : δ ^ 2 ≤ ε ^ 2 := sq_le_sq' (abs_le.mp hδε).1 (abs_le.mp hδε).2
  calc
    jointMI (binaryJoint q δ) ≤ 4 * δ ^ 2 :=
      binaryJoint_information_le_quadratic q δ (hδε.trans hε)
    _ ≤ 4 * ε ^ 2 := by linarith

/-- Probability-law form of the all-prior, all-signed-bias envelope. -/
theorem binaryJointLaw_information_le_envelope (q δ ε : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδε : |δ| ≤ ε) (hε : ε ≤ 1 / 2) :
    jointMI (binaryJointLaw q δ hq0 hq1 (hδε.trans hε)).mass ≤ 4 * ε ^ 2 :=
  binaryJoint_information_le_envelope q δ ε hδε hε

/-- Zero signal gives zero information for every prior, without any division by signal. -/
theorem binaryJoint_information_zero_bias (q : ℝ) :
    jointMI (binaryJoint q 0) = 0 := by
  simp [binaryJoint_information]

/-- A certain false label has no initial uncertainty to acquire. -/
theorem binaryJoint_information_prior_zero (δ : ℝ) :
    jointMI (binaryJoint 0 δ) = 0 := by
  have ho : (1 / 2 - δ + 2 * δ * 0 : ℝ) = 1 - (1 / 2 + δ) := by ring
  rw [binaryJoint_information, ho, Real.binEntropy_one_sub, sub_self, zero_div]

/-- A certain true label also gives zero information. -/
theorem binaryJoint_information_prior_one (δ : ℝ) :
    jointMI (binaryJoint 1 δ) = 0 := by
  have ho : (1 / 2 - δ + 2 * δ * 1 : ℝ) = 1 / 2 + δ := by ring
  rw [binaryJoint_information, ho, sub_self, zero_div]

/-- The noiseless positive endpoint returns all prior entropy. -/
theorem binaryJoint_information_positive_endpoint (q : ℝ) :
    jointMI (binaryJoint q (1 / 2)) = Real.binEntropy q / Real.log 2 := by
  have ho : (1 / 2 - (1 / 2) + 2 * (1 / 2) * q : ℝ) = q := by ring
  rw [binaryJoint_information, ho]
  norm_num

/-- The deterministic bit-flip endpoint also returns all prior entropy. -/
theorem binaryJoint_information_negative_endpoint (q : ℝ) :
    jointMI (binaryJoint q (-(1 / 2))) = Real.binEntropy q / Real.log 2 := by
  rw [binaryJoint_information_neg_bias, binaryJoint_information_positive_endpoint]

/-- Upper-only signed bias is insufficient: a nonpositive deterministic flip carries one bit. -/
theorem binaryJoint_upper_only_control :
    (-(1 / 2) : ℝ) ≤ 0 ∧ jointMI (binaryJoint (1 / 2) (-(1 / 2))) = 1 := by
  constructor
  · norm_num
  · rw [binaryJoint_information_negative_endpoint]
    have hh : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
      simpa only [one_div] using Real.binEntropy_two_inv
    rw [hh, div_self (Real.log_pos one_lt_two).ne']

/-! M3.1: the policy, observation, stopping and cost share the same retained history. -/

/-- A finite experiment with history-dependent actions, observations, stopping and cost. -/
structure FiniteProtocol (Z A Y : Type) [Fintype Z] [Fintype A] [Fintype Y] where
  prior : FiniteLaw Z
  policy : List (A × Y) → FiniteLaw A
  observation : List (A × Y) → A → Z → FiniteLaw Y
  stop : List (A × Y) → Bool
  cost : List (A × Y) → A → ℝ
  cost_nonnegative : ∀ h a, 0 ≤ cost h a

section FiniteProtocol
variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

/-- One source transition retains the event and multiplies its actual probability. -/
noncomputable def prefixStep (p : FiniteProtocol Z A Y) (z : Z)
    (acc : List (A × Y) × ℝ) (ay : A × Y) : List (A × Y) × ℝ :=
  (acc.1 ++ [ay], if p.stop acc.1 then 0 else
    acc.2 * (p.policy acc.1).mass ay.1 * (p.observation acc.1 ay.1 z).mass ay.2)

noncomputable def prefixState (p : FiniteProtocol Z A Y) (z : Z)
    (h : List (A × Y)) : List (A × Y) × ℝ :=
  h.foldl (prefixStep p z) ([], p.prior.mass z)

noncomputable def prefixMass (p : FiniteProtocol Z A Y) (z : Z)
    (h : List (A × Y)) : ℝ := (prefixState p z h).2

/-- Cell identity with the specification's fold implementation; no law is assumed. -/
theorem prefixMass_eq_source_fold (p : FiniteProtocol Z A Y) (z : Z)
    (h : List (A × Y)) :
    prefixMass p z h =
      (h.foldl (fun acc ay =>
        (acc.1 ++ [ay], if p.stop acc.1 then (0 : ℝ) else
          acc.2 * (p.policy acc.1).mass ay.1 * (p.observation acc.1 ay.1 z).mass ay.2))
        (([] : List (A × Y)), p.prior.mass z)).2 := rfl

/-- The first fold coordinate is exactly the retained history. -/
theorem prefixState_fst (p : FiniteProtocol Z A Y) (z : Z) (h : List (A × Y)) :
    (prefixState p z h).1 = h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h ay ih =>
    change ((h ++ [ay]).foldl (prefixStep p z) ([], p.prior.mass z)).1 = _
    rw [List.foldl_append]
    change (prefixState p z h).1 ++ [ay] = h ++ [ay]
    rw [ih]

theorem prefixMass_nil (p : FiniteProtocol Z A Y) (z : Z) :
    prefixMass p z [] = p.prior.mass z := rfl

/-- Source recursion is proved from the fold and its retained-history invariant. -/
theorem prefixMass_append (p : FiniteProtocol Z A Y) (z : Z)
    (h : List (A × Y)) (a : A) (y : Y) :
    prefixMass p z (h ++ [(a, y)]) = if p.stop h then 0 else
      prefixMass p z h * (p.policy h).mass a * (p.observation h a z).mass y := by
  unfold prefixMass prefixState
  rw [List.foldl_append]
  change (if p.stop (prefixState p z h).1 then 0 else
      prefixMass p z h * (p.policy (prefixState p z h).1).mass a *
        (p.observation (prefixState p z h).1 a z).mass y) = _
  rw [prefixState_fst]
  rfl

theorem prefixMass_nonnegative (p : FiniteProtocol Z A Y) (z : Z)
    (h : List (A × Y)) : 0 ≤ prefixMass p z h := by
  induction h using List.reverseRecOn with
  | nil => exact p.prior.nonnegative z
  | append_singleton h ay ih =>
    obtain ⟨a, y⟩ := ay
    rw [prefixMass_append]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg ih ((p.policy h).nonnegative a))
        ((p.observation h a z).nonnegative y)

noncomputable def historyMass (p : FiniteProtocol Z A Y) (h : List (A × Y)) : ℝ :=
  ∑ z, prefixMass p z h

noncomputable def posterior (p : FiniteProtocol Z A Y) (h : List (A × Y)) (z : Z) : ℝ :=
  prefixMass p z h / historyMass p h

theorem historyMass_nonnegative (p : FiniteProtocol Z A Y) (h : List (A × Y)) :
    0 ≤ historyMass p h :=
  Finset.sum_nonneg (fun z _ => prefixMass_nonnegative p z h)

theorem prefixMass_le_historyMass (p : FiniteProtocol Z A Y)
    (h : List (A × Y)) (z : Z) : prefixMass p z h ≤ historyMass p h :=
  Finset.single_le_sum (fun z _ => prefixMass_nonnegative p z h) (Finset.mem_univ z)

/-- A zero history mass forces every target cell to be zero. -/
theorem prefixMass_zero_of_historyMass_zero (p : FiniteProtocol Z A Y)
    (h : List (A × Y)) (hw : historyMass p h = 0) (z : Z) : prefixMass p z h = 0 := by
  exact le_antisymm ((prefixMass_le_historyMass p h z).trans_eq hw)
    (prefixMass_nonnegative p z h)

theorem posterior_nonnegative (p : FiniteProtocol Z A Y)
    (h : List (A × Y)) (z : Z) : 0 ≤ posterior p h z :=
  div_nonneg (prefixMass_nonnegative p z h) (historyMass_nonnegative p h)

/-- Posterior normalization is required only at positive-mass histories. -/
theorem posterior_total (p : FiniteProtocol Z A Y) (h : List (A × Y))
    (hw : 0 < historyMass p h) : ∑ z, posterior p h z = 1 := by
  simp only [posterior]
  rw [← Finset.sum_div]
  exact div_self hw.ne'

/-- The weighted posterior recovers the original cells, including zero histories. -/
theorem historyMass_mul_posterior (p : FiniteProtocol Z A Y)
    (h : List (A × Y)) (z : Z) :
    historyMass p h * posterior p h z = prefixMass p z h := by
  by_cases hw : historyMass p h = 0
  · rw [hw, zero_mul, prefixMass_zero_of_historyMass_zero p h hw z]
  · unfold posterior
    calc
      historyMass p h * (prefixMass p z h / historyMass p h) =
          prefixMass p z h * (historyMass p h / historyMass p h) := by ring
      _ = prefixMass p z h := by rw [div_self hw, mul_one]

/-- Every source row conserves target mass before stopping. -/
theorem prefixMass_children (p : FiniteProtocol Z A Y) (h : List (A × Y)) (z : Z) :
    (∑ a, ∑ y, prefixMass p z (h ++ [(a, y)])) =
      if p.stop h then 0 else prefixMass p z h := by
  cases hs : p.stop h with
  | true => simp [prefixMass_append, hs]
  | false =>
    simp only [prefixMass_append, hs, Bool.false_eq_true, if_false]
    calc
      (∑ a, ∑ y, prefixMass p z h * (p.policy h).mass a *
          (p.observation h a z).mass y) =
          ∑ a, prefixMass p z h * (p.policy h).mass a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum, (p.observation h a z).total, mul_one]
      _ = _ := by rw [← Finset.mul_sum, (p.policy h).total, mul_one]

/-- Stop is a function of retained history; no target-dependent external stop is present. -/
noncomputable def stoppedMass (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z)
    (h : List (A × Y)) : ℝ :=
  if h.length ≤ n ∧ (p.stop h = true ∨ h.length = n) then prefixMass p z h else 0

theorem stoppedMass_nonnegative (p : FiniteProtocol Z A Y) (n : ℕ) (z : Z)
    (h : List (A × Y)) : 0 ≤ stoppedMass p n z h := by
  unfold stoppedMass
  split_ifs
  · exact prefixMass_nonnegative p z h
  · exact le_rfl

end FiniteProtocol

/-- One event extends a retained history on the right. -/
def historySnoc {E : Type} (he : List E × E) : List E := he.1 ++ [he.2]

theorem historySnoc_injective {E : Type} : Function.Injective (@historySnoc E) := by
  rintro ⟨h, e⟩ ⟨k, f⟩ heq
  have hr : e :: h.reverse = f :: k.reverse := by
    simpa [historySnoc] using congrArg List.reverse heq
  have hc := List.cons.inj hr
  exact Prod.ext (List.reverse_injective hc.2) hc.1

theorem historySnoc_ne_nil {E : Type} (he : List E × E) : historySnoc he ≠ [] := by
  simp [historySnoc]

open scoped Classical in
/-- The complete finite set of histories of length at most n. -/
noncomputable def historySet (E : Type) [Fintype E] : ℕ → Finset (List E)
  | 0 => {[]}
  | n + 1 => insert [] (((historySet E n) ×ˢ Finset.univ).image historySnoc)

theorem mem_historySet {E : Type} [Fintype E] (n : ℕ) (h : List E) :
    h ∈ historySet E n ↔ h.length ≤ n := by
  classical
  induction n generalizing h with
  | zero => simp [historySet]
  | succ n ih =>
    induction h using List.reverseRecOn with
    | nil => simp [historySet]
    | append_singleton h e _ =>
      rw [historySet]
      constructor
      · intro hm
        rcases Finset.mem_insert.mp hm with hn | hm
        · exact False.elim (historySnoc_ne_nil (h, e) hn)
        · obtain ⟨he, hmem, heq⟩ := Finset.mem_image.mp hm
          have hp : he = (h, e) := historySnoc_injective heq
          subst he
          have hh := (ih h).mp (Finset.mem_product.mp hmem).1
          simpa only [List.length_append, List.length_singleton] using
            Nat.add_le_add_right hh 1
      · intro hh
        have hl : h.length ≤ n := by
          simpa only [List.length_append, List.length_singleton, Nat.add_le_add_iff_right]
            using hh
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨(h, e), Finset.mem_product.mpr ⟨(ih h).mpr hl, Finset.mem_univ e⟩, rfl⟩))

theorem historySet_mono {E : Type} [Fintype E] {n m : ℕ} (hnm : n ≤ m) :
    historySet E n ⊆ historySet E m := by
  intro h hh
  exact (mem_historySet m h).mpr (((mem_historySet n h).mp hh).trans hnm)

/-- The complete-list contract is identical to the specification. -/
def HistoryBank {A Y : Type} (n : ℕ) (bank : List (List (A × Y))) : Prop :=
  bank.Nodup ∧ ∀ h, h ∈ bank ↔ h.length ≤ n

noncomputable def historyBank (A Y : Type) [Fintype A] [Fintype Y] (n : ℕ) :
    List (List (A × Y)) := (historySet (A × Y) n).toList

theorem historyBank_complete (A Y : Type) [Fintype A] [Fintype Y] (n : ℕ) :
    HistoryBank n (historyBank A Y n) := by
  refine ⟨Finset.nodup_toList _, ?_⟩
  intro h
  simp only [historyBank, Finset.mem_toList, mem_historySet]

/-- Any complete bank gives the same finite sum, independent of enumeration order. -/
theorem HistoryBank.sum_eq {A Y : Type} [Fintype A] [Fintype Y]
    {n : ℕ} {bank : List (List (A × Y))} (hb : HistoryBank n bank)
    (f : List (A × Y) → ℝ) :
    (bank.map f).sum = ∑ h ∈ historySet (A × Y) n, f h := by
  have hp : bank.Perm (historySet (A × Y) n).toList :=
    (List.perm_ext_iff_of_nodup hb.1 (Finset.nodup_toList _)).mpr (by
      intro h
      simpa only [Finset.mem_toList, mem_historySet] using hb.2 h)
  exact (hp.map f).sum_eq.trans (Finset.sum_map_toList _ _)

/-- The successor bank is the root and exactly one copy of every child. -/
theorem historySet_sum_succ {E : Type} [Fintype E] (n : ℕ) (f : List E → ℝ) :
    (∑ h ∈ historySet E (n + 1), f h) =
      f [] + ∑ h ∈ historySet E n, ∑ e, f (h ++ [e]) := by
  classical
  have hn : [] ∉ ((historySet E n) ×ˢ Finset.univ).image historySnoc := by
    intro hm
    obtain ⟨he, _, heq⟩ := Finset.mem_image.mp hm
    exact historySnoc_ne_nil he heq
  rw [historySet, Finset.sum_insert hn,
    Finset.sum_image (fun x _ y _ hxy => historySnoc_injective hxy)]
  simp only [Finset.sum_product, historySnoc]

/-- Terms vanishing on the new level can be summed over the preceding bank. -/
theorem historySet_sum_restrict {E : Type} [Fintype E] (n : ℕ) (f : List E → ℝ)
    (hf : ∀ h, h.length = n + 1 → f h = 0) :
    (∑ h ∈ historySet E (n + 1), f h) = ∑ h ∈ historySet E n, f h := by
  classical
  symm
  apply Finset.sum_subset (historySet_mono (Nat.le_succ n))
  intro h hbig hsmall
  have hle := (mem_historySet (n + 1) h).mp hbig
  have hnot : ¬ h.length ≤ n := fun hh => hsmall ((mem_historySet n h).mpr hh)
  exact hf h (by omega)

/-- The boundary retains a stopped node or a node at the finite horizon. -/
noncomputable def boundaryValue {E : Type} (stop : List E → Bool) (n : ℕ)
    (f : List E → ℝ) (h : List E) : ℝ :=
  if h.length ≤ n ∧ (stop h = true ∨ h.length = n) then f h else 0

/-- Only active histories strictly before the horizon receive a local charge. -/
noncomputable def activeValue {E : Type} (stop : List E → Bool) (n : ℕ)
    (f : List E → ℝ) (h : List E) : ℝ :=
  if h.length < n ∧ stop h = false then f h else 0

theorem historySet_active_sum_succ {E : Type} [Fintype E]
    (stop : List E → Bool) (n : ℕ) (f : List E → ℝ) :
    (∑ h ∈ historySet E (n + 1), activeValue stop (n + 1) f h) =
      ∑ h ∈ historySet E n, if stop h then 0 else f h := by
  rw [historySet_sum_restrict n _ (by intro h hh; simp [activeValue, hh])]
  apply Finset.sum_congr rfl
  intro h hh
  have hl : h.length < n + 1 := Nat.lt_succ_of_le ((mem_historySet n h).mp hh)
  cases hs : stop h <;> simp [activeValue, hl, hs]

/-- Finite tree cancellation from node values, with zero children after stopping.
No entropy increment or chain-rule conclusion occurs among the hypotheses. -/
theorem historySet_boundary_balance {E : Type} [Fintype E]
    (stop : List E → Bool) (n : ℕ) (f : List E → ℝ)
    (hstop : ∀ h, stop h = true → ∀ e, f (h ++ [e]) = 0) :
    (∑ h ∈ historySet E n, boundaryValue stop n f h) +
      (∑ h ∈ historySet E n,
        activeValue stop n (fun h => f h - ∑ e, f (h ++ [e])) h) = f [] := by
  cases n with
  | zero => simp [historySet, boundaryValue, activeValue]
  | succ n =>
    have hsplit : (∑ h ∈ historySet E (n + 1), f h) =
        (∑ h ∈ historySet E (n + 1), boundaryValue stop (n + 1) f h) +
        (∑ h ∈ historySet E (n + 1), activeValue stop (n + 1) f h) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h hh
      have hl := (mem_historySet (n + 1) h).mp hh
      by_cases he : h.length = n + 1
      · simp [boundaryValue, activeValue, he]
      · have hlt : h.length < n + 1 := by omega
        cases hs : stop h <;> simp [boundaryValue, activeValue, hl, hlt, he, hs]
    have hdiv :
        (∑ h ∈ historySet E (n + 1),
          activeValue stop (n + 1) (fun h => f h - ∑ e, f (h ++ [e])) h) =
        (∑ h ∈ historySet E (n + 1), activeValue stop (n + 1) f h) -
        (∑ h ∈ historySet E n, ∑ e, f (h ++ [e])) := by
      rw [historySet_active_sum_succ, historySet_active_sum_succ,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro h _
      cases hs : stop h with
      | false => simp
      | true => simp [hstop h hs]
    have hsum := historySet_sum_succ n f
    linarith

section StoppedConservation
variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

/-- Every target's stopped mass is its own prior mass, before averaging targets. -/
theorem historySet_stoppedMass_target_marginal (p : FiniteProtocol Z A Y)
    (n : ℕ) (z : Z) :
    (∑ h ∈ historySet (A × Y) n, stoppedMass p n z h) = p.prior.mass z := by
  have hb := historySet_boundary_balance p.stop n (prefixMass p z) (by
    intro h hs ay
    obtain ⟨a, y⟩ := ay
    simp [prefixMass_append, hs])
  have hz : ∀ h, activeValue p.stop n
      (fun h => prefixMass p z h - ∑ ay : A × Y, prefixMass p z (h ++ [ay])) h = 0 := by
    intro h
    unfold activeValue
    split_ifs with ha
    · have hc : (∑ ay : A × Y, prefixMass p z (h ++ [ay])) = prefixMass p z h := by
        rw [Fintype.sum_prod_type]
        simpa [ha.2] using prefixMass_children p h z
      change prefixMass p z h - (∑ ay : A × Y, prefixMass p z (h ++ [ay])) = 0
      rw [hc, sub_self]
    · rfl
  simp only [hz, Finset.sum_const_zero, add_zero, prefixMass_nil] at hb
  exact hb

/-- Complete list banks preserve the same target marginal as the source fold. -/
theorem stoppedMass_target_marginal (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank) (z : Z) :
    (bank.map (fun h => stoppedMass p n z h)).sum = p.prior.mass z := by
  rw [hb.sum_eq]
  exact historySet_stoppedMass_target_marginal p n z

theorem stoppedMass_total (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    (∑ z, (bank.map (fun h => stoppedMass p n z h)).sum) = 1 := by
  simp only [stoppedMass_target_marginal p n bank hb]
  exact p.prior.total

end StoppedConservation

/-- Native entropy contribution in bits, including the zero-mass value. -/
noncomputable def entropyTerm (x : ℝ) : ℝ := Real.negMulLog x / Real.log 2

theorem entropyTerm_eq_source (x : ℝ) :
    entropyTerm x = if x = 0 then 0 else -x * Real.log x / Real.log 2 := by
  by_cases hx : x = 0
  · simp [entropyTerm, hx]
  · simp only [entropyTerm, Real.negMulLog, hx, if_false]

theorem entropyTerm_zero : entropyTerm 0 = 0 := by simp [entropyTerm]
theorem entropyTerm_one : entropyTerm 1 = 0 := by simp [entropyTerm]

theorem entropyTerm_mul (x y : ℝ) :
    entropyTerm (x * y) = y * entropyTerm x + x * entropyTerm y := by
  unfold entropyTerm
  rw [Real.negMulLog_mul]
  ring

theorem entropy_eq_sum {Z : Type} [Fintype Z] (m : Z → ℝ) :
    entropy m = ∑ z, entropyTerm (m z) := by
  unfold entropy BitDivision.entropy entropyTerm
  exact Finset.sum_div _ _ _

theorem entropy_zero {Z : Type} [Fintype Z] : entropy (fun _ : Z => 0) = 0 := by
  simp [entropy_eq_sum, entropyTerm_zero]

/-- Entropy scaling follows cell by cell, with no positive-mass restriction. -/
theorem entropy_scale {Z : Type} [Fintype Z] (c : ℝ) (m : Z → ℝ) :
    entropy (fun z => c * m z) =
      (∑ z, m z) * entropyTerm c + c * entropy m := by
  simp only [entropy_eq_sum, entropyTerm_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]

/-- Unnormalized conditional entropy of a target slice. -/
noncomputable def massUncertainty {Z : Type} [Fintype Z] (m : Z → ℝ) : ℝ :=
  entropy m - entropyTerm (∑ z, m z)

theorem massUncertainty_zero {Z : Type} [Fintype Z] :
    massUncertainty (fun _ : Z => 0) = 0 := by
  simp [massUncertainty, entropy_zero, entropyTerm_zero]

theorem massUncertainty_scale {Z : Type} [Fintype Z] (c : ℝ) (m : Z → ℝ) :
    massUncertainty (fun z => c * m z) = c * massUncertainty m := by
  unfold massUncertainty
  rw [entropy_scale, ← Finset.mul_sum, entropyTerm_mul]
  ring

theorem massUncertainty_of_total_one {Z : Type} [Fintype Z] (m : Z → ℝ)
    (hm : ∑ z, m z = 1) : massUncertainty m = entropy m := by
  rw [massUncertainty, hm, entropyTerm_one, sub_zero]

/-- Joint entropy is the sum of the entropies of its target slices. -/
theorem entropy_joint_slices {Z Y : Type} [Fintype Z] [Fintype Y]
    (m : Z × Y → ℝ) : entropy m = ∑ y, entropy (fun z => m (z, y)) := by
  simp only [entropy_eq_sum, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The channel information formula is derived from its normalized rows. -/
theorem jointMI_kernel {Z Y : Type} [Fintype Z] [Fintype Y]
    (q : Z → ℝ) (K : Z → Y → ℝ) (hK : ∀ z, ∑ y, K z y = 1) :
    jointMI (fun zy : Z × Y => q zy.1 * K zy.1 zy.2) =
      entropy (fun y => ∑ z, q z * K z y) - ∑ z, q z * entropy (K z) := by
  have hm : (fun z => ∑ y, q z * K z y) = q := by
    funext z
    rw [← Finset.mul_sum, hK z, mul_one]
  unfold jointMI
  change entropy (fun z => ∑ y, q z * K z y) +
    entropy (fun y => ∑ z, q z * K z y) -
    entropy (fun zy : Z × Y => q zy.1 * K zy.1 zy.2) = _
  rw [hm, entropy_joint_kernel q K hK]
  ring

/-- The posterior entropy drop is calculated from the actual joint cells. -/
theorem massUncertainty_kernel_sum {Z Y : Type} [Fintype Z] [Fintype Y]
    (q : Z → ℝ) (K : Z → Y → ℝ) (hK : ∀ z, ∑ y, K z y = 1) :
    (∑ y, massUncertainty (fun z => q z * K z y)) =
      entropy q - jointMI (fun zy : Z × Y => q zy.1 * K zy.1 zy.2) := by
  unfold massUncertainty
  rw [Finset.sum_sub_distrib,
    ← entropy_joint_slices (fun zy : Z × Y => q zy.1 * K zy.1 zy.2),
    ← entropy_eq_sum (fun y => ∑ z, q z * K z y),
    entropy_joint_kernel q K hK, jointMI_kernel q K hK]
  ring

/-- Concavity proves nonnegative information for every normalized input prior. -/
theorem jointMI_kernel_nonnegative {Z Y : Type} [Fintype Z] [Fintype Y]
    (q : Z → ℝ) (K : Z → Y → ℝ) (hq0 : ∀ z, 0 ≤ q z)
    (hq1 : ∑ z, q z = 1) (hK0 : ∀ z y, 0 ≤ K z y)
    (hK1 : ∀ z, ∑ y, K z y = 1) :
    0 ≤ jointMI (fun zy : Z × Y => q zy.1 * K zy.1 zy.2) := by
  have hj : (∑ y, ∑ z, q z * entropyTerm (K z y)) ≤
      ∑ y, entropyTerm (∑ z, q z * K z y) := by
    apply Finset.sum_le_sum
    intro y _
    have hn : (∑ z, q z * Real.negMulLog (K z y)) ≤
        Real.negMulLog (∑ z, q z * K z y) := by
      simpa only [smul_eq_mul] using
        Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := q)
          (p := fun z => K z y) (fun z _ => hq0 z) hq1 (fun z _ => hK0 z y)
    simpa only [entropyTerm, Finset.sum_div, mul_div_assoc] using
      (div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).mpr hn
  rw [jointMI_kernel q K hK1]
  apply sub_nonneg.mpr
  calc
    (∑ z, q z * entropy (K z)) = ∑ y, ∑ z, q z * entropyTerm (K z y) := by
      simp only [entropy_eq_sum, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ _ := hj
    _ = _ := (entropy_eq_sum _).symm

/-- A policy independent of the target adds no information of its own. -/
theorem jointMI_product_zero {Z A : Type} [Fintype Z] [Fintype A]
    (q : Z → ℝ) (r : A → ℝ) (hq : ∑ z, q z = 1) (hr : ∑ a, r a = 1) :
    jointMI (fun za : Z × A => q za.1 * r za.2) = 0 := by
  have ho : (fun a => ∑ z, q z * r a) = r := by
    funext a
    rw [← Finset.sum_mul, hq, one_mul]
  rw [jointMI_kernel q (fun _ => r) (fun _ => hr), ho,
    ← Finset.sum_mul, hq, one_mul, sub_self]

section LocalInformation
variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

noncomputable def localGain (p : FiniteProtocol Z A Y) (h : List (A × Y)) (a : A) : ℝ :=
  jointMI (fun zy : Z × Y =>
    posterior p h zy.1 * (p.observation h a zy.1).mass zy.2)

/-- The capacity premise applies only to reachable, active, positive-action branches. -/
def LocalCapacityBound (p : FiniteProtocol Z A Y) (κ : ℝ) : Prop :=
  ∀ h a, 0 < historyMass p h → p.stop h = false → 0 < (p.policy h).mass a →
    localGain p h a ≤ κ * p.cost h a

/-- Summing observations yields the actual conditional target/action product law. -/
theorem prefixMass_action_marginal (p : FiniteProtocol Z A Y) (h : List (A × Y))
    (hs : p.stop h = false) (z : Z) (a : A) :
    (∑ y, prefixMass p z (h ++ [(a, y)])) / historyMass p h =
      posterior p h z * (p.policy h).mass a := by
  simp only [prefixMass_append, hs, Bool.false_eq_true, if_false]
  rw [← Finset.mul_sum, (p.observation h a z).total, mul_one]
  unfold posterior
  ring

theorem policy_information_zero (p : FiniteProtocol Z A Y) (h : List (A × Y))
    (hw : 0 < historyMass p h) :
    jointMI (fun za : Z × A => posterior p h za.1 * (p.policy h).mass za.2) = 0 :=
  jointMI_product_zero _ _ (posterior_total p h hw) (p.policy h).total

theorem localGain_zero_of_historyMass_zero (p : FiniteProtocol Z A Y)
    (h : List (A × Y)) (hw : historyMass p h = 0) (a : A) : localGain p h a = 0 := by
  simp [localGain, posterior, hw, jointMI, entropy_zero]

theorem localGain_nonnegative (p : FiniteProtocol Z A Y) (h : List (A × Y)) (a : A) :
    0 ≤ localGain p h a := by
  rcases (historyMass_nonnegative p h).eq_or_lt with hw | hw
  · rw [localGain_zero_of_historyMass_zero p h hw.symm a]
  · change 0 ≤ jointMI (fun zy : Z × Y =>
        posterior p h zy.1 * (p.observation h a zy.1).mass zy.2)
    exact jointMI_kernel_nonnegative (Z := Z) (Y := Y)
      (posterior p h) (fun z y => (p.observation h a z).mass y)
      (posterior_nonnegative p h) (posterior_total p h hw)
      (fun z y => (p.observation h a z).nonnegative y)
      (fun z => (p.observation h a z).total)

/-- Weighted posterior entropy equals the uncertainty of the original source cells. -/
theorem massUncertainty_prefix (p : FiniteProtocol Z A Y) (h : List (A × Y)) :
    massUncertainty (fun z => prefixMass p z h) =
      historyMass p h * entropy (posterior p h) := by
  rcases (historyMass_nonnegative p h).eq_or_lt with hw | hw
  · have hm : (fun z => prefixMass p z h) = (fun _ => 0) := by
      funext z
      exact prefixMass_zero_of_historyMass_zero p h hw.symm z
    rw [hm, massUncertainty_zero, ← hw, zero_mul]
  · have hm : (fun z => prefixMass p z h) =
        (fun z => historyMass p h * posterior p h z) := by
      funext z
      exact (historyMass_mul_posterior p h z).symm
    rw [hm, massUncertainty_scale,
      massUncertainty_of_total_one _ (posterior_total p h hw)]

/-- The complete one-step entropy identity is derived from every child mass. -/
theorem massUncertainty_children (p : FiniteProtocol Z A Y) (h : List (A × Y))
    (hs : p.stop h = false) :
    (∑ a, ∑ y, massUncertainty (fun z => prefixMass p z (h ++ [(a, y)]))) =
      massUncertainty (fun z => prefixMass p z h) -
        historyMass p h * ∑ a, (p.policy h).mass a * localGain p h a := by
  have hc (a : A) (y : Y) :
      massUncertainty (fun z => prefixMass p z (h ++ [(a, y)])) =
        (historyMass p h * (p.policy h).mass a) *
          massUncertainty (fun z => posterior p h z * (p.observation h a z).mass y) := by
    have hm : (fun z => prefixMass p z (h ++ [(a, y)])) =
        (fun z => (historyMass p h * (p.policy h).mass a) *
          (posterior p h z * (p.observation h a z).mass y)) := by
      funext z
      rw [prefixMass_append, hs]
      change prefixMass p z h * (p.policy h).mass a * (p.observation h a z).mass y = _
      rw [← historyMass_mul_posterior p h z]
      ring
    rw [hm, massUncertainty_scale]
  have ha (a : A) :
      (∑ y, massUncertainty (fun z => prefixMass p z (h ++ [(a, y)]))) =
        (historyMass p h * (p.policy h).mass a) *
          (entropy (posterior p h) - localGain p h a) := by
    simp only [hc]
    rw [← Finset.mul_sum]
    exact congrArg (fun t => (historyMass p h * (p.policy h).mass a) * t)
      (massUncertainty_kernel_sum (posterior p h)
        (fun z y => (p.observation h a z).mass y) (fun z => (p.observation h a z).total))
  simp only [ha]
  calc
    (∑ a, (historyMass p h * (p.policy h).mass a) *
        (entropy (posterior p h) - localGain p h a)) =
      (∑ a, (p.policy h).mass a) * (historyMass p h * entropy (posterior p h)) -
        historyMass p h * ∑ a, (p.policy h).mass a * localGain p h a := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [(p.policy h).total, one_mul, massUncertainty_prefix]

end LocalInformation

/-- A subtype sum is the same sum over its defining finite set. -/
theorem finset_subtype_sum {H : Type} (s : Finset H) (f : H → ℝ) :
    (∑ h : s, f h.val) = ∑ h ∈ s, f h := by
  rw [Finset.sum_coe_sort_eq_attach]
  exact Finset.sum_attach s f

section FiniteInformation
variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

/-- The stopped joint law has the original target and a retained finite transcript. -/
noncomputable def stoppedJointLaw (p : FiniteProtocol Z A Y) (n : ℕ) :
    FiniteLaw (Z × (historySet (A × Y) n)) where
  mass zh := stoppedMass p n zh.1 zh.2.val
  nonnegative zh := stoppedMass_nonnegative p n zh.1 zh.2.val
  total := by
    rw [Fintype.sum_prod_type]
    simp only [finset_subtype_sum, historySet_stoppedMass_target_marginal]
    exact p.prior.total

/-- This is the specification's terminal information, not a supplied ledger value. -/
noncomputable def terminalMI (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) : ℝ :=
  entropy p.prior.mass +
    (bank.map (fun h => entropyTerm (∑ z, stoppedMass p n z h))).sum -
    ∑ z, (bank.map (fun h => entropyTerm (stoppedMass p n z h))).sum

noncomputable def expectedCost (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) : ℝ :=
  (bank.map (fun h => if h.length < n ∧ p.stop h = false then
    historyMass p h * ∑ a, (p.policy h).mass a * p.cost h a else 0)).sum

/-- The bank expression is mutual information of that very same normalized joint law. -/
theorem terminalMI_eq_jointMI (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    terminalMI p n bank = jointMI (stoppedJointLaw p n).mass := by
  have hi : (fun z => ∑ h : historySet (A × Y) n, stoppedMass p n z h.val) =
      p.prior.mass := by
    funext z
    rw [finset_subtype_sum]
    exact historySet_stoppedMass_target_marginal p n z
  unfold terminalMI jointMI
  change entropy p.prior.mass +
      (bank.map (fun h => entropyTerm (∑ z, stoppedMass p n z h))).sum -
      (∑ z, (bank.map (fun h => entropyTerm (stoppedMass p n z h))).sum) =
    entropy (fun z => ∑ h : historySet (A × Y) n, stoppedMass p n z h.val) +
      entropy (fun h : historySet (A × Y) n => ∑ z, stoppedMass p n z h.val) -
      entropy (fun zh : Z × (historySet (A × Y) n) => stoppedMass p n zh.1 zh.2.val)
  rw [hi]
  simp only [hb.sum_eq, entropy_eq_sum, Fintype.sum_prod_type]
  have ho : (∑ h : historySet (A × Y) n, entropyTerm (∑ z, stoppedMass p n z h.val)) =
      ∑ h ∈ historySet (A × Y) n, entropyTerm (∑ z, stoppedMass p n z h) :=
    finset_subtype_sum (historySet (A × Y) n)
      (fun h => entropyTerm (∑ z, stoppedMass p n z h))
  have hj : (∑ z, ∑ h : historySet (A × Y) n, entropyTerm (stoppedMass p n z h.val)) =
      ∑ z, ∑ h ∈ historySet (A × Y) n, entropyTerm (stoppedMass p n z h) := by
    apply Finset.sum_congr rfl
    intro z _
    exact finset_subtype_sum (historySet (A × Y) n)
      (fun h => entropyTerm (stoppedMass p n z h))
  rw [ho, hj]

/-- Terminal information is initial entropy minus actual stopped conditional entropy. -/
theorem terminalMI_eq_entropy_sub (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    terminalMI p n bank = entropy p.prior.mass -
      ∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => stoppedMass p n z h) := by
  unfold terminalMI
  simp only [hb.sum_eq]
  rw [Finset.sum_comm]
  simp only [massUncertainty, entropy_eq_sum, Finset.sum_sub_distrib]
  ring

noncomputable def historyUncertainty (p : FiniteProtocol Z A Y)
    (h : List (A × Y)) : ℝ := massUncertainty (fun z => prefixMass p z h)

theorem historyUncertainty_nil (p : FiniteProtocol Z A Y) :
    historyUncertainty p [] = entropy p.prior.mass := by
  simp only [historyUncertainty, prefixMass_nil]
  exact massUncertainty_of_total_one _ p.prior.total

theorem historyUncertainty_after_stop (p : FiniteProtocol Z A Y)
    (h : List (A × Y)) (hs : p.stop h = true) (ay : A × Y) :
    historyUncertainty p (h ++ [ay]) = 0 := by
  obtain ⟨a, y⟩ := ay
  simp [historyUncertainty, prefixMass_append, hs, massUncertainty_zero]

theorem historyUncertainty_drop (p : FiniteProtocol Z A Y)
    (h : List (A × Y)) (hs : p.stop h = false) :
    historyUncertainty p h - (∑ ay : A × Y, historyUncertainty p (h ++ [ay])) =
      historyMass p h * ∑ a, (p.policy h).mass a * localGain p h a := by
  unfold historyUncertainty
  rw [Fintype.sum_prod_type, massUncertainty_children p h hs]
  ring

theorem massUncertainty_stopped (p : FiniteProtocol Z A Y) (n : ℕ)
    (h : List (A × Y)) :
    massUncertainty (fun z => stoppedMass p n z h) =
      boundaryValue p.stop n (historyUncertainty p) h := by
  unfold stoppedMass boundaryValue
  split_ifs
  · rfl
  · exact massUncertainty_zero

/-- Exact finite entropy telescope from the source fold, including stopped and zero-mass nodes. -/
theorem terminalMI_eq_gain_sum (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    terminalMI p n bank =
      (bank.map (fun h => if h.length < n ∧ p.stop h = false then
        historyMass p h * ∑ a, (p.policy h).mass a * localGain p h a else 0)).sum := by
  rw [terminalMI_eq_entropy_sub p n bank hb, hb.sum_eq]
  have hbal := historySet_boundary_balance p.stop n (historyUncertainty p)
    (historyUncertainty_after_stop p)
  have hbnd : (∑ h ∈ historySet (A × Y) n,
      boundaryValue p.stop n (historyUncertainty p) h) =
      ∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => stoppedMass p n z h) := by
    apply Finset.sum_congr rfl
    intro h _
    exact (massUncertainty_stopped p n h).symm
  have hac : ∀ h, activeValue p.stop n
      (fun h => historyUncertainty p h - ∑ ay : A × Y, historyUncertainty p (h ++ [ay])) h =
      if h.length < n ∧ p.stop h = false then
        historyMass p h * ∑ a, (p.policy h).mass a * localGain p h a else 0 := by
    intro h
    unfold activeValue
    split_ifs with hh
    · exact historyUncertainty_drop p h hh.2
    · rfl
  rw [hbnd, historyUncertainty_nil] at hbal
  simp only [hac] at hbal
  linarith

/-- Information is nonnegative, including every zero-probability history. -/
theorem terminalMI_nonnegative (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank) : 0 ≤ terminalMI p n bank := by
  rw [terminalMI_eq_gain_sum p n bank hb, hb.sum_eq]
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact mul_nonneg (historyMass_nonnegative p h) (Finset.sum_nonneg (fun a _ =>
      mul_nonneg ((p.policy h).nonnegative a) (localGain_nonnegative p h a)))
  · exact le_rfl

theorem expectedCost_nonnegative (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank) : 0 ≤ expectedCost p n bank := by
  unfold expectedCost
  rw [hb.sum_eq]
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact mul_nonneg (historyMass_nonnegative p h) (Finset.sum_nonneg (fun a _ =>
      mul_nonneg ((p.policy h).nonnegative a) (p.cost_nonnegative h a)))
  · exact le_rfl

/-- Local capacity is used only when both the history and chosen action have positive mass. -/
theorem weightedGain_le_cost (p : FiniteProtocol Z A Y) (κ : ℝ)
    (hc : LocalCapacityBound p κ) (h : List (A × Y)) (hs : p.stop h = false) :
    historyMass p h * (∑ a, (p.policy h).mass a * localGain p h a) ≤
      κ * (historyMass p h * ∑ a, (p.policy h).mass a * p.cost h a) := by
  rcases (historyMass_nonnegative p h).eq_or_lt with hw | hw
  · simp only [← hw, zero_mul, mul_zero, le_refl]
  · have ha : (∑ a, (p.policy h).mass a * localGain p h a) ≤
        κ * ∑ a, (p.policy h).mass a * p.cost h a := by
      calc
        (∑ a, (p.policy h).mass a * localGain p h a) ≤
            ∑ a, (p.policy h).mass a * (κ * p.cost h a) := by
          apply Finset.sum_le_sum
          intro a _
          rcases ((p.policy h).nonnegative a).eq_or_lt with hz | hz
          · simp only [← hz, zero_mul, le_refl]
          · exact mul_le_mul_of_nonneg_left (hc h a hw hs hz) hz.le
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    calc
      historyMass p h * (∑ a, (p.policy h).mass a * localGain p h a) ≤
          historyMass p h * (κ * ∑ a, (p.policy h).mass a * p.cost h a) :=
        mul_le_mul_of_nonneg_left ha hw.le
      _ = _ := by ring

/-- Finite-horizon capacity/cost bound, derived from actual stopped mutual information.
No sign restriction on kappa is needed beyond its local capacity hypothesis. -/
theorem terminalMI_le_expectedCost (p : FiniteProtocol Z A Y) (κ : ℝ) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank)
    (hc : LocalCapacityBound p κ) : terminalMI p n bank ≤ κ * expectedCost p n bank := by
  rw [terminalMI_eq_gain_sum p n bank hb]
  unfold expectedCost
  simp only [hb.sum_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  by_cases hh : h.length < n ∧ p.stop h = false
  · simp only [if_pos hh]
    exact weightedGain_le_cost p κ hc h hh.2
  · simp only [if_neg hh, mul_zero, le_refl]

end FiniteInformation

/-- The actual initial joint law is bound to one protocol for each retained initial record H0.
Persistent available random seeds are part of H0; later policy draws use retained history. -/
structure ConditionalProtocol (H0 Z A Y : Type)
    [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y] where
  initialRecord : FiniteLaw H0
  initialJoint : FiniteLaw (H0 × Z)
  given : H0 → FiniteProtocol Z A Y
  initial_joint : ∀ h z, initialJoint.mass (h, z) =
    initialRecord.mass h * (given h).prior.mass z

section ConditionalInformation
variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

noncomputable def conditionalStoppedMass (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (h0 : H0) (z : Z) (h : List (A × Y)) : ℝ :=
  p.initialRecord.mass h0 * stoppedMass (p.given h0) n z h

noncomputable def conditionalMI (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) : ℝ :=
  ∑ h0, p.initialRecord.mass h0 * terminalMI (p.given h0) n bank

noncomputable def conditionalExpectedCost (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) : ℝ :=
  ∑ h0, p.initialRecord.mass h0 * expectedCost (p.given h0) n bank

/-- H(Z,H0)+H(H0,transcript)-H(H0)-H(Z,H0,transcript), with the same source masses. -/
noncomputable def conditionalJointInfo (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) : ℝ :=
  entropy p.initialJoint.mass +
    (∑ h0, (bank.map (fun h => entropyTerm (∑ z, conditionalStoppedMass p n h0 z h))).sum) -
    entropy p.initialRecord.mass -
    ∑ h0, ∑ z, (bank.map (fun h => entropyTerm (conditionalStoppedMass p n h0 z h))).sum

/-- A normalized conditional stopped law, constructed from the actual finite laws. -/
noncomputable def conditionalStoppedJointLaw (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    FiniteLaw (H0 × (Z × (historySet (A × Y) n))) where
  mass uh := p.initialRecord.mass uh.1 * (stoppedJointLaw (p.given uh.1) n).mass uh.2
  nonnegative uh := mul_nonneg (p.initialRecord.nonnegative uh.1)
    ((stoppedJointLaw (p.given uh.1) n).nonnegative uh.2)
  total := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ u, ∑ zh : Z × (historySet (A × Y) n),
          p.initialRecord.mass u * (stoppedJointLaw (p.given u) n).mass zh) =
          ∑ u, p.initialRecord.mass u := by
        apply Finset.sum_congr rfl
        intro u _
        rw [← Finset.mul_sum, (stoppedJointLaw (p.given u) n).total, mul_one]
      _ = 1 := p.initialRecord.total

theorem conditionalStoppedJointLaw_source (p : ConditionalProtocol H0 Z A Y) (n : ℕ)
    (u : H0) (z : Z) (h : historySet (A × Y) n) :
    (conditionalStoppedJointLaw p n).mass (u, (z, h)) =
      conditionalStoppedMass p n u z h.val := rfl

theorem conditionalStoppedMass_nonnegative (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (u : H0) (z : Z) (h : List (A × Y)) :
    0 ≤ conditionalStoppedMass p n u z h :=
  mul_nonneg (p.initialRecord.nonnegative u) (stoppedMass_nonnegative (p.given u) n z h)

/-- The retained stopped law has exactly the original initial-joint marginal. -/
theorem conditionalStoppedMass_target_marginal (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) (u : H0) (z : Z) :
    (bank.map (fun h => conditionalStoppedMass p n u z h)).sum = p.initialJoint.mass (u, z) := by
  rw [hb.sum_eq]
  simp only [conditionalStoppedMass]
  rw [← Finset.mul_sum, historySet_stoppedMass_target_marginal]
  exact (p.initial_joint u z).symm

theorem conditionalInitialRecord_marginal (p : ConditionalProtocol H0 Z A Y) (u : H0) :
    (∑ z, p.initialJoint.mass (u, z)) = p.initialRecord.mass u := by
  simp only [p.initial_joint]
  rw [← Finset.mul_sum, (p.given u).prior.total, mul_one]

/-- The initial record marginal is unchanged by any permitted finite protocol. -/
theorem conditionalStoppedMass_record_marginal (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) (u : H0) :
    (∑ z, (bank.map (fun h => conditionalStoppedMass p n u z h)).sum) =
      p.initialRecord.mass u := by
  simp only [conditionalStoppedMass_target_marginal p n bank hb]
  exact conditionalInitialRecord_marginal p u

theorem conditionalStoppedMass_total (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    (∑ u, ∑ z, (bank.map (fun h => conditionalStoppedMass p n u z h)).sum) = 1 := by
  simp only [conditionalStoppedMass_record_marginal p n bank hb]
  exact p.initialRecord.total

/-- A zero-mass initial record contributes no joint cells, information or cost. -/
theorem conditional_zero_record (p : ConditionalProtocol H0 Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (u : H0) (hu : p.initialRecord.mass u = 0) :
    (∀ z h, conditionalStoppedMass p n u z h = 0) ∧
      p.initialRecord.mass u * terminalMI (p.given u) n bank = 0 ∧
      p.initialRecord.mass u * expectedCost (p.given u) n bank = 0 := by
  simp [conditionalStoppedMass, hu]

/-- Initial entropy is derived from the actual joint prior, including zero H0 masses. -/
theorem conditionalInitial_entropy (p : ConditionalProtocol H0 Z A Y) :
    entropy p.initialJoint.mass = entropy p.initialRecord.mass +
      ∑ u, p.initialRecord.mass u * entropy (p.given u).prior.mass := by
  have hs : p.initialJoint.mass =
      (fun uz : H0 × Z => p.initialRecord.mass uz.1 * (p.given uz.1).prior.mass uz.2) := by
    funext uz
    exact p.initial_joint uz.1 uz.2
  rw [hs, entropy_joint_kernel p.initialRecord.mass
    (fun u z => (p.given u).prior.mass z) (fun u => (p.given u).prior.total)]

/-- The joint-law expression subtracts the actual stopped conditional entropy. -/
theorem conditionalJointInfo_eq_entropy_sub (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    conditionalJointInfo p n bank = entropy p.initialJoint.mass - entropy p.initialRecord.mass -
      ∑ u, ∑ h ∈ historySet (A × Y) n,
        massUncertainty (fun z => conditionalStoppedMass p n u z h) := by
  unfold conditionalJointInfo
  simp only [hb.sum_eq]
  have hex : (∑ u, ∑ z, ∑ h ∈ historySet (A × Y) n,
      entropyTerm (conditionalStoppedMass p n u z h)) =
      ∑ u, ∑ h ∈ historySet (A × Y) n, ∑ z,
        entropyTerm (conditionalStoppedMass p n u z h) := by
    apply Finset.sum_congr rfl
    intro u _
    exact Finset.sum_comm
  rw [hex]
  simp only [massUncertainty, entropy_eq_sum, Finset.sum_sub_distrib]
  ring

/-- Conditional information equals the H0-weighted actual information, not a stipulated gain. -/
theorem conditionalJointInfo_eq_conditionalMI (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    conditionalJointInfo p n bank = conditionalMI p n bank := by
  have hs (u : H0) :
      (∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => conditionalStoppedMass p n u z h)) =
        p.initialRecord.mass u *
          ∑ h ∈ historySet (A × Y) n, massUncertainty (fun z => stoppedMass (p.given u) n z h) := by
    simp only [conditionalStoppedMass, massUncertainty_scale, Finset.mul_sum]
  have ht (u : H0) := terminalMI_eq_entropy_sub (p.given u) n bank hb
  rw [conditionalJointInfo_eq_entropy_sub p n bank hb, conditionalInitial_entropy]
  simp only [hs]
  unfold conditionalMI
  simp only [ht, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The conditional entropy telescope retains the actual prior and policy for every H0. -/
theorem conditionalMI_eq_gain_sum (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    conditionalMI p n bank = ∑ u, p.initialRecord.mass u *
      (bank.map (fun h => if h.length < n ∧ (p.given u).stop h = false then
        historyMass (p.given u) h *
          ∑ a, ((p.given u).policy h).mass a * localGain (p.given u) h a else 0)).sum := by
  unfold conditionalMI
  apply Finset.sum_congr rfl
  intro u _
  rw [terminalMI_eq_gain_sum (p.given u) n bank hb]

theorem conditionalMI_nonnegative (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    0 ≤ conditionalMI p n bank :=
  Finset.sum_nonneg (fun u _ => mul_nonneg (p.initialRecord.nonnegative u)
    (terminalMI_nonnegative (p.given u) n bank hb))

theorem conditionalExpectedCost_nonnegative (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    0 ≤ conditionalExpectedCost p n bank :=
  Finset.sum_nonneg (fun u _ => mul_nonneg (p.initialRecord.nonnegative u)
    (expectedCost_nonnegative (p.given u) n bank hb))

/-- Positive H0 branches are bounded first; zero H0 branches vanish without an extra premise. -/
theorem conditionalMI_le_expectedCost (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) (κ : ℝ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ) :
    conditionalMI p n bank ≤ κ * conditionalExpectedCost p n bank := by
  unfold conditionalMI conditionalExpectedCost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rcases (p.initialRecord.nonnegative u).eq_or_lt with hu | hu
  · simp only [← hu, zero_mul, mul_zero, le_refl]
  · calc
      p.initialRecord.mass u * terminalMI (p.given u) n bank ≤
          p.initialRecord.mass u * (κ * expectedCost (p.given u) n bank) :=
        mul_le_mul_of_nonneg_left
          (terminalMI_le_expectedCost (p.given u) κ n bank hb (hc u hu)) hu.le
      _ = _ := by ring

/-- The finite conditional theorem couples law normalization, derived information and actual cost.
This theorem does not take a stopped-limit or entropy-telescope conclusion as a premise. -/
theorem conditionalJointInfo_bounds (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank) (κ : ℝ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ) :
    conditionalJointInfo p n bank = conditionalMI p n bank ∧
      (∑ u, ∑ z, (bank.map (fun h => conditionalStoppedMass p n u z h)).sum) = 1 ∧
      (∀ u, 0 < p.initialRecord.mass u →
        terminalMI (p.given u) n bank ≤ κ * expectedCost (p.given u) n bank) ∧
      0 ≤ conditionalJointInfo p n bank ∧
      conditionalJointInfo p n bank ≤ κ * conditionalExpectedCost p n bank := by
  have hi := conditionalJointInfo_eq_conditionalMI p n bank hb
  refine ⟨hi, conditionalStoppedMass_total p n bank hb, ?_, ?_, ?_⟩
  · intro u hu
    exact terminalMI_le_expectedCost (p.given u) κ n bank hb (hc u hu)
  · rw [hi]
    exact conditionalMI_nonnegative p n bank hb
  · rw [hi]
    exact conditionalMI_le_expectedCost p n bank hb κ hc

/-- Zero local capacity forces zero finite conditional acquisition, without dividing by kappa. -/
theorem conditionalJointInfo_zero_capacity (p : ConditionalProtocol H0 Z A Y)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) 0) :
    conditionalJointInfo p n bank = 0 := by
  rw [conditionalJointInfo_eq_conditionalMI p n bank hb]
  apply le_antisymm
  · simpa only [zero_mul] using conditionalMI_le_expectedCost p n bank hb 0 hc
  · exact conditionalMI_nonnegative p n bank hb

end ConditionalInformation

/-- A concrete normalized law witnesses nonempty protocol carriers. -/
def unitLaw : FiniteLaw Unit where
  mass _ := 1
  nonnegative _ := zero_le_one
  total := by simp

/-- A concrete constant-target protocol stops immediately and acquires no information. -/
def stoppedUnitProtocol : FiniteProtocol Unit Unit Unit where
  prior := unitLaw
  policy _ := unitLaw
  observation _ _ _ := unitLaw
  stop _ := true
  cost _ _ := 0
  cost_nonnegative _ _ := le_rfl

/-- A nonvacuous stopped-protocol control, for every complete finite history bank. -/
theorem stoppedUnitProtocol_zero_information_cost (n : ℕ)
    (bank : List (List (Unit × Unit))) (hb : HistoryBank n bank) :
    terminalMI stoppedUnitProtocol n bank = 0 ∧ expectedCost stoppedUnitProtocol n bank = 0 := by
  constructor
  · rw [terminalMI_eq_gain_sum stoppedUnitProtocol n bank hb]
    simp [stoppedUnitProtocol]
  · simp [expectedCost, stoppedUnitProtocol]

/-! ## Adaptive binary menus, with retained initial information -/

section BinaryMenus
variable {A H0 : Type} [Fintype A] [Fintype H0]

/-- Each permitted reading has a signed bias bounded at every retained history. -/
structure BinaryMenu (p : FiniteProtocol Bool A Bool) (ε : ℝ) where
  bias : List (A × Bool) → A → ℝ
  bound : ∀ h a, |bias h a| ≤ ε
  source : ∀ h a z y, (p.observation h a z).mass y = binaryKernel (bias h a) z y
  reading_cost : ∀ h a, 1 ≤ p.cost h a

/-- A reachable binary posterior is the prior determined by its true mass. -/
theorem posterior_eq_binaryPrior (p : FiniteProtocol Bool A Bool)
    (h : List (A × Bool)) (hw : 0 < historyMass p h) :
    posterior p h = binaryPrior (posterior p h true) := by
  have hp := posterior_total p h hw
  simp only [Fintype.sum_bool] at hp
  funext b
  cases b
  · change posterior p h false = 1 - posterior p h true
    linarith
  · rfl

/-- The local gain is the mutual information of the actual posterior and actual reading. -/
theorem binaryMenu_localGain (p : FiniteProtocol Bool A Bool) (ε : ℝ)
    (menu : BinaryMenu p ε) (h : List (A × Bool)) (a : A)
    (hw : 0 < historyMass p h) :
    localGain p h a = jointMI (binaryJoint (posterior p h true) (menu.bias h a)) := by
  unfold localGain binaryJoint
  rw [posterior_eq_binaryPrior p h hw]
  simp only [menu.source, binaryPrior, if_true]

/-- Every active reading obeys the all-prior capacity bound at its own posterior. -/
theorem binaryMenu_capacity (p : FiniteProtocol Bool A Bool) (ε : ℝ)
    (menu : BinaryMenu p ε) (hε : ε ≤ 1 / 2) : LocalCapacityBound p (4 * ε ^ 2) := by
  intro h a hw _ _
  rw [binaryMenu_localGain p ε menu h a hw]
  calc
    jointMI (binaryJoint (posterior p h true) (menu.bias h a)) ≤ 4 * ε ^ 2 :=
      binaryJoint_information_le_envelope _ _ ε (menu.bound h a) hε
    _ ≤ (4 * ε ^ 2) * p.cost h a := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (menu.reading_cost h a) (by positivity : 0 ≤ 4 * ε ^ 2)

/-- The adaptive finite bound uses the stopped law and the sum of paid reading costs. -/
theorem binaryMenu_information_bound (p : FiniteProtocol Bool A Bool) (ε : ℝ)
    (menu : BinaryMenu p ε) (hε : ε ≤ 1 / 2) (n : ℕ)
    (bank : List (List (A × Bool))) (hb : HistoryBank n bank) :
    0 ≤ terminalMI p n bank ∧ terminalMI p n bank ≤ 4 * ε ^ 2 * expectedCost p n bank :=
  ⟨terminalMI_nonnegative p n bank hb,
    terminalMI_le_expectedCost p _ n bank hb (binaryMenu_capacity p ε menu hε)⟩

/-- Acquiring c bits in this menu requires the stated expected number of paid readings. -/
theorem binaryMenu_cost_lower_bound (p : FiniteProtocol Bool A Bool) (ε c : ℝ)
    (menu : BinaryMenu p ε) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (n : ℕ)
    (bank : List (List (A × Bool))) (hb : HistoryBank n bank)
    (hc : c ≤ terminalMI p n bank) : c / (4 * ε ^ 2) ≤ expectedCost p n bank := by
  apply (div_le_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  simpa only [mul_comm] using hc.trans
    (binaryMenu_information_bound p ε menu hε n bank hb).2

/-- Conditioning on H0 removes prior information before any reading is charged. -/
theorem conditional_binaryMenu_bound (p : ConditionalProtocol H0 Bool A Bool) (ε : ℝ)
    (menu : ∀ u, 0 < p.initialRecord.mass u → BinaryMenu (p.given u) ε)
    (hε : ε ≤ 1 / 2) (n : ℕ) (bank : List (List (A × Bool)))
    (hb : HistoryBank n bank) :
    0 ≤ conditionalJointInfo p n bank ∧
      conditionalJointInfo p n bank ≤ 4 * ε ^ 2 * conditionalExpectedCost p n bank := by
  have hi := conditionalJointInfo_bounds p n bank hb (4 * ε ^ 2)
    (fun u hu => binaryMenu_capacity (p.given u) ε (menu u hu) hε)
  exact ⟨hi.2.2.2.1, hi.2.2.2.2⟩

/-- The conditional reading bound applies to the same retained initial joint law. -/
theorem conditional_binaryMenu_cost_lower_bound (p : ConditionalProtocol H0 Bool A Bool)
    (ε c : ℝ) (menu : ∀ u, 0 < p.initialRecord.mass u → BinaryMenu (p.given u) ε)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (n : ℕ) (bank : List (List (A × Bool)))
    (hb : HistoryBank n bank) (hc : c ≤ conditionalJointInfo p n bank) :
    c / (4 * ε ^ 2) ≤ conditionalExpectedCost p n bank := by
  apply (div_le_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  simpa only [mul_comm] using hc.trans
    (conditional_binaryMenu_bound p ε menu hε n bank hb).2

/-- The zero-signal endpoint supplies no new information, with arbitrary initial records. -/
theorem conditional_binaryMenu_zero_signal (p : ConditionalProtocol H0 Bool A Bool)
    (menu : ∀ u, 0 < p.initialRecord.mass u → BinaryMenu (p.given u) 0)
    (n : ℕ) (bank : List (List (A × Bool))) (hb : HistoryBank n bank) :
    conditionalJointInfo p n bank = 0 := by
  obtain ⟨hn, hu⟩ := conditional_binaryMenu_bound p 0 menu (by norm_num) n bank hb
  norm_num at hu
  exact le_antisymm hu hn

/-! ### Binary menus at every bias bound

The kernels of a binary menu are probability rows, so every bias lies in `[-1/2, 1/2]`. A menu
at a bias bound `ε` is then a menu at `min ε (1/2)`, and `4 (min ε (1/2))^2 ≤ 4 ε^2`, so the
bounds above hold with no hypothesis `ε ≤ 1/2`. -/

/-- Both outcomes of a reading of a binary menu have nonnegative mass, so its bias has absolute
value at most one half. -/
theorem BinaryMenu.abs_bias_le_half {p : FiniteProtocol Bool A Bool} {ε : ℝ}
    (menu : BinaryMenu p ε) (h : List (A × Bool)) (a : A) : |menu.bias h a| ≤ 1 / 2 := by
  have h1 := (p.observation h a true).nonnegative true
  have h2 := (p.observation h a true).nonnegative false
  rw [menu.source] at h1 h2
  simp only [binaryKernel] at h1 h2
  norm_num at h1 h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A binary menu at bias bound `ε` is a binary menu at `min ε (1/2)`, with the same biases,
kernels and costs. -/
def BinaryMenu.minHalf {p : FiniteProtocol Bool A Bool} {ε : ℝ}
    (menu : BinaryMenu p ε) : BinaryMenu p (min ε (1 / 2)) where
  bias := menu.bias
  bound h a := le_min (menu.bound h a) (menu.abs_bias_le_half h a)
  source := menu.source
  reading_cost := menu.reading_cost

/-- The capacity of the clipped bias bound is at most the capacity of the bias bound. -/
theorem four_min_half_sq_le (ε : ℝ) : 4 * min ε (1 / 2) ^ 2 ≤ 4 * ε ^ 2 := by
  rcases le_total ε (1 / 2) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    nlinarith

/-- Every active reading obeys the all-prior capacity bound `4 ε²` at every bias bound `ε`. -/
theorem binaryMenu_capacity_general (p : FiniteProtocol Bool A Bool) (ε : ℝ)
    (menu : BinaryMenu p ε) : LocalCapacityBound p (4 * ε ^ 2) := by
  intro h a hw hs ha
  exact (binaryMenu_capacity p (min ε (1 / 2)) menu.minHalf (min_le_right _ _) h a hw hs ha).trans
    (mul_le_mul_of_nonneg_right (four_min_half_sq_le ε) (p.cost_nonnegative h a))

/-- The conditional binary-menu bound at every bias bound `ε`. -/
theorem conditional_binaryMenu_bound_general (p : ConditionalProtocol H0 Bool A Bool) (ε : ℝ)
    (menu : ∀ u, 0 < p.initialRecord.mass u → BinaryMenu (p.given u) ε) (n : ℕ)
    (bank : List (List (A × Bool))) (hb : HistoryBank n bank) :
    0 ≤ conditionalJointInfo p n bank ∧
      conditionalJointInfo p n bank ≤ 4 * ε ^ 2 * conditionalExpectedCost p n bank := by
  have hi := conditionalJointInfo_bounds p n bank hb (4 * ε ^ 2)
    (fun u hu => binaryMenu_capacity_general (p.given u) ε (menu u hu))
  exact ⟨hi.2.2.2.1, hi.2.2.2.2⟩

/-- The conditional reading-cost lower bound at every positive bias bound `ε`. -/
theorem conditional_binaryMenu_cost_lower_bound_general
    (p : ConditionalProtocol H0 Bool A Bool) (ε c : ℝ)
    (menu : ∀ u, 0 < p.initialRecord.mass u → BinaryMenu (p.given u) ε)
    (hε0 : 0 < ε) (n : ℕ) (bank : List (List (A × Bool)))
    (hb : HistoryBank n bank) (hc : c ≤ conditionalJointInfo p n bank) :
    c / (4 * ε ^ 2) ≤ conditionalExpectedCost p n bank := by
  apply (div_le_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  simpa only [mul_comm] using hc.trans
    (conditional_binaryMenu_bound_general p ε menu n bank hb).2

end BinaryMenus

/-! ## Source laws under changes of names -/

/-- Relabel a complete history without deleting actions, outcomes or its length. -/
def historyEquiv {A B Y V : Type} (ea : A ≃ B) (ey : Y ≃ V) :
    List (A × Y) ≃ List (B × V) where
  toFun h := h.map (ea.prodCongr ey)
  invFun h := h.map (ea.symm.prodCongr ey.symm)
  left_inv h := by
    induction h with
    | nil => rfl
    | cons ay h ih =>
      obtain ⟨a, y⟩ := ay
      simpa using congrArg (List.cons (a, y)) ih
  right_inv h := by
    induction h with
    | nil => rfl
    | cons ay h ih =>
      obtain ⟨a, y⟩ := ay
      simpa using congrArg (List.cons (a, y)) ih

theorem historyEquiv_length {A B Y V : Type} (ea : A ≃ B) (ey : Y ≃ V)
    (h : List (A × Y)) : (historyEquiv ea ey h).length = h.length := List.length_map _

/-- The hypotheses compare primitive source probabilities and cost, before information is derived. -/
structure FiniteProtocolIso {Z A Y Z' A' Y' : Type}
    [Fintype Z] [Fintype A] [Fintype Y] [Fintype Z'] [Fintype A'] [Fintype Y']
    (p : FiniteProtocol Z A Y) (q : FiniteProtocol Z' A' Y') where
  input : Z ≃ Z'
  action : A ≃ A'
  outcome : Y ≃ Y'
  prior : ∀ z, q.prior.mass (input z) = p.prior.mass z
  policy : ∀ h a, (q.policy (historyEquiv action outcome h)).mass (action a) = (p.policy h).mass a
  observation : ∀ h a z y,
    (q.observation (historyEquiv action outcome h) (action a) (input z)).mass (outcome y) =
      (p.observation h a z).mass y
  stopping : ∀ h, q.stop (historyEquiv action outcome h) = p.stop h
  cost : ∀ h a, q.cost (historyEquiv action outcome h) (action a) = p.cost h a

/-- Entropy equality is derived from the relabeled source weights. -/
theorem entropy_reindex {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : X → ℝ) (q : Y → ℝ) (h : ∀ x, q (e x) = p x) :
    entropy q = entropy p := by
  unfold entropy BitDivision.entropy
  congr 1
  calc
    (∑ y, Real.negMulLog (q y)) = ∑ x, Real.negMulLog (q (e x)) := (e.sum_comp _).symm
    _ = _ := Finset.sum_congr rfl (fun x _ => congrArg Real.negMulLog (h x))

/-- The input and outcome marginals are transported with their common joint law. -/
theorem jointMI_reindex {X Y U V : Type}
    [Fintype X] [Fintype Y] [Fintype U] [Fintype V]
    (ex : X ≃ U) (ey : Y ≃ V) (p : X × Y → ℝ) (q : U × V → ℝ)
    (h : ∀ x y, q (ex x, ey y) = p (x, y)) : jointMI q = jointMI p := by
  have hx (x : X) : (∑ v, q (ex x, v)) = ∑ y, p (x, y) := by
    rw [← ey.sum_comp (fun v => q (ex x, v))]
    exact Finset.sum_congr rfl (fun y _ => h x y)
  have hy (y : Y) : (∑ u, q (u, ey y)) = ∑ x, p (x, y) := by
    rw [← ex.sum_comp (fun u => q (u, ey y))]
    exact Finset.sum_congr rfl (fun x _ => h x y)
  unfold jointMI
  rw [entropy_reindex ex _ _ hx, entropy_reindex ey _ _ hy,
    entropy_reindex (ex.prodCongr ey) p q (fun xy => h xy.1 xy.2)]

namespace FiniteProtocolIso
variable {Z A Y Z' A' Y' : Type}
variable [Fintype Z] [Fintype A] [Fintype Y] [Fintype Z'] [Fintype A'] [Fintype Y']
variable {p : FiniteProtocol Z A Y} {q : FiniteProtocol Z' A' Y'}

/-- Every prefix cell is the product of corresponding primitive source cells. -/
theorem prefixMass_transport (e : FiniteProtocolIso p q) (z : Z) (h : List (A × Y)) :
    prefixMass q (e.input z) (historyEquiv e.action e.outcome h) = prefixMass p z h := by
  induction h using List.reverseRecOn with
  | nil => exact e.prior z
  | append_singleton h ay ih =>
    obtain ⟨a, y⟩ := ay
    change prefixMass q (e.input z)
      ((h ++ [(a, y)]).map (e.action.prodCongr e.outcome)) = _
    rw [List.map_append, List.map_singleton]
    change prefixMass q (e.input z)
      (historyEquiv e.action e.outcome h ++ [(e.action a, e.outcome y)]) = _
    rw [prefixMass_append, prefixMass_append, e.stopping, e.policy, e.observation, ih]

/-- The probability of each retained history is kept. -/
theorem historyMass_transport (e : FiniteProtocolIso p q) (h : List (A × Y)) :
    historyMass q (historyEquiv e.action e.outcome h) = historyMass p h := by
  unfold historyMass
  rw [← e.input.sum_comp (fun z => prefixMass q z (historyEquiv e.action e.outcome h))]
  exact Finset.sum_congr rfl (fun z _ => e.prefixMass_transport z h)

/-- Stopping depends on the retained history, so stopped cells are transported as well. -/
theorem stoppedMass_transport (e : FiniteProtocolIso p q) (n : ℕ) (z : Z)
    (h : List (A × Y)) :
    stoppedMass q n (e.input z) (historyEquiv e.action e.outcome h) = stoppedMass p n z h := by
  simp only [stoppedMass, historyEquiv_length, e.stopping, e.prefixMass_transport]

/-- The bounded history carriers have an inverse on the actual retained lists. -/
def stoppedHistoryEquiv (e : FiniteProtocolIso p q) (n : ℕ) :
    (historySet (A × Y) n) ≃ (historySet (A' × Y') n) where
  toFun h := ⟨historyEquiv e.action e.outcome h.val,
    (mem_historySet n _).mpr (by simpa only [historyEquiv_length] using
      (mem_historySet n h.val).mp h.property)⟩
  invFun h := ⟨(historyEquiv e.action e.outcome).symm h.val,
    (mem_historySet n _).mpr (by
      change (h.val.map (e.action.symm.prodCongr e.outcome.symm)).length ≤ n
      simpa only [List.length_map] using (mem_historySet n h.val).mp h.property)⟩
  left_inv h := Subtype.ext ((historyEquiv e.action e.outcome).symm_apply_apply h.val)
  right_inv h := Subtype.ext ((historyEquiv e.action e.outcome).apply_symm_apply h.val)

/-- Information equality follows from the actual stopped joint law. -/
theorem terminalMI_transport (e : FiniteProtocolIso p q) (n : ℕ)
    (bank : List (List (A × Y))) (bank' : List (List (A' × Y')))
    (hb : HistoryBank n bank) (hb' : HistoryBank n bank') :
    terminalMI q n bank' = terminalMI p n bank := by
  rw [terminalMI_eq_jointMI q n bank' hb', terminalMI_eq_jointMI p n bank hb]
  apply jointMI_reindex e.input (e.stoppedHistoryEquiv n)
  intro z h
  exact e.stoppedMass_transport n z h.val

/-- Any final source loss, including error or refusal, can be integrated against these cells. -/
noncomputable def stoppedExpectation (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (loss : Z → List (A × Y) → ℝ) : ℝ :=
  ∑ z, (bank.map (fun h => stoppedMass p n z h * loss z h)).sum

/-- Every source-linked terminal loss has the same expected value after relabeling. -/
theorem stoppedExpectation_transport (e : FiniteProtocolIso p q) (n : ℕ)
    (bank : List (List (A × Y))) (loss : Z → List (A × Y) → ℝ)
    (loss' : Z' → List (A' × Y') → ℝ)
    (hl : ∀ z h, loss' (e.input z) (historyEquiv e.action e.outcome h) = loss z h) :
    stoppedExpectation q n (bank.map (historyEquiv e.action e.outcome)) loss' =
      stoppedExpectation p n bank loss := by
  unfold stoppedExpectation
  rw [← e.input.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  simp only [List.map_map, Function.comp_def, e.stoppedMass_transport, hl]

/-- The expected paid cost is kept without replacing it by an information bound. -/
theorem expectedCost_transport (e : FiniteProtocolIso p q) (n : ℕ)
    (bank : List (List (A × Y))) :
    expectedCost q n (bank.map (historyEquiv e.action e.outcome)) = expectedCost p n bank := by
  have hs (h : List (A × Y)) :
      (∑ a', (q.policy (historyEquiv e.action e.outcome h)).mass a' *
        q.cost (historyEquiv e.action e.outcome h) a') =
      ∑ a, (p.policy h).mass a * p.cost h a := by
    rw [← e.action.sum_comp]
    simp only [e.policy, e.cost]
  unfold expectedCost
  simp only [List.map_map, Function.comp_def, historyEquiv_length, e.stopping,
    e.historyMass_transport, hs]

end FiniteProtocolIso

/-! ## Increasing finite observations and their law-defined limits

Graph node M3_2. Each finite value is computed from the source stopped law.
No convergence or information-balance conclusion is supplied as a premise.
-/

/-- Entropy is nonnegative on masses in the unit interval. -/
theorem entropy_nonnegative_of_bounds {Z : Type} [Fintype Z] (m : Z → ℝ)
    (hm0 : ∀ z, 0 ≤ m z) (hm1 : ∀ z, m z ≤ 1) : 0 ≤ entropy m := by
  rw [entropy_eq_sum]
  apply Finset.sum_nonneg
  intro z _
  exact div_nonneg (Real.negMulLog_nonneg (hm0 z) (hm1 z))
    (Real.log_pos one_lt_two).le

/-- Each cell of a finite law is at most its total mass. -/
theorem FiniteLaw.mass_le_one {Z : Type} [Fintype Z] (p : FiniteLaw Z) (z : Z) :
    p.mass z ≤ 1 := by
  calc
    p.mass z ≤ ∑ x, p.mass x :=
      Finset.single_le_sum (fun x _ => p.nonnegative x) (Finset.mem_univ z)
    _ = 1 := p.total

/-- A normalized finite law has nonnegative entropy. -/
theorem FiniteLaw.entropy_nonnegative {Z : Type} [Fintype Z] (p : FiniteLaw Z) :
    0 ≤ entropy p.mass :=
  entropy_nonnegative_of_bounds p.mass p.nonnegative p.mass_le_one

section IncreasingInformation
variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

/-- Zero histories have zero posterior; positive histories have a normalized posterior. -/
theorem posterior_le_one (p : FiniteProtocol Z A Y) (h : List (A × Y)) (z : Z) :
    posterior p h z ≤ 1 := by
  rcases (historyMass_nonnegative p h).eq_or_lt with hw | hw
  · simp only [posterior, ← hw, div_zero, zero_le_one]
  · calc
      posterior p h z ≤ ∑ x, posterior p h x :=
        Finset.single_le_sum (fun x _ => posterior_nonnegative p h x) (Finset.mem_univ z)
      _ = 1 := posterior_total p h hw

/-- The uncertainty carried by each reachable history is nonnegative. -/
theorem historyUncertainty_nonnegative (p : FiniteProtocol Z A Y) (h : List (A × Y)) :
    0 ≤ historyUncertainty p h := by
  unfold historyUncertainty
  rw [massUncertainty_prefix]
  exact mul_nonneg (historyMass_nonnegative p h)
    (entropy_nonnegative_of_bounds _ (posterior_nonnegative p h) (posterior_le_one p h))

/-- Stopped conditional uncertainty is nonnegative, including absent cells. -/
theorem stoppedUncertainty_nonnegative (p : FiniteProtocol Z A Y) (n : ℕ)
    (h : List (A × Y)) :
    0 ≤ massUncertainty (fun z => stoppedMass p n z h) := by
  rw [massUncertainty_stopped]
  unfold boundaryValue
  split_ifs
  · exact historyUncertainty_nonnegative p h
  · exact le_rfl

/-- A finite experiment cannot acquire more information than its initial target entropy. -/
theorem terminalMI_le_prior_entropy (p : FiniteProtocol Z A Y) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank) :
    terminalMI p n bank ≤ entropy p.prior.mass := by
  rw [terminalMI_eq_entropy_sub p n bank hb]
  exact sub_le_self _ (Finset.sum_nonneg (fun h _ => stoppedUncertainty_nonnegative p n h))

end IncreasingInformation

/-- An active charge is zero outside the retained pre-stop histories. -/
theorem activeValue_nonnegative {E : Type} (stop : List E → Bool) (n : ℕ)
    (f : List E → ℝ) (hf : ∀ h, 0 ≤ f h) (h : List E) :
    0 ≤ activeValue stop n f h := by
  unfold activeValue
  split_ifs
  · exact hf h
  · exact le_rfl

/-- Increasing the horizon adds only nonnegative source charges. -/
theorem historySet_active_sum_mono {E : Type} [Fintype E]
    (stop : List E → Bool) (f : List E → ℝ) (hf : ∀ h, 0 ≤ f h) :
    Monotone (fun n => ∑ h ∈ historySet E n, activeValue stop n f h) := by
  intro n m hnm
  calc
    (∑ h ∈ historySet E n, activeValue stop n f h) ≤
        ∑ h ∈ historySet E n, activeValue stop m f h := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hh : h.length < n ∧ stop h = false
      · have hm : h.length < m ∧ stop h = false :=
          ⟨Nat.lt_of_lt_of_le hh.1 hnm, hh.2⟩
        simp only [activeValue, if_pos hh, if_pos hm, le_refl]
      · rw [activeValue, if_neg hh]
        exact activeValue_nonnegative stop m f hf h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (historySet_mono hnm)
      (fun h _ _ => activeValue_nonnegative stop m f hf h)

section IncreasingProtocol
variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

/-- Information increases with the finite retained transcript, without any cost assumption. -/
theorem terminalMI_mono (p : FiniteProtocol Z A Y) :
    Monotone (fun n => terminalMI p n (historyBank A Y n)) := by
  intro n m hnm
  change terminalMI p n (historyBank A Y n) ≤ terminalMI p m (historyBank A Y m)
  rw [terminalMI_eq_gain_sum p n _ (historyBank_complete A Y n),
    terminalMI_eq_gain_sum p m _ (historyBank_complete A Y m),
    (historyBank_complete A Y n).sum_eq, (historyBank_complete A Y m).sum_eq]
  exact historySet_active_sum_mono p.stop
    (fun h => historyMass p h * ∑ a, (p.policy h).mass a * localGain p h a)
    (fun h => mul_nonneg (historyMass_nonnegative p h) (Finset.sum_nonneg
      (fun a _ => mul_nonneg ((p.policy h).nonnegative a) (localGain_nonnegative p h a)))) hnm

/-- Paid cost increases with the horizon; stopping contributes no later charge. -/
theorem expectedCost_mono (p : FiniteProtocol Z A Y) :
    Monotone (fun n => expectedCost p n (historyBank A Y n)) := by
  intro n m hnm
  change expectedCost p n (historyBank A Y n) ≤ expectedCost p m (historyBank A Y m)
  unfold expectedCost
  rw [(historyBank_complete A Y n).sum_eq, (historyBank_complete A Y m).sum_eq]
  exact historySet_active_sum_mono p.stop
    (fun h => historyMass p h * ∑ a, (p.policy h).mass a * p.cost h a)
    (fun h => mul_nonneg (historyMass_nonnegative p h) (Finset.sum_nonneg
      (fun a _ => mul_nonneg ((p.policy h).nonnegative a) (p.cost_nonnegative h a)))) hnm

end IncreasingProtocol

section ProtocolLimits
open Filter
open scoped Topology ENNReal
variable {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]

/-- The information of all finite retained prefixes of this source protocol. -/
noncomputable def informationLimit (p : FiniteProtocol Z A Y) : ℝ :=
  ⨆ n, terminalMI p n (historyBank A Y n)

/-- The prior entropy bounds the actual finite information values. -/
theorem finiteInformation_bddAbove (p : FiniteProtocol Z A Y) :
    BddAbove (Set.range (fun n => terminalMI p n (historyBank A Y n))) := by
  refine ⟨entropy p.prior.mass, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact terminalMI_le_prior_entropy p n _ (historyBank_complete A Y n)

theorem terminalMI_le_informationLimit (p : FiniteProtocol Z A Y) (n : ℕ) :
    terminalMI p n (historyBank A Y n) ≤ informationLimit p :=
  le_ciSup (finiteInformation_bddAbove p) n

theorem informationLimit_nonnegative (p : FiniteProtocol Z A Y) :
    0 ≤ informationLimit p :=
  (terminalMI_nonnegative p 0 _ (historyBank_complete A Y 0)).trans
    (terminalMI_le_informationLimit p 0)

theorem informationLimit_le_prior_entropy (p : FiniteProtocol Z A Y) :
    informationLimit p ≤ entropy p.prior.mass :=
  ciSup_le (fun n => terminalMI_le_prior_entropy p n _ (historyBank_complete A Y n))

/-- Convergence follows from the source law and its entropy telescope. -/
theorem terminalMI_tendsto_informationLimit (p : FiniteProtocol Z A Y) :
    Tendsto (fun n => terminalMI p n (historyBank A Y n)) atTop (𝓝 (informationLimit p)) :=
  tendsto_atTop_ciSup (terminalMI_mono p) (finiteInformation_bddAbove p)

/-- Infinite expected cost is retained as infinity. -/
noncomputable def extendedCost (p : FiniteProtocol Z A Y) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (expectedCost p n (historyBank A Y n))

theorem finiteCost_le_extendedCost (p : FiniteProtocol Z A Y) (n : ℕ) :
    ENNReal.ofReal (expectedCost p n (historyBank A Y n)) ≤ extendedCost p :=
  le_iSup (fun n => ENNReal.ofReal (expectedCost p n (historyBank A Y n))) n

theorem finiteCost_tendsto_extendedCost (p : FiniteProtocol Z A Y) :
    Tendsto (fun n => ENNReal.ofReal (expectedCost p n (historyBank A Y n)))
      atTop (𝓝 (extendedCost p)) :=
  tendsto_atTop_iSup (fun _ _ h => ENNReal.ofReal_le_ofReal (expectedCost_mono p h))

/-- The infinite budget is bounded precisely when every finite paid budget is bounded. -/
theorem extendedCost_le_iff (p : FiniteProtocol Z A Y) (budget : ℝ) (hb : 0 ≤ budget) :
    extendedCost p ≤ ENNReal.ofReal budget ↔
      ∀ n, expectedCost p n (historyBank A Y n) ≤ budget := by
  simp only [extendedCost, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hb]

/-- The source-defined information limit obeys the capacity bound even at infinite cost. -/
theorem informationLimit_le_extendedCost (p : FiniteProtocol Z A Y) (κ : ℝ)
    (hk : 0 ≤ κ) (hc : LocalCapacityBound p κ) :
    ENNReal.ofReal (informationLimit p) ≤ ENNReal.ofReal κ * extendedCost p := by
  apply le_of_tendsto' (ENNReal.tendsto_ofReal (terminalMI_tendsto_informationLimit p))
  intro n
  calc
    ENNReal.ofReal (terminalMI p n (historyBank A Y n)) ≤
        ENNReal.ofReal (κ * expectedCost p n (historyBank A Y n)) :=
      ENNReal.ofReal_le_ofReal (terminalMI_le_expectedCost p κ n _
        (historyBank_complete A Y n) hc)
    _ = ENNReal.ofReal κ * ENNReal.ofReal (expectedCost p n (historyBank A Y n)) :=
      ENNReal.ofReal_mul hk
    _ ≤ _ := mul_le_mul_left' (finiteCost_le_extendedCost p n) _

/-- A real budget gives the real lower bound without a finite-cost assumption on the protocol. -/
theorem informationLimit_le_budget (p : FiniteProtocol Z A Y) (κ budget : ℝ)
    (hk : 0 ≤ κ) (hb : 0 ≤ budget) (hc : LocalCapacityBound p κ)
    (hcost : extendedCost p ≤ ENNReal.ofReal budget) : informationLimit p ≤ κ * budget := by
  apply ciSup_le
  intro n
  exact (terminalMI_le_expectedCost p κ n _ (historyBank_complete A Y n) hc).trans
    (mul_le_mul_of_nonneg_left ((extendedCost_le_iff p budget hb).mp hcost n) hk)

/-- Zero capacity gives zero acquired information even if total cost is infinite. -/
theorem informationLimit_zero_capacity (p : FiniteProtocol Z A Y)
    (hc : LocalCapacityBound p 0) : informationLimit p = 0 := by
  apply le_antisymm _ (informationLimit_nonnegative p)
  apply ciSup_le
  intro n
  simpa only [zero_mul] using terminalMI_le_expectedCost p 0 n _
    (historyBank_complete A Y n) hc

/-- A finite history's paid charge uses its actual probability, policy and stopping decision. -/
noncomputable def historyCost (p : FiniteProtocol Z A Y) (h : List (A × Y)) : ℝ :=
  if p.stop h = false then historyMass p h * ∑ a, (p.policy h).mass a * p.cost h a else 0

theorem historyCost_nonnegative (p : FiniteProtocol Z A Y) (h : List (A × Y)) :
    0 ≤ historyCost p h := by
  unfold historyCost
  split_ifs
  · exact mul_nonneg (historyMass_nonnegative p h)
      (Finset.sum_nonneg (fun a _ => mul_nonneg ((p.policy h).nonnegative a)
        (p.cost_nonnegative h a)))
  · exact le_rfl

/-- The histories charged before a finite horizon. -/
noncomputable def chargedHistorySet (A Y : Type) [Fintype A] [Fintype Y]
    (n : ℕ) : Finset (List (A × Y)) :=
  (historySet (A × Y) n).filter (fun h => h.length < n)

theorem mem_chargedHistorySet (n : ℕ) (h : List (A × Y)) :
    h ∈ chargedHistorySet A Y n ↔ h.length < n := by
  simp only [chargedHistorySet, Finset.mem_filter, mem_historySet]
  exact ⟨And.right, fun hh => ⟨hh.le, hh⟩⟩

/-- These finite sets eventually contain every finite collection of histories. -/
theorem chargedHistorySet_cofinal (s : Finset (List (A × Y))) :
    ∃ n, s ⊆ chargedHistorySet A Y n := by
  refine ⟨s.sup List.length + 1, ?_⟩
  intro h hh
  exact (mem_chargedHistorySet _ h).mpr
    (Nat.lt_succ_of_le (Finset.le_sup (f := List.length) hh))

theorem expectedCost_eq_historyCost (p : FiniteProtocol Z A Y) (n : ℕ) :
    expectedCost p n (historyBank A Y n) =
      ∑ h ∈ chargedHistorySet A Y n, historyCost p h := by
  unfold expectedCost
  rw [(historyBank_complete A Y n).sum_eq]
  simp only [chargedHistorySet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hl : h.length < n <;> by_cases hs : p.stop h = false <;>
    simp [hl, hs, historyCost]

/-- The extended cost is the nonnegative sum of all source-history charges. -/
theorem extendedCost_eq_tsum_historyCost (p : FiniteProtocol Z A Y) :
    extendedCost p = ∑' h : List (A × Y), ENNReal.ofReal (historyCost p h) := by
  rw [ENNReal.tsum_eq_iSup_sum' (chargedHistorySet A Y) chargedHistorySet_cofinal]
  unfold extendedCost
  congr 1
  funext n
  rw [expectedCost_eq_historyCost, ENNReal.ofReal_sum_of_nonneg]
  intro h _
  exact historyCost_nonnegative p h

end ProtocolLimits

section ConditionalProtocolLimits
open Filter
open scoped Topology ENNReal
variable {H0 Z A Y : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- Initial information is excluded before taking the limit in each conditional experiment. -/
noncomputable def conditionalInformationLimit (p : ConditionalProtocol H0 Z A Y) : ℝ :=
  ∑ u, p.initialRecord.mass u * informationLimit (p.given u)

/-- The same initial-record law weights all extended cost coordinates. -/
noncomputable def conditionalExtendedCost (p : ConditionalProtocol H0 Z A Y) : ℝ≥0∞ :=
  ∑ u, ENNReal.ofReal (p.initialRecord.mass u) * extendedCost (p.given u)

theorem conditionalInformationLimit_nonnegative (p : ConditionalProtocol H0 Z A Y) :
    0 ≤ conditionalInformationLimit p :=
  Finset.sum_nonneg (fun u _ => mul_nonneg (p.initialRecord.nonnegative u)
    (informationLimit_nonnegative (p.given u)))

/-- The actual conditional joint entropy converges to the weighted conditional limit. -/
theorem conditionalJointInfo_tendsto (p : ConditionalProtocol H0 Z A Y) :
    Tendsto (fun n => conditionalJointInfo p n (historyBank A Y n)) atTop
      (𝓝 (conditionalInformationLimit p)) := by
  have h (n : ℕ) := conditionalJointInfo_eq_conditionalMI p n _
    (historyBank_complete A Y n)
  simp_rw [h, conditionalMI]
  exact tendsto_finset_sum _ (fun u _ =>
    tendsto_const_nhds.mul (terminalMI_tendsto_informationLimit (p.given u)))

/-- Prior conditional entropy bounds all information acquired after H0. -/
theorem conditionalInformationLimit_le_initial_entropy (p : ConditionalProtocol H0 Z A Y) :
    conditionalInformationLimit p ≤
      entropy p.initialJoint.mass - entropy p.initialRecord.mass := by
  rw [conditionalInitial_entropy]
  simp only [add_sub_cancel_left]
  apply Finset.sum_le_sum
  intro u _
  exact mul_le_mul_of_nonneg_left (informationLimit_le_prior_entropy (p.given u))
    (p.initialRecord.nonnegative u)

/-- Every finite conditional cost is bounded by the sum of the extended conditional costs. -/
theorem conditionalFiniteCost_le_extendedCost (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    ENNReal.ofReal (conditionalExpectedCost p n (historyBank A Y n)) ≤
      conditionalExtendedCost p := by
  rw [conditionalExpectedCost, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_le_sum
    intro u _
    rw [ENNReal.ofReal_mul (p.initialRecord.nonnegative u)]
    exact mul_le_mul_left' (finiteCost_le_extendedCost (p.given u) n) _
  · intro u _
    exact mul_nonneg (p.initialRecord.nonnegative u)
      (expectedCost_nonnegative (p.given u) n _ (historyBank_complete A Y n))

/-- The stopped bound survives the limit with arbitrary initial side information and infinite cost. -/
theorem conditionalInformationLimit_le_extendedCost (p : ConditionalProtocol H0 Z A Y)
    (κ : ℝ) (hk : 0 ≤ κ)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ) :
    ENNReal.ofReal (conditionalInformationLimit p) ≤
      ENNReal.ofReal κ * conditionalExtendedCost p := by
  apply le_of_tendsto' (ENNReal.tendsto_ofReal (conditionalJointInfo_tendsto p))
  intro n
  have hh := (conditionalJointInfo_bounds p n _ (historyBank_complete A Y n) κ hc).2.2.2.2
  calc
    ENNReal.ofReal (conditionalJointInfo p n (historyBank A Y n)) ≤
        ENNReal.ofReal (κ * conditionalExpectedCost p n (historyBank A Y n)) :=
      ENNReal.ofReal_le_ofReal hh
    _ = ENNReal.ofReal κ * ENNReal.ofReal (conditionalExpectedCost p n (historyBank A Y n)) :=
      ENNReal.ofReal_mul hk
    _ ≤ _ := mul_le_mul_left' (conditionalFiniteCost_le_extendedCost p n) _

/-- A finite budget bounds the conditional information limit in real units. -/
theorem conditionalInformationLimit_le_budget (p : ConditionalProtocol H0 Z A Y)
    (κ budget : ℝ) (hk : 0 ≤ κ) (hb : 0 ≤ budget)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) κ)
    (hcost : conditionalExtendedCost p ≤ ENNReal.ofReal budget) :
    conditionalInformationLimit p ≤ κ * budget := by
  apply le_of_tendsto' (conditionalJointInfo_tendsto p)
  intro n
  have hfinite : conditionalExpectedCost p n (historyBank A Y n) ≤ budget :=
    (ENNReal.ofReal_le_ofReal_iff hb).mp
      ((conditionalFiniteCost_le_extendedCost p n).trans hcost)
  exact ((conditionalJointInfo_bounds p n _ (historyBank_complete A Y n) κ hc).2.2.2.2).trans
    (mul_le_mul_of_nonneg_left hfinite hk)

/-- A zero-capacity menu remains uninformative after an unbounded conditional experiment. -/
theorem conditionalInformationLimit_zero_capacity (p : ConditionalProtocol H0 Z A Y)
    (hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) 0) :
    conditionalInformationLimit p = 0 := by
  apply le_antisymm _ (conditionalInformationLimit_nonnegative p)
  apply le_of_tendsto' (conditionalJointInfo_tendsto p)
  intro n
  exact (conditionalJointInfo_zero_capacity p n _ (historyBank_complete A Y n) hc).le

/-- Finite conditional cost is the sum of the same weighted, nonnegative branch costs. -/
theorem conditionalFiniteCost_eq_weighted (p : ConditionalProtocol H0 Z A Y) (n : ℕ) :
    ENNReal.ofReal (conditionalExpectedCost p n (historyBank A Y n)) =
      ∑ u, ENNReal.ofReal (p.initialRecord.mass u) *
        ENNReal.ofReal (expectedCost (p.given u) n (historyBank A Y n)) := by
  rw [conditionalExpectedCost, ENNReal.ofReal_sum_of_nonneg]
  · exact Finset.sum_congr rfl (fun u _ => ENNReal.ofReal_mul (p.initialRecord.nonnegative u))
  · intro u _
    exact mul_nonneg (p.initialRecord.nonnegative u)
      (expectedCost_nonnegative (p.given u) n _ (historyBank_complete A Y n))

/-- Conditional cost converges in the extended nonnegative reals, including infinite branches. -/
theorem conditionalFiniteCost_tendsto (p : ConditionalProtocol H0 Z A Y) :
    Tendsto (fun n => ENNReal.ofReal (conditionalExpectedCost p n (historyBank A Y n)))
      atTop (𝓝 (conditionalExtendedCost p)) := by
  simp_rw [conditionalFiniteCost_eq_weighted]
  exact tendsto_finset_sum _ (fun u _ =>
    ENNReal.Tendsto.const_mul (finiteCost_tendsto_extendedCost (p.given u))
      (Or.inr ENNReal.ofReal_ne_top))

/-- Conditional cost sums the actual charges at every retained history and initial record. -/
theorem conditionalExtendedCost_eq_history_charges (p : ConditionalProtocol H0 Z A Y) :
    conditionalExtendedCost p =
      ∑ u, ENNReal.ofReal (p.initialRecord.mass u) *
        ∑' h : List (A × Y), ENNReal.ofReal (historyCost (p.given u) h) := by
  simp only [conditionalExtendedCost, extendedCost_eq_tsum_historyCost]

/-- The weak-signal estimate holds after taking every finite horizon. -/
theorem conditional_binaryMenu_limit_bound (p : ConditionalProtocol H0 Bool A Bool)
    (ε : ℝ) (menu : ∀ u, 0 < p.initialRecord.mass u → BinaryMenu (p.given u) ε)
    (hε : ε ≤ 1 / 2) :
    ENNReal.ofReal (conditionalInformationLimit p) ≤
      ENNReal.ofReal (4 * ε ^ 2) * conditionalExtendedCost p :=
  conditionalInformationLimit_le_extendedCost p (4 * ε ^ 2) (by positivity)
    (fun u hu => binaryMenu_capacity (p.given u) ε (menu u hu) hε)

/-- Every finite budget for the source protocol has the same inverse-square lower bound. -/
theorem conditional_binaryMenu_limit_cost_lower (p : ConditionalProtocol H0 Bool A Bool)
    (ε c budget : ℝ) (menu : ∀ u, 0 < p.initialRecord.mass u → BinaryMenu (p.given u) ε)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hb : 0 ≤ budget)
    (hc : c ≤ conditionalInformationLimit p)
    (hcost : conditionalExtendedCost p ≤ ENNReal.ofReal budget) :
    c / (4 * ε ^ 2) ≤ budget := by
  apply (div_le_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  simpa only [mul_comm] using hc.trans
    (conditionalInformationLimit_le_budget p (4 * ε ^ 2) budget (by positivity) hb
      (fun u hu => binaryMenu_capacity (p.given u) ε (menu u hu) hε) hcost)

/-- At zero signal every finite prefix and its limit has zero conditional acquisition. -/
theorem conditional_binaryMenu_limit_zero_signal (p : ConditionalProtocol H0 Bool A Bool)
    (menu : ∀ u, 0 < p.initialRecord.mass u → BinaryMenu (p.given u) 0) :
    conditionalInformationLimit p = 0 := by
  apply conditionalInformationLimit_zero_capacity
  intro u hu
  simpa using binaryMenu_capacity (p.given u) 0 (menu u hu) (by norm_num)

end ConditionalProtocolLimits

/-! ## Specification goals of M3.1, M3.2 and M3.3

Each goal is copied from UniversalObservationSpec.lean, namespace Protocol, and proved from the
source laws of this module. -/

/-- The acquisition inequality refers to the actual stopped law and actual cost. -/
def FiniteProtocolInformationGoal : Prop :=
  ∀ (Z A Y : Type) [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) (κ : ℝ) (n : ℕ) (bank : List (List (A × Y))),
    0 ≤ κ → HistoryBank n bank → LocalCapacityBound p κ →
    terminalMI p n bank ≤ κ * expectedCost p n bank

theorem finiteProtocolInformationGoal : FiniteProtocolInformationGoal := by
  intro Z A Y _ _ _ p κ n bank _ hb hc
  exact terminalMI_le_expectedCost p κ n bank hb hc

/-- Normalization of the stopped law is not assumed in the information goal. -/
def StoppedNormalizationGoal : Prop :=
  ∀ (Z A Y : Type) [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) (n : ℕ) (bank : List (List (A × Y))),
    HistoryBank n bank → (∑ z, (bank.map (fun h => stoppedMass p n z h)).sum) = 1

theorem stoppedNormalizationGoal : StoppedNormalizationGoal := by
  intro Z A Y _ _ _ p n bank hb
  exact stoppedMass_total p n bank hb

/-- Gain/cost assembly is separate from proving a real protocol supplies these terms. -/
def FiniteCostGoal : Prop :=
  ∀ (n : ℕ) (gain cost : Fin n → ℝ) (κ target : ℝ),
    (∀ t, gain t ≤ κ * cost t) → target ≤ ∑ t, gain t →
      target ≤ κ * ∑ t, cost t

theorem finiteCostGoal : FiniteCostGoal := by
  intro n gain cost κ target hg ht
  rw [Finset.mul_sum]
  exact ht.trans (Finset.sum_le_sum (fun t _ => hg t))

/-- Stopped limits require both convergence and a proved finite-prefix inequality. -/
def StoppedCostGoal : Prop :=
  ∀ (g c : ℕ → ℝ) (G C κ : ℝ),
    Filter.Tendsto g Filter.atTop (nhds G) →
    Filter.Tendsto c Filter.atTop (nhds C) →
    (∀ n, g n ≤ κ * c n) → G ≤ κ * C

theorem stoppedCostGoal : StoppedCostGoal := by
  intro g c G C κ hg hc hle
  exact le_of_tendsto_of_tendsto' hg (hc.const_mul κ) hle

def BinaryCapacityGoal : Prop :=
  ∀ (ε prior : ℝ), 0 ≤ ε → ε ≤ 1/2 → 0 ≤ prior → prior ≤ 1 →
    jointMI (fun by_ : Bool × Bool =>
      (if by_.1 then prior else 1-prior) * binaryKernel ε by_.1 by_.2) ≤ 4 * ε^2

theorem binaryCapacityGoal : BinaryCapacityGoal := by
  intro ε prior hε0 hε _ _
  exact binaryJoint_information_le_quadratic prior ε (by rw [abs_of_nonneg hε0]; exact hε)

/-- Initial information is excluded; positive-mass branches are bounded before averaging. -/
def ConditionalInformationGoal : Prop :=
  ∀ (H0 Z A Y : Type) [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Z A Y) (n : ℕ) (bank : List (List (A × Y))),
    HistoryBank n bank →
    conditionalJointInfo p n bank = conditionalMI p n bank ∧
    (∑ h0, ∑ z, (bank.map (fun h => conditionalStoppedMass p n h0 z h)).sum) = 1 ∧
    ∀ κ : ℝ, 0 ≤ κ →
      (∀ h0, 0 < p.initialRecord.mass h0 → LocalCapacityBound (p.given h0) κ) →
      (∀ h0, 0 < p.initialRecord.mass h0 →
        terminalMI (p.given h0) n bank ≤ κ * expectedCost (p.given h0) n bank) ∧
      conditionalMI p n bank ≤ κ * conditionalExpectedCost p n bank

theorem conditionalInformationGoal : ConditionalInformationGoal := by
  intro H0 Z A Y _ _ _ _ p n bank hb
  refine ⟨conditionalJointInfo_eq_conditionalMI p n bank hb,
    conditionalStoppedMass_total p n bank hb, fun κ _ hc => ⟨fun u hu => ?_,
      conditionalMI_le_expectedCost p n bank hb κ hc⟩⟩
  exact terminalMI_le_expectedCost (p.given u) κ n bank hb (hc u hu)

/-! ## M3.5: the feasible protocol, readout and repair frontier

Graph node M3_5. A task fixes the initial record law, the target prior of every record, the
instrument kernels, the permitted actions, the target readout, the licensed repairs and every cost
coordinate. A strategy chooses a policy and a stopping rule for every initial record and one repair
witness. Feasibility at a requirement is the existence of an admissible strategy whose actual
stopped law meets the stated information, error and refusal levels and whose expected cost meets
the budget in every coordinate. No minimum cost and no feasibility flag is supplied as data: both
are computed from the family. Cost coordinates stay a vector and carry no conversion into heat.
-/

/-- A finite law carried along an equivalence of its carrier. -/
def FiniteLaw.reindex {B C : Type} [Fintype B] [Fintype C] (e : B ≃ C) (p : FiniteLaw B) :
    FiniteLaw C where
  mass c := p.mass (e.symm c)
  nonnegative c := p.nonnegative (e.symm c)
  total := (e.symm.sum_comp p.mass).trans p.total

theorem FiniteLaw.reindex_mass {B C : Type} [Fintype B] [Fintype C] (e : B ≃ C)
    (p : FiniteLaw B) (b : B) : (p.reindex e).mass (e b) = p.mass b := by
  change p.mass (e.symm (e b)) = p.mass b
  rw [Equiv.symm_apply_apply]

/-- The identity relabeling of histories is the identity. -/
theorem historyEquiv_refl {A Y : Type} (h : List (A × Y)) :
    historyEquiv (Equiv.refl A) (Equiv.refl Y) h = h := by
  induction h with
  | nil => rfl
  | cons ay h ih => exact congrArg (List.cons ay) ih

/-- Composite relabelings of histories compose. -/
theorem historyEquiv_trans {A B C Y U W : Type} (ea : A ≃ B) (eb : B ≃ C) (ey : Y ≃ U)
    (eu : U ≃ W) (h : List (A × Y)) :
    historyEquiv (ea.trans eb) (ey.trans eu) h = historyEquiv eb eu (historyEquiv ea ey h) := by
  induction h with
  | nil => rfl
  | cons ay h ih => exact congrArg (List.cons _) ih

/-- The inverse relabeling of histories undoes the relabeling. -/
theorem historyEquiv_apply_symm {A B Y U : Type} (ea : A ≃ B) (ey : Y ≃ U)
    (h : List (B × U)) : historyEquiv ea ey (historyEquiv ea.symm ey.symm h) = h :=
  (historyEquiv ea ey).apply_symm_apply h

/-- A relabeled complete bank is a complete bank. -/
theorem historyBank_map {A Y B U : Type} (ea : A ≃ B) (ey : Y ≃ U) {n : ℕ}
    {bank : List (List (A × Y))} (hb : HistoryBank n bank) :
    HistoryBank n (bank.map (historyEquiv ea ey)) := by
  refine ⟨List.Nodup.map (historyEquiv ea ey).injective hb.1, fun h => ?_⟩
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [historyEquiv_length]
    exact (hb.2 k).mp hk
  · intro hl
    refine ⟨(historyEquiv ea ey).symm h, (hb.2 _).mpr ?_,
      (historyEquiv ea ey).apply_symm_apply h⟩
    rw [← historyEquiv_length ea ey, Equiv.apply_symm_apply]
    exact hl

/-- Two complete banks of one horizon give the same finite sum. -/
theorem HistoryBank.sum_bank {A Y : Type} [Fintype A] [Fintype Y] {n : ℕ}
    {bank bank' : List (List (A × Y))} (hb : HistoryBank n bank) (hb' : HistoryBank n bank')
    (f : List (A × Y) → ℝ) : (bank.map f).sum = (bank'.map f).sum :=
  (hb.sum_eq f).trans (hb'.sum_eq f).symm

theorem expectedCost_bank {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) {n : ℕ} {bank bank' : List (List (A × Y))}
    (hb : HistoryBank n bank) (hb' : HistoryBank n bank') :
    expectedCost p n bank = expectedCost p n bank' := by
  unfold expectedCost
  exact hb.sum_bank hb' _

theorem stoppedExpectation_bank {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) {n : ℕ} {bank bank' : List (List (A × Y))}
    (hb : HistoryBank n bank) (hb' : HistoryBank n bank') (loss : Z → List (A × Y) → ℝ) :
    FiniteProtocolIso.stoppedExpectation p n bank loss =
      FiniteProtocolIso.stoppedExpectation p n bank' loss := by
  unfold FiniteProtocolIso.stoppedExpectation
  exact Finset.sum_congr rfl (fun z _ => hb.sum_bank hb' _)

/-- The complete bank of horizon zero holds only the empty history. -/
theorem historyBank_zero_sum {A Y : Type} [Fintype A] [Fintype Y] (f : List (A × Y) → ℝ) :
    ((historyBank A Y 0).map f).sum = f [] := by
  rw [(historyBank_complete A Y 0).sum_eq]
  exact Finset.sum_singleton f []

theorem stoppedMass_zero_nil {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) (z : Z) : stoppedMass p 0 z [] = p.prior.mass z := by
  simp [stoppedMass, prefixMass_nil]

/-- At horizon zero the stopped expectation is the prior expectation at the empty history. -/
theorem stoppedExpectation_zero {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) (loss : Z → List (A × Y) → ℝ) :
    FiniteProtocolIso.stoppedExpectation p 0 (historyBank A Y 0) loss =
      ∑ z, p.prior.mass z * loss z [] := by
  unfold FiniteProtocolIso.stoppedExpectation
  exact Finset.sum_congr rfl (fun z _ => by rw [historyBank_zero_sum, stoppedMass_zero_nil])

theorem stoppedExpectation_const_zero {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) (n : ℕ) (bank : List (List (A × Y))) :
    FiniteProtocolIso.stoppedExpectation p n bank (fun _ _ => 0) = 0 := by
  simp [FiniteProtocolIso.stoppedExpectation]

/-- A unit loss integrates to the total stopped mass, which is one. -/
theorem stoppedExpectation_const_one {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) {n : ℕ} {bank : List (List (A × Y))} (hb : HistoryBank n bank) :
    FiniteProtocolIso.stoppedExpectation p n bank (fun _ _ => 1) = 1 := by
  unfold FiniteProtocolIso.stoppedExpectation
  simp only [mul_one]
  exact stoppedMass_total p n bank hb

/-- No active history lies before horizon zero, so nothing is paid. -/
theorem expectedCost_horizon_zero {Z A Y : Type} [Fintype Z] [Fintype A] [Fintype Y]
    (p : FiniteProtocol Z A Y) : expectedCost p 0 (historyBank A Y 0) = 0 := by
  unfold expectedCost
  rw [historyBank_zero_sum]
  simp

/-- A source-bound acquisition task with a vector of cost coordinates indexed by `ι`.
`readout r u h` is the answer that the repair witness `r` reports from the initial record `u` and
the retained history `h`; `none` is a refusal. -/
structure ProtocolTask (H0 Z A Y V R ι : Type) [Fintype H0] [Fintype Z] [Fintype A]
    [Fintype Y] where
  initialRecord : FiniteLaw H0
  prior : H0 → FiniteLaw Z
  observation : H0 → List (A × Y) → A → Z → FiniteLaw Y
  permitted : H0 → List (A × Y) → A → Prop
  target : H0 → Z → V
  licensed : R → Prop
  readout : R → H0 → List (A × Y) → Option V
  cost : ι → H0 → List (A × Y) → A → ℝ
  cost_nonnegative : ∀ j u h a, 0 ≤ cost j u h a

/-- A policy and a stopping rule for every initial record, and one repair witness.
Both rules read only the record and the retained history. -/
structure ProtocolStrategy (H0 A Y R : Type) [Fintype A] where
  policy : H0 → List (A × Y) → FiniteLaw A
  stop : H0 → List (A × Y) → Bool
  repair : R

/-- The stated levels: information at least `information`, error and refusal masses at most the
stated values, and expected cost at most `budget j` in every coordinate `j`. -/
structure ProtocolRequirement (ι : Type) where
  information : ℝ
  error : ℝ
  refusal : ℝ
  budget : ι → ℝ

/-- The requirement with its cost coordinates renamed. -/
def ProtocolRequirement.reindex {ι ι' : Type} (ec : ι ≃ ι') (q : ProtocolRequirement ι) :
    ProtocolRequirement ι' where
  information := q.information
  error := q.error
  refusal := q.refusal
  budget j := q.budget (ec.symm j)

theorem ProtocolRequirement.reindex_symm {ι ι' : Type} (ec : ι ≃ ι')
    (q : ProtocolRequirement ι) : (q.reindex ec).reindex ec.symm = q := by
  cases q
  simp only [ProtocolRequirement.reindex, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem ProtocolRequirement.symm_reindex {ι ι' : Type} (ec : ι ≃ ι')
    (q : ProtocolRequirement ι') : (q.reindex ec.symm).reindex ec = q := by
  cases q
  simp only [ProtocolRequirement.reindex, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- A reported answer different from the target; a refusal is not an error. -/
noncomputable def errorLoss {V : Type} (v : V) : Option V → ℝ
  | none => 0
  | some w => by classical exact if w = v then 0 else 1

/-- One unit of loss for a refusal. -/
def refusalLoss {V : Type} : Option V → ℝ
  | none => 1
  | some _ => 0

theorem errorLoss_map {V V' : Type} (e : V ≃ V') (v : V) (o : Option V) :
    errorLoss (e v) (o.map e) = errorLoss v o := by
  cases o with
  | none => rfl
  | some w =>
    classical
    show errorLoss (e v) (some (e w)) = errorLoss v (some w)
    simp only [errorLoss]
    rcases eq_or_ne w v with rfl | hw
    · rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (e.injective.ne hw), if_neg hw]

theorem refusalLoss_map {V V' : Type} (f : V → V') (o : Option V) :
    refusalLoss (o.map f) = refusalLoss o := by
  cases o <;> rfl

theorem option_map_refl {V : Type} (o : Option V) : o.map (Equiv.refl V) = o := by
  cases o <;> rfl

theorem option_map_symm_map {V V' : Type} (e : V ≃ V') (o : Option V) :
    (o.map e).map e.symm = o := by
  cases o with
  | none => rfl
  | some v => exact congrArg some (e.symm_apply_apply v)

namespace ProtocolTask
open scoped ENNReal
variable {H0 Z A Y V R ι : Type} [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]

/-- The actual initial joint law of record and target. -/
noncomputable def initialJoint (T : ProtocolTask H0 Z A Y V R ι) : FiniteLaw (H0 × Z) where
  mass uz := T.initialRecord.mass uz.1 * (T.prior uz.1).mass uz.2
  nonnegative uz := mul_nonneg (T.initialRecord.nonnegative uz.1)
    ((T.prior uz.1).nonnegative uz.2)
  total := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ u, ∑ z, T.initialRecord.mass u * (T.prior u).mass z) =
          ∑ u, T.initialRecord.mass u := by
        apply Finset.sum_congr rfl
        intro u _
        rw [← Finset.mul_sum, (T.prior u).total, mul_one]
      _ = 1 := T.initialRecord.total

/-- The finite protocol run at record `u` under strategy `σ`, charged by `c`. -/
noncomputable def protocol (T : ProtocolTask H0 Z A Y V R ι) (σ : ProtocolStrategy H0 A Y R)
    (u : H0) (c : List (A × Y) → A → ℝ) (hc : ∀ h a, 0 ≤ c h a) : FiniteProtocol Z A Y where
  prior := T.prior u
  policy := σ.policy u
  observation := T.observation u
  stop := σ.stop u
  cost := c
  cost_nonnegative := hc

/-- The conditional protocol of a strategy, with one charge for every record. -/
noncomputable def conditional (T : ProtocolTask H0 Z A Y V R ι) (σ : ProtocolStrategy H0 A Y R)
    (c : H0 → List (A × Y) → A → ℝ) (hc : ∀ u h a, 0 ≤ c u h a) :
    ConditionalProtocol H0 Z A Y where
  initialRecord := T.initialRecord
  initialJoint := T.initialJoint
  given u := T.protocol σ u (c u) (hc u)
  initial_joint _ _ := rfl

/-- The law of a strategy, with no charge. -/
noncomputable def lawConditional (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) : ConditionalProtocol H0 Z A Y :=
  T.conditional σ (fun _ _ _ => 0) (fun _ _ _ => le_rfl)

/-- The law of a strategy, charged in the cost coordinate `j`. -/
noncomputable def costConditional (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (j : ι) : ConditionalProtocol H0 Z A Y :=
  T.conditional σ (T.cost j) (T.cost_nonnegative j)

/-- Conditional information of the target given the initial record and the stopped transcript,
from the stopped joint law at horizon `n`. -/
noncomputable def information (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (n : ℕ) : ℝ :=
  conditionalJointInfo (T.lawConditional σ) n (historyBank A Y n)

/-- Expected cost in coordinate `j` at horizon `n`. -/
noncomputable def expectedCostAt (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (n : ℕ) (j : ι) : ℝ :=
  conditionalExpectedCost (T.costConditional σ j) n (historyBank A Y n)

/-- Stopped mass of a reported answer different from the target. -/
noncomputable def errorMass (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (n : ℕ) : ℝ :=
  ∑ u, T.initialRecord.mass u * FiniteProtocolIso.stoppedExpectation
    ((T.lawConditional σ).given u) n (historyBank A Y n)
    (fun z h => errorLoss (T.target u z) (T.readout σ.repair u h))

/-- Stopped mass of a refusal. -/
noncomputable def refusalMass (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (n : ℕ) : ℝ :=
  ∑ u, T.initialRecord.mass u * FiniteProtocolIso.stoppedExpectation
    ((T.lawConditional σ).given u) n (historyBank A Y n)
    (fun _ h => refusalLoss (T.readout σ.repair u h))

/-- The repair carries its license, and every action with positive policy mass at an active
history is permitted. -/
def Admissible (T : ProtocolTask H0 Z A Y V R ι) (σ : ProtocolStrategy H0 A Y R) : Prop :=
  T.licensed σ.repair ∧
    ∀ u h a, σ.stop u h = false → 0 < (σ.policy u h).mass a → T.permitted u h a

/-- The stopped law of `σ` at horizon `n` meets every level of `q`. -/
def Meets (T : ProtocolTask H0 Z A Y V R ι) (σ : ProtocolStrategy H0 A Y R) (n : ℕ)
    (q : ProtocolRequirement ι) : Prop :=
  q.information ≤ T.information σ n ∧ T.errorMass σ n ≤ q.error ∧
    T.refusalMass σ n ≤ q.refusal ∧ ∀ j, T.expectedCostAt σ n j ≤ q.budget j

/-- The actual membership criterion of the frontier. -/
def Feasible (T : ProtocolTask H0 Z A Y V R ι) (n : ℕ) (q : ProtocolRequirement ι) : Prop :=
  ∃ σ, T.Admissible σ ∧ T.Meets σ n q

/-- The feasible frontier at horizon `n`. -/
def frontier (T : ProtocolTask H0 Z A Y V R ι) (n : ℕ) : Set (ProtocolRequirement ι) :=
  {q | T.Feasible n q}

/-- An admissible strategy meeting the information, error and refusal levels of `q`. -/
def Qualifies (T : ProtocolTask H0 Z A Y V R ι) (σ : ProtocolStrategy H0 A Y R) (n : ℕ)
    (q : ProtocolRequirement ι) : Prop :=
  T.Admissible σ ∧ q.information ≤ T.information σ n ∧ T.errorMass σ n ≤ q.error ∧
    T.refusalMass σ n ≤ q.refusal

/-- Least expected cost in coordinate `j` over the qualifying strategies; infinity when none
qualifies. -/
noncomputable def minimumCost (T : ProtocolTask H0 Z A Y V R ι) (n : ℕ)
    (q : ProtocolRequirement ι) (j : ι) : ℝ≥0∞ :=
  ⨅ (σ : ProtocolStrategy H0 A Y R) (_ : T.Qualifies σ n q),
    ENNReal.ofReal (T.expectedCostAt σ n j)

theorem minimumCost_eq_top_iff (T : ProtocolTask H0 Z A Y V R ι) (n : ℕ)
    (q : ProtocolRequirement ι) (j : ι) :
    T.minimumCost n q j = ⊤ ↔ ∀ σ, ¬ T.Qualifies σ n q := by
  simp only [minimumCost, iInf₂_eq_top, ENNReal.ofReal_ne_top, imp_false]

theorem minimumCost_le_of_feasible (T : ProtocolTask H0 Z A Y V R ι) (n : ℕ)
    (q : ProtocolRequirement ι) (hq : T.Feasible n q) (j : ι) :
    T.minimumCost n q j ≤ ENNReal.ofReal (q.budget j) := by
  obtain ⟨σ, ha, hi, he, hr, hc⟩ := hq
  exact (iInf₂_le σ ⟨ha, hi, he, hr⟩).trans (ENNReal.ofReal_le_ofReal (hc j))

/-- Below the minimum there is no qualifying strategy; above it there is one. -/
theorem exists_lt_of_minimumCost_lt (T : ProtocolTask H0 Z A Y V R ι) (n : ℕ)
    (q : ProtocolRequirement ι) (j : ι) (b : ℝ)
    (hb : T.minimumCost n q j < ENNReal.ofReal b) :
    ∃ σ, T.Qualifies σ n q ∧ T.expectedCostAt σ n j < b := by
  obtain ⟨σ, hσ'⟩ := iInf_lt_iff.mp hb
  obtain ⟨hσ, hlt⟩ := iInf_lt_iff.mp hσ'
  exact ⟨σ, hσ, ((ENNReal.ofReal_lt_ofReal_iff').mp hlt).1⟩

theorem information_nonnegative (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (n : ℕ) : 0 ≤ T.information σ n := by
  unfold information
  rw [conditionalJointInfo_eq_conditionalMI _ n _ (historyBank_complete A Y n)]
  exact conditionalMI_nonnegative _ n _ (historyBank_complete A Y n)

/-- A strategy that refuses from every history makes no error. -/
theorem errorMass_eq_zero_of_refuses (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (n : ℕ) (hnone : ∀ u h, T.readout σ.repair u h = none) :
    T.errorMass σ n = 0 := by
  unfold errorMass
  simp only [hnone, errorLoss, stoppedExpectation_const_zero, mul_zero, Finset.sum_const_zero]

/-- A strategy that refuses from every history refuses with mass one. -/
theorem refusalMass_eq_one_of_refuses (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (n : ℕ) (hnone : ∀ u h, T.readout σ.repair u h = none) :
    T.refusalMass σ n = 1 := by
  unfold refusalMass
  simp only [hnone, refusalLoss, stoppedExpectation_const_one _ (historyBank_complete A Y n),
    mul_one]
  exact T.initialRecord.total

/-- A coordinate that charges nothing has zero expected cost. -/
theorem expectedCostAt_eq_zero_of_free (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (n : ℕ) (j : ι) (hfree : ∀ u h a, T.cost j u h a = 0) :
    T.expectedCostAt σ n j = 0 := by
  unfold expectedCostAt conditionalExpectedCost
  refine Finset.sum_eq_zero fun u _ => ?_
  have h0 : expectedCost ((T.costConditional σ j).given u) n (historyBank A Y n) = 0 := by
    unfold expectedCost
    rw [(historyBank_complete A Y n).sum_eq]
    refine Finset.sum_eq_zero fun h _ => ?_
    split_ifs
    · change historyMass _ h * ∑ a, _ * T.cost j u h a = 0
      simp only [hfree, mul_zero, Finset.sum_const_zero]
    · rfl
  rw [h0, mul_zero]

/-- The information does not read the cost coordinate. -/
theorem information_eq_cost (T : ProtocolTask H0 Z A Y V R ι) (σ : ProtocolStrategy H0 A Y R)
    (n : ℕ) (j : ι) :
    T.information σ n = conditionalJointInfo (T.costConditional σ j) n (historyBank A Y n) :=
  rfl

/-- Information acquired by the unbounded experiment, after the initial record. -/
noncomputable def informationLimitOf (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) : ℝ :=
  conditionalInformationLimit (T.lawConditional σ)

/-- Extended expected cost of the unbounded experiment in coordinate `j`. -/
noncomputable def extendedCostOf (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (j : ι) : ℝ≥0∞ :=
  conditionalExtendedCost (T.costConditional σ j)

theorem informationLimitOf_eq_cost (T : ProtocolTask H0 Z A Y V R ι)
    (σ : ProtocolStrategy H0 A Y R) (j : ι) :
    T.informationLimitOf σ = conditionalInformationLimit (T.costConditional σ j) := rfl

/-- Feasibility of the unbounded experiment: information limit at least `c` and extended cost
at most `budget j` in every coordinate; an infinite budget coordinate is permitted. -/
def LimitFeasible (T : ProtocolTask H0 Z A Y V R ι) (c : ℝ) (budget : ι → ℝ≥0∞) : Prop :=
  ∃ σ, T.Admissible σ ∧ c ≤ T.informationLimitOf σ ∧ ∀ j, T.extendedCostOf σ j ≤ budget j

/-- Least extended cost in coordinate `j` of an admissible unbounded experiment acquiring `c`. -/
noncomputable def limitMinimumCost (T : ProtocolTask H0 Z A Y V R ι) (c : ℝ) (j : ι) : ℝ≥0∞ :=
  ⨅ (σ : ProtocolStrategy H0 A Y R) (_ : T.Admissible σ ∧ c ≤ T.informationLimitOf σ),
    T.extendedCostOf σ j

end ProtocolTask

/-- A law-, license- and cost-preserving isomorphism of tasks. Every primitive is compared at
every record, history, action, target and outcome, including zero-mass ones. -/
structure TaskIso {H0 Z A Y V R ι H0' Z' A' Y' V' R' ι' : Type}
    [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]
    [Fintype H0'] [Fintype Z'] [Fintype A'] [Fintype Y']
    (S : ProtocolTask H0 Z A Y V R ι) (T : ProtocolTask H0' Z' A' Y' V' R' ι') where
  record : H0 ≃ H0'
  input : Z ≃ Z'
  action : A ≃ A'
  outcome : Y ≃ Y'
  answer : V ≃ V'
  repair : R ≃ R'
  coord : ι ≃ ι'
  initialRecord : ∀ u, T.initialRecord.mass (record u) = S.initialRecord.mass u
  prior : ∀ u z, (T.prior (record u)).mass (input z) = (S.prior u).mass z
  observation : ∀ u h a z y,
    (T.observation (record u) (historyEquiv action outcome h) (action a) (input z)).mass
      (outcome y) = (S.observation u h a z).mass y
  permitted : ∀ u h a,
    T.permitted (record u) (historyEquiv action outcome h) (action a) ↔ S.permitted u h a
  target : ∀ u z, T.target (record u) (input z) = answer (S.target u z)
  licensed : ∀ r, T.licensed (repair r) ↔ S.licensed r
  readout : ∀ r u h,
    T.readout (repair r) (record u) (historyEquiv action outcome h) =
      (S.readout r u h).map answer
  cost : ∀ j u h a,
    T.cost (coord j) (record u) (historyEquiv action outcome h) (action a) = S.cost j u h a

namespace FiniteProtocolIso
open scoped ENNReal
variable {Z A Y Z' A' Y' : Type}
variable [Fintype Z] [Fintype A] [Fintype Y] [Fintype Z'] [Fintype A'] [Fintype Y']
variable {p : FiniteProtocol Z A Y} {q : FiniteProtocol Z' A' Y'}

/-- The limit of the finite informations is transported term by term. -/
theorem informationLimit_transport (e : FiniteProtocolIso p q) :
    informationLimit q = informationLimit p := by
  unfold informationLimit
  exact iSup_congr fun n => e.terminalMI_transport n _ _
    (historyBank_complete A Y n) (historyBank_complete A' Y' n)

/-- The extended cost is transported term by term, including the value infinity. -/
theorem extendedCost_transport (e : FiniteProtocolIso p q) :
    extendedCost q = extendedCost p := by
  unfold extendedCost
  exact iSup_congr fun n => congrArg ENNReal.ofReal
    ((expectedCost_bank q (historyBank_complete A' Y' n)
      (historyBank_map e.action e.outcome (historyBank_complete A Y n))).trans
        (e.expectedCost_transport n _))

end FiniteProtocolIso

namespace TaskIso
open scoped ENNReal
variable {H0 Z A Y V R ι H0' Z' A' Y' V' R' ι' : Type}
variable [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]
variable [Fintype H0'] [Fintype Z'] [Fintype A'] [Fintype Y']
variable {S : ProtocolTask H0 Z A Y V R ι} {T : ProtocolTask H0' Z' A' Y' V' R' ι'}

/-- The translated strategy: policy, stopping rule and repair read through the inverse maps. -/
noncomputable def mapStrategy (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) :
    ProtocolStrategy H0' A' Y' R' where
  policy u h :=
    (σ.policy (e.record.symm u) ((historyEquiv e.action e.outcome).symm h)).reindex e.action
  stop u h := σ.stop (e.record.symm u) ((historyEquiv e.action e.outcome).symm h)
  repair := e.repair σ.repair

theorem mapStrategy_policy (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (u : H0)
    (h : List (A × Y)) (a : A) :
    ((e.mapStrategy σ).policy (e.record u) (historyEquiv e.action e.outcome h)).mass
      (e.action a) = (σ.policy u h).mass a := by
  change (σ.policy (e.record.symm (e.record u))
    ((historyEquiv e.action e.outcome).symm (historyEquiv e.action e.outcome h))).mass
      (e.action.symm (e.action a)) = _
  simp only [Equiv.symm_apply_apply]

theorem mapStrategy_stop (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (u : H0)
    (h : List (A × Y)) :
    (e.mapStrategy σ).stop (e.record u) (historyEquiv e.action e.outcome h) = σ.stop u h := by
  change σ.stop (e.record.symm (e.record u))
    ((historyEquiv e.action e.outcome).symm (historyEquiv e.action e.outcome h)) = _
  simp only [Equiv.symm_apply_apply]

/-- The record protocols of a strategy and of its translation are law isomorphic. -/
def protocolIso (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (u : H0)
    (c : List (A × Y) → A → ℝ) (hc : ∀ h a, 0 ≤ c h a)
    (c' : List (A' × Y') → A' → ℝ) (hc' : ∀ h a, 0 ≤ c' h a)
    (hcost : ∀ h a, c' (historyEquiv e.action e.outcome h) (e.action a) = c h a) :
    FiniteProtocolIso (S.protocol σ u c hc)
      (T.protocol (e.mapStrategy σ) (e.record u) c' hc') where
  input := e.input
  action := e.action
  outcome := e.outcome
  prior z := e.prior u z
  policy h a := e.mapStrategy_policy σ u h a
  observation h a z y := e.observation u h a z y
  stopping h := e.mapStrategy_stop σ u h
  cost h a := hcost h a

/-- The uncharged record protocols. -/
def lawIso (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (u : H0) :
    FiniteProtocolIso ((S.lawConditional σ).given u)
      ((T.lawConditional (e.mapStrategy σ)).given (e.record u)) :=
  e.protocolIso σ u (fun _ _ => 0) (fun _ _ => le_rfl) (fun _ _ => 0) (fun _ _ => le_rfl)
    (fun _ _ => rfl)

/-- The record protocols charged in a cost coordinate and in its image. -/
def costIso (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (j : ι) (u : H0) :
    FiniteProtocolIso ((S.costConditional σ j).given u)
      ((T.costConditional (e.mapStrategy σ) (e.coord j)).given (e.record u)) :=
  e.protocolIso σ u (S.cost j u) (S.cost_nonnegative j u) (T.cost (e.coord j) (e.record u))
    (T.cost_nonnegative (e.coord j) (e.record u)) (e.cost j u)

theorem information_transport (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (n : ℕ) :
    T.information (e.mapStrategy σ) n = S.information σ n := by
  unfold ProtocolTask.information
  rw [conditionalJointInfo_eq_conditionalMI _ n _ (historyBank_complete A' Y' n),
    conditionalJointInfo_eq_conditionalMI _ n _ (historyBank_complete A Y n)]
  unfold conditionalMI
  rw [← e.record.sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  exact congrArg₂ (· * ·) (e.initialRecord u)
    ((e.lawIso σ u).terminalMI_transport n _ _
      (historyBank_complete A Y n) (historyBank_complete A' Y' n))

theorem expectedCostAt_transport (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (n : ℕ)
    (j : ι) : T.expectedCostAt (e.mapStrategy σ) n (e.coord j) = S.expectedCostAt σ n j := by
  unfold ProtocolTask.expectedCostAt conditionalExpectedCost
  rw [← e.record.sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  refine congrArg₂ (· * ·) (e.initialRecord u) ?_
  rw [expectedCost_bank _ (historyBank_complete A' Y' n)
    (historyBank_map e.action e.outcome (historyBank_complete A Y n))]
  exact (e.costIso σ j u).expectedCost_transport n _

theorem errorMass_transport (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (n : ℕ) :
    T.errorMass (e.mapStrategy σ) n = S.errorMass σ n := by
  unfold ProtocolTask.errorMass
  rw [← e.record.sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  refine congrArg₂ (· * ·) (e.initialRecord u) ?_
  rw [stoppedExpectation_bank _ (historyBank_complete A' Y' n)
    (historyBank_map e.action e.outcome (historyBank_complete A Y n))]
  apply (e.lawIso σ u).stoppedExpectation_transport n _ _ _
  intro z h
  show errorLoss (T.target (e.record u) (e.input z))
      (T.readout (e.repair σ.repair) (e.record u) (historyEquiv e.action e.outcome h)) =
    errorLoss (S.target u z) (S.readout σ.repair u h)
  rw [e.target, e.readout]
  exact errorLoss_map e.answer _ _

theorem refusalMass_transport (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (n : ℕ) :
    T.refusalMass (e.mapStrategy σ) n = S.refusalMass σ n := by
  unfold ProtocolTask.refusalMass
  rw [← e.record.sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  refine congrArg₂ (· * ·) (e.initialRecord u) ?_
  rw [stoppedExpectation_bank _ (historyBank_complete A' Y' n)
    (historyBank_map e.action e.outcome (historyBank_complete A Y n))]
  apply (e.lawIso σ u).stoppedExpectation_transport n _ _ _
  intro z h
  show refusalLoss
      (T.readout (e.repair σ.repair) (e.record u) (historyEquiv e.action e.outcome h)) =
    refusalLoss (S.readout σ.repair u h)
  rw [e.readout]
  exact refusalLoss_map e.answer _

theorem admissible_transport (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) :
    T.Admissible (e.mapStrategy σ) ↔ S.Admissible σ := by
  unfold ProtocolTask.Admissible
  refine and_congr (e.licensed σ.repair) ⟨fun h u k a hs ha => ?_, fun h u' k' a' hs ha => ?_⟩
  · have hs' : (e.mapStrategy σ).stop (e.record u) (historyEquiv e.action e.outcome k) = false :=
      (e.mapStrategy_stop σ u k).trans hs
    have ha' : 0 < ((e.mapStrategy σ).policy (e.record u)
        (historyEquiv e.action e.outcome k)).mass (e.action a) :=
      (e.mapStrategy_policy σ u k a).symm ▸ ha
    exact (e.permitted u k a).mp (h _ _ _ hs' ha')
  · obtain ⟨u, rfl⟩ := e.record.surjective u'
    obtain ⟨k, rfl⟩ := (historyEquiv e.action e.outcome).surjective k'
    obtain ⟨a, rfl⟩ := e.action.surjective a'
    rw [e.mapStrategy_stop] at hs
    rw [e.mapStrategy_policy] at ha
    exact (e.permitted u k a).mpr (h u k a hs ha)

theorem meets_transport (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (n : ℕ)
    (q : ProtocolRequirement ι) :
    T.Meets (e.mapStrategy σ) n (q.reindex e.coord) ↔ S.Meets σ n q := by
  unfold ProtocolTask.Meets
  rw [e.information_transport, e.errorMass_transport, e.refusalMass_transport]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    ⟨fun h j => ?_, fun h j' => ?_⟩))
  · have k := h (e.coord j)
    rw [e.expectedCostAt_transport] at k
    simpa only [ProtocolRequirement.reindex, Equiv.symm_apply_apply] using k
  · obtain ⟨j, rfl⟩ := e.coord.surjective j'
    rw [e.expectedCostAt_transport]
    simpa only [ProtocolRequirement.reindex, Equiv.symm_apply_apply] using h j

theorem qualifies_transport (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (n : ℕ)
    (q : ProtocolRequirement ι) :
    T.Qualifies (e.mapStrategy σ) n (q.reindex e.coord) ↔ S.Qualifies σ n q := by
  unfold ProtocolTask.Qualifies
  rw [e.admissible_transport, e.information_transport, e.errorMass_transport,
    e.refusalMass_transport]
  rfl

/-- One direction of the frontier transport, at the renamed budget. -/
theorem feasible_transport (e : TaskIso S T) (n : ℕ) (q : ProtocolRequirement ι) :
    S.Feasible n q → T.Feasible n (q.reindex e.coord) := by
  rintro ⟨σ, ha, hm⟩
  exact ⟨e.mapStrategy σ, (e.admissible_transport σ).mpr ha, (e.meets_transport σ n q).mpr hm⟩

theorem informationLimitOf_transport (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) :
    T.informationLimitOf (e.mapStrategy σ) = S.informationLimitOf σ := by
  unfold ProtocolTask.informationLimitOf conditionalInformationLimit
  rw [← e.record.sum_comp]
  exact Finset.sum_congr rfl fun u _ => congrArg₂ (· * ·) (e.initialRecord u)
    (e.lawIso σ u).informationLimit_transport

theorem extendedCostOf_transport (e : TaskIso S T) (σ : ProtocolStrategy H0 A Y R) (j : ι) :
    T.extendedCostOf (e.mapStrategy σ) (e.coord j) = S.extendedCostOf σ j := by
  unfold ProtocolTask.extendedCostOf conditionalExtendedCost
  rw [← e.record.sum_comp]
  exact Finset.sum_congr rfl fun u _ => congrArg₂ (· * ·)
    (congrArg ENNReal.ofReal (e.initialRecord u)) (e.costIso σ j u).extendedCost_transport

/-- One direction of the unbounded transport, with a stated budget conversion. -/
theorem limitFeasible_transport (e : TaskIso S T) (c : ℝ) (b : ι → ℝ≥0∞) (b' : ι' → ℝ≥0∞)
    (hb : ∀ j, b' (e.coord j) = b j) : S.LimitFeasible c b → T.LimitFeasible c b' := by
  rintro ⟨σ, ha, hi, hc⟩
  refine ⟨e.mapStrategy σ, (e.admissible_transport σ).mpr ha,
    hi.trans_eq (e.informationLimitOf_transport σ).symm, fun j' => ?_⟩
  obtain ⟨j, rfl⟩ := e.coord.surjective j'
  rw [e.extendedCostOf_transport, hb]
  exact hc j

/-- The identity isomorphism. -/
def refl (S : ProtocolTask H0 Z A Y V R ι) : TaskIso S S where
  record := Equiv.refl H0
  input := Equiv.refl Z
  action := Equiv.refl A
  outcome := Equiv.refl Y
  answer := Equiv.refl V
  repair := Equiv.refl R
  coord := Equiv.refl ι
  initialRecord _ := rfl
  prior _ _ := rfl
  observation u h a z y := by
    show (S.observation u (historyEquiv (Equiv.refl A) (Equiv.refl Y) h) a z).mass y = _
    rw [historyEquiv_refl]
  permitted u h a := by
    show S.permitted u (historyEquiv (Equiv.refl A) (Equiv.refl Y) h) a ↔ _
    rw [historyEquiv_refl]
  target _ _ := rfl
  licensed _ := Iff.rfl
  readout r u h := by
    show S.readout r u (historyEquiv (Equiv.refl A) (Equiv.refl Y) h) = _
    rw [historyEquiv_refl, option_map_refl]
  cost j u h a := by
    show S.cost j u (historyEquiv (Equiv.refl A) (Equiv.refl Y) h) a = _
    rw [historyEquiv_refl]

/-- The inverse isomorphism. -/
def symm (e : TaskIso S T) : TaskIso T S where
  record := e.record.symm
  input := e.input.symm
  action := e.action.symm
  outcome := e.outcome.symm
  answer := e.answer.symm
  repair := e.repair.symm
  coord := e.coord.symm
  initialRecord u := by
    have k := e.initialRecord (e.record.symm u)
    simp only [Equiv.apply_symm_apply] at k
    exact k.symm
  prior u z := by
    have k := e.prior (e.record.symm u) (e.input.symm z)
    simp only [Equiv.apply_symm_apply] at k
    exact k.symm
  observation u h a z y := by
    have k := e.observation (e.record.symm u) (historyEquiv e.action.symm e.outcome.symm h)
      (e.action.symm a) (e.input.symm z) (e.outcome.symm y)
    simp only [historyEquiv_apply_symm, Equiv.apply_symm_apply] at k
    exact k.symm
  permitted u h a := by
    have k := e.permitted (e.record.symm u) (historyEquiv e.action.symm e.outcome.symm h)
      (e.action.symm a)
    simp only [historyEquiv_apply_symm, Equiv.apply_symm_apply] at k
    exact k.symm
  target u z := by
    have k := e.target (e.record.symm u) (e.input.symm z)
    simp only [Equiv.apply_symm_apply] at k
    rw [k, Equiv.symm_apply_apply]
  licensed r := by
    have k := e.licensed (e.repair.symm r)
    simp only [Equiv.apply_symm_apply] at k
    exact k.symm
  readout r u h := by
    have k := e.readout (e.repair.symm r) (e.record.symm u)
      (historyEquiv e.action.symm e.outcome.symm h)
    simp only [historyEquiv_apply_symm, Equiv.apply_symm_apply] at k
    rw [k, option_map_symm_map]
  cost j u h a := by
    have k := e.cost (e.coord.symm j) (e.record.symm u)
      (historyEquiv e.action.symm e.outcome.symm h) (e.action.symm a)
    simp only [historyEquiv_apply_symm, Equiv.apply_symm_apply] at k
    exact k.symm

/-- Composition of isomorphisms. -/
def trans {H0'' Z'' A'' Y'' V'' R'' ι'' : Type}
    [Fintype H0''] [Fintype Z''] [Fintype A''] [Fintype Y'']
    {W : ProtocolTask H0'' Z'' A'' Y'' V'' R'' ι''} (e : TaskIso S T) (f : TaskIso T W) :
    TaskIso S W where
  record := e.record.trans f.record
  input := e.input.trans f.input
  action := e.action.trans f.action
  outcome := e.outcome.trans f.outcome
  answer := e.answer.trans f.answer
  repair := e.repair.trans f.repair
  coord := e.coord.trans f.coord
  initialRecord u := (f.initialRecord (e.record u)).trans (e.initialRecord u)
  prior u z := (f.prior (e.record u) (e.input z)).trans (e.prior u z)
  observation u h a z y := by
    rw [historyEquiv_trans]
    exact (f.observation (e.record u) (historyEquiv e.action e.outcome h) (e.action a)
      (e.input z) (e.outcome y)).trans (e.observation u h a z y)
  permitted u h a := by
    rw [historyEquiv_trans]
    exact (f.permitted (e.record u) (historyEquiv e.action e.outcome h) (e.action a)).trans
      (e.permitted u h a)
  target u z := by
    show W.target (f.record (e.record u)) (f.input (e.input z)) =
      f.answer (e.answer (S.target u z))
    rw [f.target, e.target]
  licensed r := (f.licensed (e.repair r)).trans (e.licensed r)
  readout r u h := by
    rw [historyEquiv_trans]
    show W.readout (f.repair (e.repair r)) (f.record (e.record u))
        (historyEquiv f.action f.outcome (historyEquiv e.action e.outcome h)) =
      (S.readout r u h).map (e.answer.trans f.answer)
    rw [f.readout, e.readout, Option.map_map]
    rfl
  cost j u h a := by
    rw [historyEquiv_trans]
    exact (f.cost (e.coord j) (e.record u) (historyEquiv e.action e.outcome h)
      (e.action a)).trans (e.cost j u h a)

/-- Source feasibility at `q` is target feasibility at the renamed requirement. -/
theorem feasible_transport_iff (e : TaskIso S T) (n : ℕ) (q : ProtocolRequirement ι) :
    T.Feasible n (q.reindex e.coord) ↔ S.Feasible n q := by
  refine ⟨fun h => ?_, e.feasible_transport n q⟩
  have k := e.symm.feasible_transport n (q.reindex e.coord) h
  rwa [show e.symm.coord = e.coord.symm from rfl, ProtocolRequirement.reindex_symm] at k

/-- The whole frontier is transported, not one point of it. -/
theorem frontier_transport (e : TaskIso S T) (n : ℕ) :
    T.frontier n = ProtocolRequirement.reindex e.coord '' S.frontier n := by
  ext q'
  constructor
  · intro hq
    exact ⟨q'.reindex e.coord.symm, e.symm.feasible_transport n q' hq,
      ProtocolRequirement.symm_reindex e.coord q'⟩
  · rintro ⟨q, hq, rfl⟩
    exact e.feasible_transport n q hq

/-- The least cost is derived from the two family maps of the isomorphism. -/
theorem minimumCost_transport (e : TaskIso S T) (n : ℕ) (q : ProtocolRequirement ι) (j : ι) :
    T.minimumCost n (q.reindex e.coord) (e.coord j) = S.minimumCost n q j := by
  apply le_antisymm
  · apply le_iInf₂
    intro σ hσ
    calc
      T.minimumCost n (q.reindex e.coord) (e.coord j) ≤
          ENNReal.ofReal (T.expectedCostAt (e.mapStrategy σ) n (e.coord j)) :=
        iInf₂_le (e.mapStrategy σ) ((e.qualifies_transport σ n q).mpr hσ)
      _ = ENNReal.ofReal (S.expectedCostAt σ n j) := by rw [e.expectedCostAt_transport]
  · apply le_iInf₂
    intro τ hτ
    have hs : S.Qualifies (e.symm.mapStrategy τ) n q := by
      have k := (e.symm.qualifies_transport τ n (q.reindex e.coord)).mpr hτ
      rwa [show e.symm.coord = e.coord.symm from rfl,
        ProtocolRequirement.reindex_symm] at k
    have hc := e.symm.expectedCostAt_transport τ n (e.coord j)
    rw [show e.symm.coord (e.coord j) = j from e.coord.symm_apply_apply j] at hc
    calc
      S.minimumCost n q j ≤ ENNReal.ofReal (S.expectedCostAt (e.symm.mapStrategy τ) n j) :=
        iInf₂_le (e.symm.mapStrategy τ) hs
      _ = ENNReal.ofReal (T.expectedCostAt τ n (e.coord j)) := by rw [hc]

/-- Unbounded feasibility is transported in both directions. -/
theorem limitFeasible_transport_iff (e : TaskIso S T) (c : ℝ) (b : ι → ℝ≥0∞) :
    T.LimitFeasible c (fun j' => b (e.coord.symm j')) ↔ S.LimitFeasible c b :=
  ⟨e.symm.limitFeasible_transport c _ b (fun _ => rfl),
    e.limitFeasible_transport c b _ (fun j => congrArg b (e.coord.symm_apply_apply j))⟩

/-- The least extended cost of the unbounded experiment is transported, infinity included. -/
theorem limitMinimumCost_transport (e : TaskIso S T) (c : ℝ) (j : ι) :
    T.limitMinimumCost c (e.coord j) = S.limitMinimumCost c j := by
  apply le_antisymm
  · apply le_iInf₂
    intro σ hσ
    calc
      T.limitMinimumCost c (e.coord j) ≤ T.extendedCostOf (e.mapStrategy σ) (e.coord j) :=
        iInf₂_le (e.mapStrategy σ) ⟨(e.admissible_transport σ).mpr hσ.1,
          hσ.2.trans_eq (e.informationLimitOf_transport σ).symm⟩
      _ = S.extendedCostOf σ j := e.extendedCostOf_transport σ j
  · apply le_iInf₂
    intro τ hτ
    have hc := e.symm.extendedCostOf_transport τ (e.coord j)
    rw [show e.symm.coord (e.coord j) = j from e.coord.symm_apply_apply j] at hc
    calc
      S.limitMinimumCost c j ≤ S.extendedCostOf (e.symm.mapStrategy τ) j :=
        iInf₂_le (e.symm.mapStrategy τ) ⟨(e.symm.admissible_transport τ).mpr hτ.1,
          hτ.2.trans_eq (e.symm.informationLimitOf_transport τ).symm⟩
      _ = T.extendedCostOf τ (e.coord j) := hc

end TaskIso

/-- A one-way simulation of strategies. Each admissible source strategy is sent to an admissible
target strategy whose information, error and refusal are no worse and whose cost vector is at
most `convert` of the source cost vector, for a coordinatewise monotone `convert`. -/
structure TaskSimulation {H0 Z A Y V R ι H0' Z' A' Y' V' R' ι' : Type}
    [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]
    [Fintype H0'] [Fintype Z'] [Fintype A'] [Fintype Y']
    (S : ProtocolTask H0 Z A Y V R ι) (T : ProtocolTask H0' Z' A' Y' V' R' ι') (n : ℕ) where
  map : ProtocolStrategy H0 A Y R → ProtocolStrategy H0' A' Y' R'
  admissible : ∀ σ, S.Admissible σ → T.Admissible (map σ)
  information : ∀ σ, S.Admissible σ → S.information σ n ≤ T.information (map σ) n
  error : ∀ σ, S.Admissible σ → T.errorMass (map σ) n ≤ S.errorMass σ n
  refusal : ∀ σ, S.Admissible σ → T.refusalMass (map σ) n ≤ S.refusalMass σ n
  convert : (ι → ℝ) → ι' → ℝ
  convert_mono : ∀ b c : ι → ℝ, (∀ j, b j ≤ c j) → ∀ j', convert b j' ≤ convert c j'
  cost : ∀ σ, S.Admissible σ → ∀ j',
    T.expectedCostAt (map σ) n j' ≤ convert (fun j => S.expectedCostAt σ n j) j'

/-- A one-way simulation gives only the one-way feasibility implication. -/
theorem TaskSimulation.feasible {H0 Z A Y V R ι H0' Z' A' Y' V' R' ι' : Type}
    [Fintype H0] [Fintype Z] [Fintype A] [Fintype Y]
    [Fintype H0'] [Fintype Z'] [Fintype A'] [Fintype Y']
    {S : ProtocolTask H0 Z A Y V R ι} {T : ProtocolTask H0' Z' A' Y' V' R' ι'} {n : ℕ}
    (F : TaskSimulation S T n) (q : ProtocolRequirement ι) (hq : S.Feasible n q) :
    T.Feasible n ⟨q.information, q.error, q.refusal, F.convert q.budget⟩ := by
  obtain ⟨σ, ha, hi, he, hr, hc⟩ := hq
  exact ⟨F.map σ, F.admissible σ ha, hi.trans (F.information σ ha),
    (F.error σ ha).trans he, (F.refusal σ ha).trans hr,
    fun j' => (F.cost σ ha j').trans (F.convert_mono _ _ hc j')⟩

/-! ### The protocol-wide singularity as a property of the frontier -/

/-- Every permitted reading of the task is a binary channel of absolute bias at most `ε` and
costs at least one unit in coordinate `j`. Actions that are not permitted are unconstrained. -/
structure BinaryTask {H0 A V R ι : Type} [Fintype H0] [Fintype A]
    (T : ProtocolTask H0 Bool A Bool V R ι) (ε : ℝ) (j : ι) where
  bias : H0 → List (A × Bool) → A → ℝ
  bound : ∀ u h a, T.permitted u h a → |bias u h a| ≤ ε
  source : ∀ u h a, T.permitted u h a → ∀ z y,
    (T.observation u h a z).mass y = binaryKernel (bias u h a) z y
  reading_cost : ∀ u h a, T.permitted u h a → 1 ≤ T.cost j u h a

namespace BinaryTask
open scoped ENNReal
variable {H0 A V R ι : Type} [Fintype H0] [Fintype A]
variable {T : ProtocolTask H0 Bool A Bool V R ι} {ε : ℝ} {j : ι}

/-- Every admissible strategy obeys the all-prior capacity bound at every record, because it
uses only permitted readings at its active, positive-mass branches. -/
theorem capacity (m : BinaryTask T ε j) (hε : ε ≤ 1 / 2) (σ : ProtocolStrategy H0 A Bool R)
    (hσ : T.Admissible σ) (u : H0) :
    LocalCapacityBound ((T.costConditional σ j).given u) (4 * ε ^ 2) := by
  intro h a hw hs ha
  have hp : T.permitted u h a := hσ.2 u h a hs ha
  have hsrc : ∀ z y, (((T.costConditional σ j).given u).observation h a z).mass y =
      binaryKernel (m.bias u h a) z y := m.source u h a hp
  have hgain : localGain ((T.costConditional σ j).given u) h a =
      jointMI (binaryJoint (posterior ((T.costConditional σ j).given u) h true)
        (m.bias u h a)) := by
    unfold localGain binaryJoint
    rw [posterior_eq_binaryPrior _ h hw]
    simp only [hsrc, binaryPrior, if_true]
  rw [hgain]
  calc
    jointMI (binaryJoint (posterior ((T.costConditional σ j).given u) h true) (m.bias u h a)) ≤
        4 * ε ^ 2 := binaryJoint_information_le_envelope _ _ ε (m.bound u h a hp) hε
    _ ≤ (4 * ε ^ 2) * ((T.costConditional σ j).given u).cost h a := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (m.reading_cost u h a hp) (by positivity : 0 ≤ 4 * ε ^ 2)

/-- The finite-horizon acquisition bound of an admissible strategy. -/
theorem information_le_cost (m : BinaryTask T ε j) (hε : ε ≤ 1 / 2)
    (σ : ProtocolStrategy H0 A Bool R) (hσ : T.Admissible σ) (n : ℕ) :
    T.information σ n ≤ 4 * ε ^ 2 * T.expectedCostAt σ n j :=
  (T.information_eq_cost σ n j).trans_le
    (conditionalJointInfo_bounds (T.costConditional σ j) n _ (historyBank_complete A Bool n)
      (4 * ε ^ 2) (fun u _ => m.capacity hε σ hσ u)).2.2.2.2

/-- Every feasible requirement pays the inverse-square price in coordinate `j`. -/
theorem frontier_lower (m : BinaryTask T ε j) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (n : ℕ)
    (q : ProtocolRequirement ι) (hq : T.Feasible n q) :
    q.information / (4 * ε ^ 2) ≤ q.budget j := by
  obtain ⟨σ, hσ, hi, _, _, hc⟩ := hq
  apply (div_le_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  calc
    q.information ≤ 4 * ε ^ 2 * T.expectedCostAt σ n j :=
      hi.trans (m.information_le_cost hε σ hσ n)
    _ ≤ 4 * ε ^ 2 * q.budget j := mul_le_mul_of_nonneg_left (hc j) (by positivity)
    _ = q.budget j * (4 * ε ^ 2) := mul_comm _ _

/-- The least cost in coordinate `j` lies above the inverse-square price. -/
theorem minimumCost_lower (m : BinaryTask T ε j) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (n : ℕ)
    (q : ProtocolRequirement ι) :
    ENNReal.ofReal (q.information / (4 * ε ^ 2)) ≤ T.minimumCost n q j := by
  apply le_iInf₂
  intro σ hσ
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  rw [mul_comm]
  exact hσ.2.1.trans (m.information_le_cost hε σ hσ.1 n)

/-- The information limit of an admissible strategy is bounded by its finite extended cost. -/
theorem informationLimit_le_budget (m : BinaryTask T ε j) (hε : ε ≤ 1 / 2)
    (σ : ProtocolStrategy H0 A Bool R) (hσ : T.Admissible σ) (b : ℝ) (hb : 0 ≤ b)
    (hcost : T.extendedCostOf σ j ≤ ENNReal.ofReal b) :
    T.informationLimitOf σ ≤ 4 * ε ^ 2 * b :=
  (T.informationLimitOf_eq_cost σ j).trans_le
    (conditionalInformationLimit_le_budget (T.costConditional σ j) (4 * ε ^ 2) b
      (by positivity) hb (fun u _ => m.capacity hε σ hσ u) hcost)

/-- The unbounded experiment pays the same price for every real budget. -/
theorem limit_frontier_lower (m : BinaryTask T ε j) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (c b : ℝ)
    (hb : 0 ≤ b) (budget : ι → ℝ≥0∞) (hbj : budget j = ENNReal.ofReal b)
    (h : T.LimitFeasible c budget) : c / (4 * ε ^ 2) ≤ b := by
  obtain ⟨σ, hσ, hi, hc⟩ := h
  apply (div_le_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  rw [mul_comm]
  exact hi.trans (m.informationLimit_le_budget hε σ hσ b hb ((hc j).trans_eq hbj))

/-- The least extended cost of the unbounded experiment lies above the inverse-square price;
an infinite extended cost is allowed. -/
theorem limitMinimumCost_lower (m : BinaryTask T ε j) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (c : ℝ) : ENNReal.ofReal (c / (4 * ε ^ 2)) ≤ T.limitMinimumCost c j := by
  apply le_iInf₂
  intro σ hσ
  by_cases htop : T.extendedCostOf σ j = ⊤
  · rw [htop]
    exact le_top
  · have he : T.extendedCostOf σ j = ENNReal.ofReal (T.extendedCostOf σ j).toReal :=
      (ENNReal.ofReal_toReal htop).symm
    rw [he]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
    rw [mul_comm]
    exact hσ.2.trans (m.informationLimit_le_budget hε σ hσ.1 _ ENNReal.toReal_nonneg he.le)

/-- At zero signal no feasible requirement asks for positive information; no division occurs. -/
theorem zero_capacity (m : BinaryTask T 0 j) (n : ℕ) (q : ProtocolRequirement ι)
    (hq : T.Feasible n q) : q.information ≤ 0 := by
  obtain ⟨σ, hσ, hi, _⟩ := hq
  have h0 := m.information_le_cost (by norm_num) σ hσ n
  norm_num at h0
  exact hi.trans h0

/-- At zero signal every admissible unbounded experiment acquires nothing, at every cost. -/
theorem limit_zero_capacity (m : BinaryTask T 0 j) (σ : ProtocolStrategy H0 A Bool R)
    (hσ : T.Admissible σ) : T.informationLimitOf σ = 0 :=
  (T.informationLimitOf_eq_cost σ j).trans
    (conditionalInformationLimit_zero_capacity (T.costConditional σ j) (fun u _ => by
      simpa using m.capacity (by norm_num) σ hσ u))

end BinaryTask

/-! ### Concrete binary tasks and the controls of M3.5 -/

/-- The signed-bias reading as a finite law on the outcome. -/
noncomputable def binaryKernelLaw (δ : ℝ) (hδ : |δ| ≤ 1 / 2) (z : Bool) : FiniteLaw Bool where
  mass := binaryKernel δ z
  nonnegative := binaryKernel_nonnegative δ hδ z
  total := binaryKernel_total δ z

/-- One hidden bit of prior `q`, one reading of signed bias `δ` at a fixed price per reading,
readouts that may use the whole retained history, and the license `lic` on every readout. -/
noncomputable def binaryTask (q δ price : ℝ) (lic : Prop) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) :
    ProtocolTask Unit Bool Unit Bool Bool (List (Unit × Bool) → Option Bool) Unit where
  initialRecord := unitLaw
  prior _ := binaryPriorLaw q hq0 hq1
  observation _ _ _ z := binaryKernelLaw δ hδ z
  permitted _ _ _ := True
  target _ z := z
  licensed _ := lic
  readout r _ h := r h
  cost _ _ _ _ := price
  cost_nonnegative _ _ _ _ := hp

/-- Each binary task with a unit price per reading is a binary task of its own bias. -/
def binaryTask_binary (q δ price : ℝ) (lic : Prop) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) (hprice : 1 ≤ price) :
    BinaryTask (binaryTask q δ price lic hq0 hq1 hδ hp) |δ| () where
  bias _ _ _ := δ
  bound _ _ _ _ := le_rfl
  source _ _ _ _ _ _ := rfl
  reading_cost _ _ _ _ := hprice

/-- Bool negation as an equivalence. -/
def boolFlip : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

/-- Reversing the bias is the same reading with its outcome renamed. -/
theorem binaryKernel_flip (δ : ℝ) (z y : Bool) :
    binaryKernel (-δ) z (!y) = binaryKernel δ z y := by
  cases z <;> cases y <;> simp [binaryKernel, sub_eq_add_neg]

/-- The concrete renamed binary protocol: the outcome of the reading is negated, the bias is
reversed and the readouts are composed with the renaming of histories. -/
noncomputable def binaryTaskFlip (q δ price : ℝ) (lic : Prop) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) :
    TaskIso (binaryTask q δ price lic hq0 hq1 hδ hp)
      (binaryTask q (-δ) price lic hq0 hq1 (by rwa [abs_neg]) hp) where
  record := Equiv.refl Unit
  input := Equiv.refl Bool
  action := Equiv.refl Unit
  outcome := boolFlip
  answer := Equiv.refl Bool
  repair := (historyEquiv (Equiv.refl Unit) boolFlip).arrowCongr (Equiv.refl (Option Bool))
  coord := Equiv.refl Unit
  initialRecord _ := rfl
  prior _ _ := rfl
  observation _ _ _ z y := binaryKernel_flip δ z y
  permitted _ _ _ := Iff.rfl
  target _ _ := rfl
  licensed _ := Iff.rfl
  readout r _ h := by
    show r ((historyEquiv (Equiv.refl Unit) boolFlip).symm
      (historyEquiv (Equiv.refl Unit) boolFlip h)) = (r h).map (Equiv.refl Bool)
    rw [Equiv.symm_apply_apply, option_map_refl]
  cost _ _ _ _ := rfl

/-- The renamed protocol has the same frontier at every horizon, and its kernel is a different
function whenever the bias is nonzero. -/
theorem binaryTaskFlip_frontier (q δ price : ℝ) (lic : Prop) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) (hδ0 : δ ≠ 0) (n : ℕ) (r : ProtocolRequirement Unit) :
    ((binaryTask q (-δ) price lic hq0 hq1 (by rwa [abs_neg]) hp).Feasible n r ↔
      (binaryTask q δ price lic hq0 hq1 hδ hp).Feasible n r) ∧
    binaryKernel (-δ) true true ≠ binaryKernel δ true true := by
  refine ⟨(binaryTaskFlip q δ price lic hq0 hq1 hδ hp).feasible_transport_iff n r, ?_⟩
  intro h
  simp only [binaryKernel, if_true] at h
  exact hδ0 (by linarith)

/-- Horizon zero of a binary task: error and refusal are read at the empty history. -/
theorem binaryTask_error_zero (q δ price : ℝ) (lic : Prop) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price)
    (σ : ProtocolStrategy Unit Unit Bool (List (Unit × Bool) → Option Bool)) :
    (binaryTask q δ price lic hq0 hq1 hδ hp).errorMass σ 0 =
      q * errorLoss true (σ.repair []) + (1 - q) * errorLoss false (σ.repair []) := by
  unfold ProtocolTask.errorMass
  simp only [stoppedExpectation_zero, Fintype.sum_unique, Fintype.sum_bool]
  change 1 * (q * errorLoss true (σ.repair []) + (1 - q) * errorLoss false (σ.repair [])) = _
  rw [one_mul]

theorem binaryTask_refusal_zero (q δ price : ℝ) (lic : Prop) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price)
    (σ : ProtocolStrategy Unit Unit Bool (List (Unit × Bool) → Option Bool)) :
    (binaryTask q δ price lic hq0 hq1 hδ hp).refusalMass σ 0 = refusalLoss (σ.repair []) := by
  unfold ProtocolTask.refusalMass
  simp only [stoppedExpectation_zero, Fintype.sum_unique, Fintype.sum_bool]
  change 1 * (q * refusalLoss (σ.repair []) + (1 - q) * refusalLoss (σ.repair [])) = _
  ring

theorem binaryTask_cost_zero (q δ price : ℝ) (lic : Prop) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price)
    (σ : ProtocolStrategy Unit Unit Bool (List (Unit × Bool) → Option Bool)) (j : Unit) :
    (binaryTask q δ price lic hq0 hq1 hδ hp).expectedCostAt σ 0 j = 0 := by
  unfold ProtocolTask.expectedCostAt conditionalExpectedCost
  simp only [expectedCost_horizon_zero, mul_zero, Finset.sum_const_zero]

/-- The strategy that stops at once and reports `answer` from every history. -/
def stopAndReport (answer : Option Bool) :
    ProtocolStrategy Unit Unit Bool (List (Unit × Bool) → Option Bool) where
  policy _ _ := unitLaw
  stop _ _ := true
  repair _ := answer

/-- At horizon zero, error at most one quarter and no refusal. -/
noncomputable def quarterErrorTarget : ProtocolRequirement Unit := ⟨0, 1 / 4, 0, fun _ => 0⟩

/-- Equal support, different probabilities: the prior of one quarter meets the target. -/
theorem quarterPrior_feasible (δ price : ℝ) (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) :
    (binaryTask (1 / 4) δ price True (by norm_num) (by norm_num) hδ hp).Feasible 0
      quarterErrorTarget := by
  refine ⟨stopAndReport (some false), ⟨trivial, fun _ _ _ _ _ => trivial⟩,
    ProtocolTask.information_nonnegative _ _ 0, ?_, ?_, fun j => ?_⟩
  · rw [binaryTask_error_zero]
    simp [stopAndReport, errorLoss, quarterErrorTarget]
  · rw [binaryTask_refusal_zero]
    simp [stopAndReport, refusalLoss, quarterErrorTarget]
  · rw [binaryTask_cost_zero]
    rfl

/-- Equal support, different probabilities: the fair prior does not meet the same target. -/
theorem fairPrior_infeasible (δ price : ℝ) (lic : Prop) (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) :
    ¬ (binaryTask (1 / 2) δ price lic (by norm_num) (by norm_num) hδ hp).Feasible 0
      quarterErrorTarget := by
  rintro ⟨σ, _, _, he, hr, _⟩
  rw [binaryTask_error_zero] at he
  rw [binaryTask_refusal_zero] at hr
  cases ho : σ.repair [] with
  | none =>
    rw [ho] at hr
    norm_num [refusalLoss, quarterErrorTarget] at hr
  | some b =>
    rw [ho] at he
    cases b <;> simp [errorLoss, quarterErrorTarget] at he <;> norm_num at he

/-- Same support, different probabilities: no law-preserving isomorphism exists, whatever the
renamings, so support alone transports neither information nor the frontier. -/
theorem equalSupport_control (δ price : ℝ) (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) :
    (∀ b, 0 < binaryPrior (1 / 2) b) ∧ (∀ b, 0 < binaryPrior (1 / 4) b) ∧
      IsEmpty (TaskIso
        (binaryTask (1 / 2) δ price True (by norm_num) (by norm_num) hδ hp)
        (binaryTask (1 / 4) δ price True (by norm_num) (by norm_num) hδ hp)) := by
  refine ⟨fun b => by cases b <;> norm_num [binaryPrior],
    fun b => by cases b <;> norm_num [binaryPrior], ⟨fun e => ?_⟩⟩
  exact fairPrior_infeasible δ price True hδ hp
    (e.symm.feasible_transport 0 _ (quarterPrior_feasible δ price hδ hp))

/-- Refusal everywhere, no error, no cost at horizon zero. -/
def refusalTarget : ProtocolRequirement Unit := ⟨0, 1, 1, fun _ => 0⟩

/-- A licensed binary task meets the refusal target. -/
theorem licensed_refusal_feasible (q δ price : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) :
    (binaryTask q δ price True hq0 hq1 hδ hp).Feasible 0 refusalTarget := by
  refine ⟨stopAndReport none, ⟨trivial, fun _ _ _ _ _ => trivial⟩,
    ProtocolTask.information_nonnegative _ _ 0, ?_, ?_, fun j => ?_⟩
  · rw [binaryTask_error_zero]
    simp [stopAndReport, errorLoss, refusalTarget]
  · rw [binaryTask_refusal_zero]
    simp [stopAndReport, refusalLoss, refusalTarget]
  · rw [binaryTask_cost_zero]
    rfl

/-- A map that keeps every law, readout and cost but loses the license: the unlicensed task is
feasible nowhere, no isomorphism exists, and the one-way simulation from it exists. -/
theorem licenseLoss_control (q δ price : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) :
    (binaryTask q δ price True hq0 hq1 hδ hp).Feasible 0 refusalTarget ∧
      (∀ n r, ¬ (binaryTask q δ price False hq0 hq1 hδ hp).Feasible n r) ∧
      IsEmpty (TaskIso (binaryTask q δ price True hq0 hq1 hδ hp)
        (binaryTask q δ price False hq0 hq1 hδ hp)) ∧
      Nonempty (TaskSimulation (binaryTask q δ price False hq0 hq1 hδ hp)
        (binaryTask q δ price True hq0 hq1 hδ hp) 0) := by
  have hno : ∀ n r, ¬ (binaryTask q δ price False hq0 hq1 hδ hp).Feasible n r :=
    fun _ _ ⟨_, ha, _⟩ => ha.1
  refine ⟨licensed_refusal_feasible q δ price hq0 hq1 hδ hp, hno, ⟨fun e => ?_⟩, ⟨?_⟩⟩
  · exact hno 0 _ (e.feasible_transport 0 _ (licensed_refusal_feasible q δ price hq0 hq1 hδ hp))
  · exact
      { map := id
        admissible := fun _ ha => absurd ha.1 id
        information := fun _ ha => absurd ha.1 id
        error := fun _ ha => absurd ha.1 id
        refusal := fun _ ha => absurd ha.1 id
        convert := id
        convert_mono := fun _ _ h => h
        cost := fun _ ha => absurd ha.1 id }

/-- The strategy that reads once and reports `answer` from every history. -/
def readOnce (answer : List (Unit × Bool) → Option Bool) :
    ProtocolStrategy Unit Unit Bool (List (Unit × Bool) → Option Bool) where
  policy _ _ := unitLaw
  stop _ _ := false
  repair := answer

/-- One reading at horizon one acquires exactly the information of the reading. -/
theorem readOnce_information (q δ price : ℝ) (lic : Prop) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hδ : |δ| ≤ 1 / 2) (hp : 0 ≤ price) (answer : List (Unit × Bool) → Option Bool) :
    (binaryTask q δ price lic hq0 hq1 hδ hp).information (readOnce answer) 1 =
      jointMI (binaryJoint q δ) := by
  set p := ((binaryTask q δ price lic hq0 hq1 hδ hp).lawConditional (readOnce answer)).given ()
  have hb := historyBank_complete Unit Bool 1
  have hw : historyMass p [] = 1 := binaryPrior_total q
  have hpost : posterior p [] = binaryPrior q := by
    funext z
    unfold posterior
    rw [hw, div_one]
    rfl
  have hgain : localGain p [] () = jointMI (binaryJoint q δ) := by
    unfold localGain
    rw [hpost]
    rfl
  unfold ProtocolTask.information
  rw [conditionalJointInfo_eq_conditionalMI _ 1 _ hb]
  unfold conditionalMI
  rw [Fintype.sum_unique]
  change 1 * terminalMI p 1 (historyBank Unit Bool 1) = _
  rw [one_mul, terminalMI_eq_gain_sum p 1 _ hb, hb.sum_eq, historySet_sum_succ]
  have hnil : ([] : List (Unit × Bool)).length < 1 ∧ p.stop [] = false := ⟨Nat.zero_lt_one, rfl⟩
  have hgain' : ∀ a : Unit, (p.policy []).mass a * localGain p [] a = jointMI (binaryJoint q δ) := by
    intro a
    cases a
    rw [hgain]
    exact one_mul _
  have hzero : ∀ (h : List (Unit × Bool)) (e : Unit × Bool),
      (if (h ++ [e]).length < 1 ∧ p.stop (h ++ [e]) = false then
        historyMass p (h ++ [e]) * ∑ a, (p.policy (h ++ [e])).mass a * localGain p (h ++ [e]) a
      else 0) = 0 := fun h e => if_neg (by simp)
  rw [if_pos hnil, hw, one_mul]
  simp only [hzero, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_unique, hgain']

/-- Same laws, different costs: a free reading meets one bit at budget zero, a priced reading
does not. -/
theorem cost_control :
    (binaryTask (1 / 2) (1 / 2) 0 True (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
      le_rfl).Feasible 1 ⟨1, 1, 1, fun _ => 0⟩ ∧
    ¬ (binaryTask (1 / 2) (1 / 2) 1 True (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
      zero_le_one).Feasible 1 ⟨1, 1, 1, fun _ => 0⟩ := by
  constructor
  · refine ⟨readOnce (fun _ => none), ⟨trivial, fun _ _ _ _ _ => trivial⟩, ?_, ?_, ?_,
      fun j => ?_⟩
    · rw [readOnce_information, binaryJoint_information_fair]
      norm_num
    · exact (ProtocolTask.errorMass_eq_zero_of_refuses _ _ 1 (fun _ _ => rfl)).le.trans
        zero_le_one
    · exact (ProtocolTask.refusalMass_eq_one_of_refuses _ _ 1 (fun _ _ => rfl)).le
    · exact (ProtocolTask.expectedCostAt_eq_zero_of_free _ _ 1 j (fun _ _ _ => rfl)).le
  · intro h
    have k := (binaryTask_binary (1 / 2) (1 / 2) 1 True (by norm_num) (by norm_num)
      (by norm_num [abs_of_pos]) zero_le_one le_rfl).frontier_lower (by norm_num [abs_of_pos])
      (by norm_num [abs_of_pos]) 1 _ h
    norm_num [abs_of_pos] at k

/-- A record of outcomes alone is not a relabeling of histories: two histories with the same
outcome record and different actions are distinct, and a task isomorphism translates both. -/
theorem outcomeRecord_not_injective :
    ¬ Function.Injective (fun h : List (Bool × Unit) => h.map Prod.snd) := by
  intro hinj
  have k := @hinj [(true, ())] [(false, ())] rfl
  simp at k

end OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
