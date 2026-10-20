import OperatorKO7.Meta.SchemaOperationalIncompleteness
import OperatorKO7.Meta.RecordEmissionNecessity
import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.SchemaNormMismatch
import OperatorKO7.Meta.SchemaConfessionDominance

/-!
# Statements the paper makes that the cited declarations did not yet carry

The claim inventory found paper statements whose cited Lean declarations prove less than the
paper says. This module proves the stated forms.

* Staticity of the boundary: a step-indexed family of projection transactions whose license is the
  same at consecutive stages, and whose license determines the projected dimension and the
  forgetting witness, is constant.
* The generator sort of the record-emitting syntax has one term, so the duplicated generator is the
  unique bridge between the emitted record and the continuing computation.
* The six-clause LCEL comparison type and the comparison-witness type are subsingletons.
* Marginal cost per bit of gauge information: with cumulative completed-cell mass
  `Cum(j,w) = w j (j+1) / 2` and `bitCost(m,w) = Cum(2^m - 1, w) - Cum(2^(m-1) - 1, w)`, the identity
  `2 bitCost(m,w) + w 2^(m-1) = 3 w 4^(m-1)` and the bound `bitCost(m,w) >= w 4^(m-1)` hold for
  `m >= 1`; the projected counter of height `k >= 1` needs `floor(log2 k) + 1` bits.
* The explicit description is shorter than the repeated-carrier envelope when the cell weight is at
  least two, the index at least two, and the glue overhead below the index; at index zero the
  inequality runs the other way.
* Terminal-record completeness on a sorted record model: for positive depth the record determines
  the base identifier, the payload identifier, and the depth; at depth zero the payload identifier
  is absent; when the base slot may hold a frame, depth and base cannot both be recovered; and the
  squared depth times the payload size is at most the doubled confessed burden.

Relation: equality of records, transactions, and comparison witnesses.
Property: the paper statements named above.
Trust: kernel only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.ClaimStrengthening

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.RecordTerm
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-! ## Staticity of the boundary -/

/-- Two projection transactions with equal dimension, license, and forgetting witness are
equal. -/
theorem projectionTransaction_ext {S : StepDuplicatingSchema} {T U : ProjectionTransaction S}
    (hd : T.dimension = U.dimension) (hl : T.license = U.license)
    (hb : T.boundary = U.boundary) : T = U := by
  cases T with
  | mk d l b p =>
    cases U with
    | mk d' l' b' p' =>
      dsimp only at hd hl hb
      subst hd hl hb
      rfl

/-- **Staticity of the boundary.** A step-indexed family of projection transactions whose license
is the same at consecutive stages, and whose license determines the projected dimension and the
forgetting witness, is static and constant. -/
theorem projectionFamily_constant_of_license_constant {S : StepDuplicatingSchema}
    (τ : ℕ → ProjectionTransaction S) (hlic : ∀ i, (τ (i + 1)).license = (τ i).license)
    (hdet : ∀ i j, (τ i).license = (τ j).license →
      (τ i).dimension = (τ j).dimension ∧ (τ i).boundary = (τ j).boundary) :
    IsStaticProjectionFamily τ ∧ ∀ i j, τ i = τ j := by
  have hl0 : ∀ i, (τ i).license = (τ 0).license := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => exact (hlic n).trans ih
  have hall : ∀ i, τ i = τ 0 := fun i =>
    projectionTransaction_ext (hdet i 0 (hl0 i)).1 (hl0 i) (hdet i 0 (hl0 i)).2
  exact ⟨fun i => ⟨(hdet i 0 (hl0 i)).1, hl0 i, (hdet i 0 (hl0 i)).2⟩,
    fun i j => (hall i).trans (hall j).symm⟩

/-! ## The generator bridge -/

/-- The generator sort has one term. -/
theorem recordGenerator_eq_gen (g : RecordGenerator) : g = RecordGenerator.gen := by
  cases g
  rfl

/-- The generator sort is a subsingleton. -/
instance recordGenerator_subsingleton : Subsingleton RecordGenerator :=
  ⟨fun a b => (recordGenerator_eq_gen a).trans (recordGenerator_eq_gen b).symm⟩

/-- **The shared generator is the unique bridge.** Any two generator tokens are equal, and the
primitive duplicator's right-hand side carries two distinct generator positions. -/
theorem generator_bridge_unique (n : RecordCounter) :
    (∀ g₁ g₂ : RecordGenerator, g₁ = g₂) ∧
      type_of% (primitiveDuplicatorRhs_witnesses_duplication n) :=
  ⟨fun a b => Subsingleton.elim a b, primitiveDuplicatorRhs_witnesses_duplication n⟩

/-! ## LCEL comparison types -/

/-- The six-clause LCEL comparison type is a subsingleton: every field is a proposition. -/
instance lcelQuasiFunctor_subsingleton (L₁ L₂ : OperatorKO7.LCELSchema.FormalLCELInstance) :
    Subsingleton (OperatorKO7.LCELStructuralIdentity.LCELQuasiFunctor L₁ L₂) :=
  ⟨fun a b => by
    cases a
    cases b
    rfl⟩

/-- The LCEL comparison-witness type is a subsingleton: every field is a proposition. -/
instance lcelComparisonWitness_subsingleton (L₁ L₂ : OperatorKO7.LCELSchema.FormalLCELInstance) :
    Subsingleton (OperatorKO7.LCELStructuralIdentity.LCELComparisonWitness L₁ L₂) :=
  ⟨fun a b => by
    cases a
    cases b
    rfl⟩

/-! ## Marginal cost per bit of gauge information -/

/-- Doubled cumulative completed-cell mass through stage `j`. -/
def cumCellMassDoubled (j w : ℕ) : ℕ := w * j * (j + 1)

/-- Cumulative completed-cell mass through stage `j`: `w j (j+1) / 2`. -/
def cumCellMass (j w : ℕ) : ℕ := w * (j * (j + 1) / 2)

theorem cumCellMassDoubled_eq (j w : ℕ) : cumCellMassDoubled j w = 2 * cumCellMass j w := by
  unfold cumCellMassDoubled cumCellMass
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self j
  rw [mul_assoc, ht, show (t + t) / 2 = t by omega]
  ring

/-- Doubled marginal cost of the `m`-th bit: the completed-cell mass between stages
`2^(m-1) - 1` and `2^m - 1`, doubled. -/
def bitCostDoubled (m w : ℕ) : ℕ :=
  cumCellMassDoubled (2 ^ m - 1) w - cumCellMassDoubled (2 ^ (m - 1) - 1) w

/-- Marginal cost of the `m`-th bit. -/
def bitCost (m w : ℕ) : ℕ := cumCellMass (2 ^ m - 1) w - cumCellMass (2 ^ (m - 1) - 1) w

theorem bitCostDoubled_eq (m w : ℕ) (hm : 1 ≤ m) : bitCostDoubled m w = 2 * bitCost m w := by
  have hle : 2 ^ (m - 1) - 1 ≤ 2 ^ m - 1 := by
    have : 2 ^ (m - 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hmono : cumCellMass (2 ^ (m - 1) - 1) w ≤ cumCellMass (2 ^ m - 1) w := by
    unfold cumCellMass
    exact Nat.mul_le_mul le_rfl (Nat.div_le_div_right (Nat.mul_le_mul hle (by omega)))
  unfold bitCostDoubled bitCost
  rw [cumCellMassDoubled_eq, cumCellMassDoubled_eq]
  omega

/-- **The bit-cost identity** (doubled form): `2 bitCost(m,w) + w 2^(m-1) = 3 w 4^(m-1)`. -/
theorem bitCostDoubled_identity (m w : ℕ) (hm : 1 ≤ m) :
    bitCostDoubled m w + w * 2 ^ (m - 1) = 3 * w * 4 ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ n = b + 1 :=
    ⟨2 ^ n - 1, (Nat.succ_pred_eq_of_pos (Nat.two_pow_pos n)).symm⟩
  have h2 : 2 ^ (n + 1) - 1 = 2 * b + 1 := by
    rw [pow_succ, hb]
    omega
  have h0 : 2 ^ n - 1 = b := by
    rw [hb]
    omega
  have h4 : 4 ^ n = (b + 1) * (b + 1) := by
    rw [← hb, ← mul_pow]
    norm_num
  unfold bitCostDoubled cumCellMassDoubled
  rw [Nat.add_sub_cancel, h2, h0, h4, hb]
  have hle : w * b * (b + 1) ≤ w * (2 * b + 1) * (2 * b + 1 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) (by omega)
  zify [hle]
  ring

/-- **The bit-cost identity:** `2 bitCost(m,w) + w 2^(m-1) = 3 w 4^(m-1)` for `m >= 1`. -/
theorem bitCost_identity (m w : ℕ) (hm : 1 ≤ m) :
    2 * bitCost m w + w * 2 ^ (m - 1) = 3 * w * 4 ^ (m - 1) := by
  rw [← bitCostDoubled_eq m w hm]
  exact bitCostDoubled_identity m w hm

/-- **Each bit crosses a geometrically larger shell:** `bitCost(m,w) >= w 4^(m-1)`. -/
theorem bitCost_ge (m w : ℕ) (hm : 1 ≤ m) : w * 4 ^ (m - 1) ≤ bitCost m w := by
  have hid := bitCost_identity m w hm
  have h4 : 4 ^ (m - 1) = 2 ^ (m - 1) * 2 ^ (m - 1) := by
    rw [← mul_pow]
    norm_num
  rw [h4] at hid ⊢
  have hX : w * 2 ^ (m - 1) ≤ w * (2 ^ (m - 1) * 2 ^ (m - 1)) :=
    Nat.mul_le_mul le_rfl (Nat.le_mul_self _)
  nlinarith [hid, hX]

/-- Binary length of the projected counter. -/
def projBits (k : ℕ) : ℕ := Nat.log 2 k + 1

/-- The projected counter of height `k >= 1` occupies exactly `projBits k` binary digits. -/
theorem projBits_spec (k : ℕ) (hk : 1 ≤ k) :
    2 ^ (projBits k - 1) ≤ k ∧ k < 2 ^ projBits k := by
  unfold projBits
  rw [Nat.add_sub_cancel]
  exact ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) k⟩

/-! ## Explicit description against the repeated carrier -/

theorem index_succ_lt_two_pow (i : ℕ) (hi : 2 ≤ i) : i + 1 < 2 ^ i := by
  induction i, hi using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
      rw [pow_succ]
      omega

/-- **The repeated carrier exceeds the explicit description** when the cell weight is at least
two, the index at least two, and the glue overhead below the index. -/
theorem explicitDescriptionLength_lt_repeatedCarrierMass (wrapSize paySize glue i : ℕ)
    (hweight : 2 ≤ wrapSize + paySize) (hi : 2 ≤ i) (hglue : glue < i) :
    explicitDescriptionLength wrapSize paySize glue i < repeatedCarrierMass wrapSize paySize i := by
  have hbal := repeatedCarrierMass_description_balance wrapSize paySize glue i
  have hsize : Nat.size (i + 1) ≤ i := Nat.size_le.2 (index_succ_lt_two_pow i hi)
  have hmul : i * 2 ≤ i * (wrapSize + paySize) := Nat.mul_le_mul le_rfl hweight
  omega

/-- **At index zero the inequality runs the other way.** -/
theorem repeatedCarrierMass_lt_explicitDescriptionLength_at_zero (wrapSize paySize glue : ℕ) :
    repeatedCarrierMass wrapSize paySize 0 < explicitDescriptionLength wrapSize paySize glue 0 := by
  have hsize : Nat.size (0 + 1) = 1 := Nat.size_one
  unfold repeatedCarrierMass explicitDescriptionLength
  omega

/-! ## Terminal-record completeness on a sorted record model -/

/-- Records of the sorted model: a base identifier under a stack of payload frames. The base slot
holds an identifier, never a frame. -/
inductive SortedRecord where
  | base : ℕ → SortedRecord
  | frame : ℕ → SortedRecord → SortedRecord
  deriving DecidableEq

/-- `K` payload frames with identifier `y` over the record `t`. -/
def framePow (y : ℕ) : ℕ → SortedRecord → SortedRecord
  | 0, t => t
  | K + 1, t => .frame y (framePow y K t)

/-- The terminal record `G^K(Y, X)` with base identifier `x` and payload identifier `y`. -/
def sortedRecord (K x y : ℕ) : SortedRecord := framePow y K (.base x)

/-- Number of payload frames. -/
def recordDepth : SortedRecord → ℕ
  | .base _ => 0
  | .frame _ t => recordDepth t + 1

/-- Identifier in the base slot. -/
def recordBase : SortedRecord → ℕ
  | .base x => x
  | .frame _ t => recordBase t

/-- Identifier of the outermost payload frame, when there is one. -/
def recordPayload : SortedRecord → Option ℕ
  | .base _ => none
  | .frame y _ => some y

theorem recordDepth_sortedRecord (K x y : ℕ) : recordDepth (sortedRecord K x y) = K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      unfold sortedRecord at ih ⊢
      simp only [framePow, recordDepth, ih]

theorem recordBase_sortedRecord (K x y : ℕ) : recordBase (sortedRecord K x y) = x := by
  induction K with
  | zero => rfl
  | succ K ih =>
      unfold sortedRecord at ih ⊢
      simp only [framePow, recordBase, ih]

theorem recordPayload_sortedRecord (K x y : ℕ) (hK : 1 ≤ K) :
    recordPayload (sortedRecord K x y) = some y := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rfl

/-- **Terminal-record completeness.** For positive depth the record determines its depth, its base
identifier, and its payload identifier. -/
theorem sortedRecord_injective {K K' x x' y y' : ℕ} (hK : 1 ≤ K) (hK' : 1 ≤ K')
    (h : sortedRecord K x y = sortedRecord K' x' y') : K = K' ∧ x = x' ∧ y = y' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← recordDepth_sortedRecord K x y, ← recordDepth_sortedRecord K' x' y', h]
  · rw [← recordBase_sortedRecord K x y, ← recordBase_sortedRecord K' x' y', h]
  · have hp := congrArg recordPayload h
    rw [recordPayload_sortedRecord K x y hK, recordPayload_sortedRecord K' x' y' hK'] at hp
    exact Option.some.inj hp

/-- **The zero-depth boundary.** At depth zero the record is the base identifier alone, so the
payload identifier is absent. -/
theorem sortedRecord_zero_forgets_payload (x y y' : ℕ) :
    sortedRecord 0 x y = sortedRecord 0 x y' ∧ recordPayload (sortedRecord 0 x y) = none :=
  ⟨rfl, rfl⟩

theorem framePow_frame (y K : ℕ) (t : SortedRecord) :
    framePow y K (.frame y t) = framePow y (K + 1) t := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [framePow, ih]

/-- **Sort separation is necessary.** When the base slot may hold a frame, the record of depth `K`
over the base `G(Y, X')` equals the record of depth `K + 1` over `X'`, so depth and base cannot both
be recovered. -/
theorem unsorted_depth_base_collision (K x y : ℕ) :
    framePow y K (.frame y (.base x)) = framePow y (K + 1) (.base x) ∧ K ≠ K + 1 :=
  ⟨framePow_frame y K (.base x), by omega⟩

/-- **Quadratic mass.** The squared depth times the payload size is at most the doubled confessed
burden `2 Con(K, Y) = (K+1)(K+2)|Y|`. -/
theorem depth_sq_mul_payload_le_confessedBurdenDoubled (K β : ℕ) :
    K ^ 2 * β ≤ confessedBurdenDoubled K β := by
  rw [confessedBurdenDoubled_eq]
  apply Nat.mul_le_mul_right
  nlinarith

end OperatorKO7.Meta.OperationalInexpressibility.ClaimStrengthening
