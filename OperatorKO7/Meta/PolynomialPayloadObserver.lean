import OperatorKO7.Meta.PayloadExposureMatrix

/-!
# Polynomial payload dominance

A finite monomial table assigns a natural-number value to payload-count vectors. `PolynomialPayloadDominates` selects a monomial with positive coefficient that uses the target coordinate linearly and has a positive cofactor at the base counts. The cofactor and the remaining table contribution must not decrease from the source counts to the target counts. Under these conditions, a strict rise in the target coordinate forces the table value to rise.

A direct whole-term observer must decrease along the declared step. The dominance conditions therefore rule out orientation of that step by an observer built from the table. A two-coordinate example without dominance shows a table that decreases when the target coordinate rises and another coordinate falls.

Scope: one root step in the `DuplicatingRecursiveFamily.Step` relation. No contextual or transitive-closure result is stated. Trust: no proof hole or added axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.StepDuplicating

/-! ## 1. Finite monomial table over payload-count coordinates -/

/-- A cross-monomial in payload-count coordinates: `coeff * count leftCoord ^ leftExp *
count rightCoord ^ rightExp`. Setting `rightExp = 0` recovers an ordinary single-coordinate
monomial, so the table below expresses both pure and cross-coupled polynomial terms. -/
structure PolynomialPayloadMonomial (C : Type) where
  /-- Nonnegative integer coefficient. -/
  coeff : Nat
  /-- First payload coordinate read by the monomial. -/
  leftCoord : C
  /-- Exponent on the first coordinate. -/
  leftExp : Nat
  /-- Second payload coordinate read by the monomial. -/
  rightCoord : C
  /-- Exponent on the second coordinate. -/
  rightExp : Nat

/-- Value of one monomial at a vector of payload counts. -/
def PolynomialPayloadMonomial.eval {C : Type} (m : PolynomialPayloadMonomial C)
    (count : C → Nat) : Nat :=
  m.coeff * count m.leftCoord ^ m.leftExp * count m.rightCoord ^ m.rightExp

/-- A finite polynomial table over payload-count coordinates. -/
abbrev PolynomialPayloadTable (C : Type) := List (PolynomialPayloadMonomial C)

/-- Value of a finite monomial table at a vector of payload counts. -/
def polynomialPayloadEval {C : Type} :
    PolynomialPayloadTable C → (C → Nat) → Nat
  | [], _ => 0
  | m :: ms, count => m.eval count + polynomialPayloadEval ms count

/-! ## 2. Monotonicity in the payload counts -/

/-- Base monotonicity of natural powers, proved locally by induction on the exponent so that no
Mathlib base-monotonicity name is assumed. -/
theorem natPow_le_of_base_le {a b : Nat} (h : a ≤ b) : ∀ e : Nat, a ^ e ≤ b ^ e
  | 0 => by simp
  | e + 1 => by
      have ih := natPow_le_of_base_le h e
      calc a ^ (e + 1) = a ^ e * a := by simp [Nat.pow_succ]
        _ ≤ b ^ e * b := Nat.mul_le_mul ih h
        _ = b ^ (e + 1) := by simp [Nat.pow_succ]

/-- Every monomial is nondecreasing in every payload count. -/
theorem PolynomialPayloadMonomial.eval_mono {C : Type} (m : PolynomialPayloadMonomial C)
    {u v : C → Nat} (h : ∀ c, u c ≤ v c) : m.eval u ≤ m.eval v := by
  simp only [PolynomialPayloadMonomial.eval]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.le_refl m.coeff)
      (natPow_le_of_base_le (h m.leftCoord) m.leftExp))
    (natPow_le_of_base_le (h m.rightCoord) m.rightExp)

/-- Every finite monomial table is nondecreasing in every payload count. -/
theorem polynomialPayloadEval_mono {C : Type} (T : PolynomialPayloadTable C)
    {u v : C → Nat} (h : ∀ c, u c ≤ v c) :
    polynomialPayloadEval T u ≤ polynomialPayloadEval T v := by
  induction T with
  | nil => simp [polynomialPayloadEval]
  | cons m ms ih =>
      simp only [polynomialPayloadEval]
      exact Nat.add_le_add (PolynomialPayloadMonomial.eval_mono m h) ih

/-- Evaluation distributes over concatenation of finite monomial tables. -/
theorem polynomialPayloadEval_append {C : Type} (T U : PolynomialPayloadTable C)
    (count : C → Nat) :
    polynomialPayloadEval (T ++ U) count =
      polynomialPayloadEval T count + polynomialPayloadEval U count := by
  induction T with
  | nil => simp [polynomialPayloadEval]
  | cons m ms ih =>
      simp [polynomialPayloadEval, ih, Nat.add_assoc]

/-! ## Cross-coupling conditions and algebraic dominance -/

/-- A monomial satisfies cross-coupling when its coefficient and both exponents are positive and its two coordinates differ. -/
structure CrossCoupledMonomial {C : Type} (m : PolynomialPayloadMonomial C) : Prop where
  /-- The monomial contributes with a positive coefficient. -/
  coeff_pos : 0 < m.coeff
  /-- The first coordinate is genuinely read. -/
  leftExp_pos : 0 < m.leftExp
  /-- The second coordinate is genuinely read. -/
  rightExp_pos : 0 < m.rightExp
  /-- The two coordinates are distinct, so the monomial couples two payload channels. -/
  coords_distinct : m.leftCoord ≠ m.rightCoord

/-- A monomial dominates coordinate `i` at base counts with a positive coefficient, `i` in the left slot with exponent one, and positive cofactor at the base value. -/
structure DominatingMonomialAt {C : Type} (m : PolynomialPayloadMonomial C)
    (i : C) (base : C → Nat) : Prop where
  /-- Positive coefficient. -/
  coeff_pos : 0 < m.coeff
  /-- The monomial reads the dominated coordinate in its first slot. -/
  target_is_left : m.leftCoord = i
  /-- The dominated coordinate occurs linearly. -/
  target_linear : m.leftExp = 1
  /-- The cofactor has positive monomial support at the base count vector. -/
  cofactor_pos : 0 < base m.rightCoord ^ m.rightExp

/-- **Algebraic net dominance.** The table has a distinguished monomial occurrence at coordinate
`i`; that occurrence's cofactor does not decrease, and the aggregate contribution of all remaining
occurrences does not decrease. This is independent of any step relation, observer, or orientation
predicate. -/
def PolynomialPayloadDominates {C : Type} (T : PolynomialPayloadTable C)
    (i : C) (u v : C → Nat) : Prop :=
  ∃ (pre : PolynomialPayloadTable C) (m : PolynomialPayloadMonomial C)
      (suffix : PolynomialPayloadTable C),
    T = pre ++ m :: suffix ∧
      DominatingMonomialAt m i u ∧
      u m.rightCoord ≤ v m.rightCoord ∧
      polynomialPayloadEval pre u + polynomialPayloadEval suffix u ≤
        polynomialPayloadEval pre v + polynomialPayloadEval suffix v

/-- A dominating monomial's value rises when its target coordinate rises and its cofactor coordinate does not decrease. -/
theorem PolynomialPayloadMonomial.eval_lt_of_dominating {C : Type}
    {m : PolynomialPayloadMonomial C} {i : C} {u v : C → Nat}
    (hdom : DominatingMonomialAt m i u)
    (hright : u m.rightCoord ≤ v m.rightCoord) (hlt : u i < v i) :
    m.eval u < m.eval v := by
  have hc : 0 < m.coeff := hdom.coeff_pos
  have hcofpos : 0 < u m.rightCoord ^ m.rightExp := hdom.cofactor_pos
  have hcof : u m.rightCoord ^ m.rightExp ≤ v m.rightCoord ^ m.rightExp :=
    natPow_le_of_base_le hright m.rightExp
  have hlt' : u m.leftCoord < v m.leftCoord := by
    rw [hdom.target_is_left]; exact hlt
  have h1 : m.coeff * u m.leftCoord < m.coeff * v m.leftCoord :=
    Nat.mul_lt_mul_of_pos_left hlt' hc
  have h2 :
      u m.rightCoord ^ m.rightExp * (m.coeff * u m.leftCoord) <
        u m.rightCoord ^ m.rightExp * (m.coeff * v m.leftCoord) :=
    Nat.mul_lt_mul_of_pos_left h1 hcofpos
  have h3 :
      u m.rightCoord ^ m.rightExp * (m.coeff * v m.leftCoord) ≤
        v m.rightCoord ^ m.rightExp * (m.coeff * v m.leftCoord) :=
    Nat.mul_le_mul_right (m.coeff * v m.leftCoord) hcof
  have h4 :
      u m.rightCoord ^ m.rightExp * (m.coeff * u m.leftCoord) <
        v m.rightCoord ^ m.rightExp * (m.coeff * v m.leftCoord) :=
    Nat.lt_of_lt_of_le h2 h3
  simp only [PolynomialPayloadMonomial.eval, hdom.target_linear, Nat.pow_one]
  calc m.coeff * u m.leftCoord * u m.rightCoord ^ m.rightExp
      = u m.rightCoord ^ m.rightExp * (m.coeff * u m.leftCoord) := by ac_rfl
    _ < v m.rightCoord ^ m.rightExp * (m.coeff * v m.leftCoord) := h4
    _ = m.coeff * v m.leftCoord * v m.rightCoord ^ m.rightExp := by ac_rfl

/-- **Dominance gives strict table increase.** When the target coordinate rises strictly, algebraic
net dominance makes the whole table rise strictly. -/
theorem polynomialPayloadEval_lt_of_dominates {C : Type}
    {i : C} {u v : C → Nat} (hlt : u i < v i)
    (T : PolynomialPayloadTable C) (hdom : PolynomialPayloadDominates T i u v) :
    polynomialPayloadEval T u < polynomialPayloadEval T v := by
  obtain ⟨pre, m, suffix, htable, hm, hright, hrest⟩ := hdom
  have hstrict : m.eval u < m.eval v :=
    PolynomialPayloadMonomial.eval_lt_of_dominating hm hright hlt
  rw [htable]
  simp only [polynomialPayloadEval_append, polynomialPayloadEval]
  omega

/-! ## 4. The induced direct whole-term observer -/

/-- Observer data contain a finite table with dominance from left-hand-side to right-hand-side payload counts at the distinguished coordinate. -/
structure PolynomialPayloadObserverData (F : DuplicatingRecursiveFamily) where
  /-- The finite monomial table. -/
  table : PolynomialPayloadTable F.schema.PayloadCoord
  /-- Algebraic dominance at the distinguished coordinate, relative to the left-hand-side counts. -/
  dominates :
    PolynomialPayloadDominates table F.distinguishedPayload
      (fun c => F.schema.payloadCount c F.schema.lhs)
      (fun c => F.schema.payloadCount c F.schema.rhs)

/-- The table value strictly increases across the declared rule under the stored dominance condition. -/
theorem polynomialPayloadObserverData_rule_strict_increase
    {F : DuplicatingRecursiveFamily} (D : PolynomialPayloadObserverData F) :
    polynomialPayloadEval D.table (fun c => F.schema.payloadCount c F.schema.lhs) <
      polynomialPayloadEval D.table (fun c => F.schema.payloadCount c F.schema.rhs) :=
  polynomialPayloadEval_lt_of_dominates F.distinguished_payload_count_strict D.table D.dominates

/-- The observer evaluates the table at payload counts. The stored dominance condition makes that value increase across the declared step, conflicting with the observer's required payload drop. -/
def polynomialPayloadObserver {F : DuplicatingRecursiveFamily}
    (D : PolynomialPayloadObserverData F) : DirectWholeTermObserver F where
  Carrier := Nat
  eval := fun t => polynomialPayloadEval D.table (fun c => F.schema.payloadCount c t)
  lt := fun m n => m < n
  visiblePayloadCoordinate := fun p => p = F.distinguishedPayload
  carrierSensitive := fun p => p = F.distinguishedPayload
  constructorLocal := True
  pumpMonotone := fun _ => True
  orient_forces_payload_drop := by
    intro i hVisible _hSensitive hOriented
    exfalso
    have hrise := polynomialPayloadObserverData_rule_strict_increase D
    omega

/-- The table increase on the declared rule rules out strict orientation by this observer. -/
theorem polynomialPayloadObserver_cannot_orient_rule
    {F : DuplicatingRecursiveFamily} (D : PolynomialPayloadObserverData F) :
    ¬ (polynomialPayloadEval D.table (fun c => F.schema.payloadCount c F.schema.rhs) <
        polynomialPayloadEval D.table (fun c => F.schema.payloadCount c F.schema.lhs)) := by
  have hrise := polynomialPayloadObserverData_rule_strict_increase D
  omega

/-- Dominance alone rules out global orientation of this family. No unbounded-pump assumption is needed for this one-step result. -/
theorem polynomialPayloadObserver_no_global_orientation_withoutPump
    {F : DuplicatingRecursiveFamily} (D : PolynomialPayloadObserverData F) :
    ¬ F.GloballyOrients (polynomialPayloadObserver D) := by
  intro hOrient
  exact polynomialPayloadObserver_cannot_orient_rule D (hOrient F.duplicating_step)

/-- Under the stored dominance data, the observer does not globally orient the family. The theorem also takes the family's unbounded-pump property as an input. -/
theorem polynomialPayloadObserver_no_global_orientation
    {F : DuplicatingRecursiveFamily} (D : PolynomialPayloadObserverData F)
    (_hPump : F.HasUnboundedPayloadPump F.distinguishedPayload) :
    ¬ F.GloballyOrients (polynomialPayloadObserver D) :=
  polynomialPayloadObserver_no_global_orientation_withoutPump D

/-! ## 5. Concrete cross-coupled inhabitant

Two Boolean payload coordinates. The table is a single genuinely cross-coupled monomial
`1 * count true * count false`. -/

/-- The concrete cross-coupled monomial `1 * count true ^ 1 * count false ^ 1`. -/
def crossCoupledMonomial : PolynomialPayloadMonomial Bool where
  coeff := 1
  leftCoord := true
  leftExp := 1
  rightCoord := false
  rightExp := 1

/-- The one-row table carrying the cross-coupled monomial. -/
def crossCoupledTable : PolynomialPayloadTable Bool := [crossCoupledMonomial]

/-- All-ones base count vector, used as the positive support point. -/
def unitCounts : Bool → Nat := fun _ => 1

/-- Count vector obtained by raising only the distinguished `true` coordinate. -/
def raisedTargetCounts : Bool → Nat := fun b => if b then 2 else 1

/-- The distinguished coordinate rises strictly in the positive control. -/
theorem unitCounts_target_lt : unitCounts true < raisedTargetCounts true := by decide

/-- The concrete monomial satisfies the cross-coupling conditions. -/
theorem crossCoupledMonomial_isCrossCoupled : CrossCoupledMonomial crossCoupledMonomial where
  coeff_pos := by decide
  leftExp_pos := by decide
  rightExp_pos := by decide
  coords_distinct := by decide

/-- The concrete monomial dominates at coordinate `true` relative to the all-ones counts. -/
theorem crossCoupledMonomial_dominatingAt :
    DominatingMonomialAt crossCoupledMonomial true unitCounts where
  coeff_pos := by decide
  target_is_left := rfl
  target_linear := rfl
  cofactor_pos := by decide

/-- The concrete table satisfies the algebraic dominance predicate. -/
theorem crossCoupledTable_dominates :
    PolynomialPayloadDominates crossCoupledTable true unitCounts raisedTargetCounts := by
  refine ⟨[], crossCoupledMonomial, [], rfl, crossCoupledMonomial_dominatingAt, ?_, ?_⟩
  · decide
  · simp [polynomialPayloadEval]

/-- The table value increases from `unitCounts` to `raisedTargetCounts`. -/
theorem crossCoupledTable_eval_strict_increase :
    polynomialPayloadEval crossCoupledTable unitCounts <
      polynomialPayloadEval crossCoupledTable raisedTargetCounts :=
  polynomialPayloadEval_lt_of_dominates unitCounts_target_lt _ crossCoupledTable_dominates

/-! ## Two-coordinate example oriented without dominance

The table reads only the `false` coordinate. From the low vector to the high vector, `true` rises while `false` falls, so the table value decreases and orients the pair. The table has no dominance at `true`; the example shows why the dominance condition is needed for the non-orientation theorem.
-/

/-- The monomial uses the `false` coordinate and has exponent zero on its second coordinate. -/
def escapeMonomial : PolynomialPayloadMonomial Bool where
  coeff := 1
  leftCoord := false
  leftExp := 1
  rightCoord := false
  rightExp := 0

/-- The one-row escape table. -/
def escapeTable : PolynomialPayloadTable Bool := [escapeMonomial]

/-- The initial count vector assigns one to both coordinates. -/
def escapeCountsLow : Bool → Nat := fun _ => 1

/-- The target count vector assigns two to `true` and zero to `false`. -/
def escapeCountsHigh : Bool → Nat := fun b => if b then 2 else 0

/-- The rise is strict at the `true` coordinate. -/
theorem escapeCounts_strict_at_true : escapeCountsLow true < escapeCountsHigh true := by
  decide

/-- **The escape table violates dominance at `true`.** Its only monomial reads `false` in both
slots, so neither the coordinate identification nor the linear-exponent clause can be met. -/
theorem escapeTable_not_dominates :
    ¬ PolynomialPayloadDominates escapeTable true escapeCountsLow escapeCountsHigh := by
  rintro ⟨pre, m, suffix, htable, hdom, _hright, _hrest⟩
  have hmem : m ∈ escapeTable := by
    rw [htable]
    simp
  have hm : m = escapeMonomial := by simpa [escapeTable] using hmem
  subst hm
  have := hdom.target_is_left
  simp [escapeMonomial] at this

/-- **The orienting escape.** Without dominance the table strictly decreases, hence orients the
pair in the termination direction, even though the distinguished `true` coordinate rises. -/
theorem escapeTable_orients_pair :
    polynomialPayloadEval escapeTable escapeCountsHigh <
      polynomialPayloadEval escapeTable escapeCountsLow := by
  simp [polynomialPayloadEval, PolynomialPayloadMonomial.eval, escapeTable, escapeMonomial,
    escapeCountsLow, escapeCountsHigh]

/-- The table value decreases from the low vector to the high vector, so it fails the strict-increase conclusion derived under dominance. -/
theorem escapeTable_no_strict_increase :
    ¬ (polynomialPayloadEval escapeTable escapeCountsLow <
        polynomialPayloadEval escapeTable escapeCountsHigh) := by
  exact Nat.not_lt_of_ge (Nat.le_of_lt escapeTable_orients_pair)

/-! ## 7. Concrete family-level orienting escape -/

/-- A right-duplicating schema whose declared step raises the distinguished `true` coordinate from
one to two while the independent `false` coordinate falls from one to zero. Terms outside the
declared step carry an explicit natural pump parameter for the `true` coordinate. -/
def escapeSchema : RightDuplicatingRecursorSchema where
  Term := Bool × Nat
  PayloadCoord := Bool
  Position := Unit
  lhs := (false, 0)
  rhs := (true, 0)
  payloadOccursAt := fun _ _ _ => False
  payloadCount := fun c t =>
    match t.1 with
    | false => if c then t.2 + 1 else 1
    | true => if c then 2 else 0
  distinguishedPayload := true
  lhs_has_payload := by decide
  rhs_duplicates_payload := by decide
  declaredClosedFirability := True

/-- The singleton-step family generated by `escapeSchema`. -/
def escapeFamily : DuplicatingRecursiveFamily where
  schema := escapeSchema
  Step := fun a b => a = (false, 0) ∧ b = (true, 0)
  duplicating_step := ⟨rfl, rfl⟩
  HasUnboundedPayloadPump := fun c =>
    ∀ K, ∃ t : Bool × Nat, K ≤ escapeSchema.payloadCount c t
  ExposesPayloadStrictly := fun c => c = true
  distinguished_exposed := rfl
  exposure_strict_count := by
    intro i hi
    subst i
    decide

/-- For every threshold `K`, the term `(false, K)` has at least `K` payload at the distinguished `true` coordinate. -/
theorem escapeFamily_hasUnboundedPayloadPump :
    escapeFamily.HasUnboundedPayloadPump escapeFamily.distinguishedPayload := by
  intro K
  exact ⟨(false, K), by simp [escapeFamily, escapeSchema]⟩

/-- This observer reads the `false` coordinate while the family marks `true` as distinguished. The dominance-based observer constructor requires dominance at `true`. -/
def escapePolynomialObserver : DirectWholeTermObserver escapeFamily where
  Carrier := Nat
  eval := fun t =>
    polynomialPayloadEval escapeTable (fun c => escapeFamily.schema.payloadCount c t)
  lt := fun m n => m < n
  visiblePayloadCoordinate := fun c => c = false
  carrierSensitive := fun c => c = false
  constructorLocal := True
  pumpMonotone := fun _ => True
  orient_forces_payload_drop := by
    intro i hVisible _hSensitive _hOriented
    subst i
    decide

/-- The escape observer evaluates the lhs to the low count-vector value. -/
theorem escapePolynomialObserver_eval_lhs :
    escapePolynomialObserver.eval escapeFamily.schema.lhs =
      polynomialPayloadEval escapeTable escapeCountsLow := rfl

/-- The escape observer evaluates the rhs to the high count-vector value. -/
theorem escapePolynomialObserver_eval_rhs :
    escapePolynomialObserver.eval escapeFamily.schema.rhs =
      polynomialPayloadEval escapeTable escapeCountsHigh := rfl

/-- **Family-level orienting escape.** The concrete polynomial observer globally orients the
singleton-step family even though the family's distinguished payload coordinate is duplicated. -/
theorem escapePolynomialObserver_globallyOrients :
    escapeFamily.GloballyOrients escapePolynomialObserver := by
  intro a b hStep
  rcases hStep with ⟨ha, hb⟩
  subst a
  subst b
  exact escapeTable_orients_pair

end OperatorKO7.StepDuplicating
