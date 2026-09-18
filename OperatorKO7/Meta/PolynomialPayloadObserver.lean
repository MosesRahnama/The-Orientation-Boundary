import OperatorKO7.Meta.PayloadExposureMatrix

/-!
# Polynomial payload observer: algebraic cross-monomial dominance

`Meta/MatrixOverPolynomialReduction.lean` carries an *abstract* `crossCoupled : Prop` field whose
only content is the witness the caller supplies. This module replaces that placeholder with a
concrete algebraic surface: a finite monomial table over payload-count coordinates, an explicit
cross-monomial witness type, and a dominance predicate defined from coefficients, exponents, and
positive monomial support alone.

## What "dominance" means here, and why it is not circular

`PolynomialPayloadDominates T i u v` says: a distinguished occurrence in the table has a positive
coefficient, carries coordinate `i` linearly, has positive cofactor support at `u`, does not lose
cofactor value from `u` to `v`, and the remainder of the table does not decrease in aggregate.
Every clause is an algebraic statement about a concrete table and two count vectors. The predicate
mentions no step relation, observer, or `GloballyOrients`; it is not `¬ GloballyOrients` in disguise.

The predicate is *consumed*: `polynomialPayloadEval_lt_of_dominates` uses the dominating monomial to
produce the strict increase, and that strict increase is what discharges the observer's
`orient_forces_payload_drop` certificate. Without dominance even non-orientation is false:
`escapeTable_orients_pair` is a concrete two-coordinate table whose target coordinate rises while
another coordinate falls, and whose value therefore strictly orients the pair in the forbidden
direction.

## Scope

The dominating monomial is required to carry the target coordinate *linearly* (`leftExp = 1`).
Monomials of higher degree in the target coordinate are inside the table and inside the
monotonicity theorem, but they do not by themselves serve as dominance witnesses here. That
restriction is deliberate and stated rather than hidden: it keeps every strictness step inside
`Nat.mul_lt_mul_of_pos_left`.

Relation: the `DuplicatingRecursiveFamily.Step` relation of the ambient family, single rule instance
`schema.lhs → schema.rhs`; the escape control instantiates a concrete singleton-step family.
Closure: root / single-step. This module makes no contextual-closure or `StepStar` claim.
Property: non-orientation (impossibility) for the induced direct whole-term observer.
Trust: Mathlib-only; no `sorry`, `admit`, new `axiom`, `native_decide`, `bv_decide`, `@[csimp]`,
`unsafe`, or `partial`.
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

/-! ## 3. Typed cross-monomial witness and algebraic dominance -/

/-- Typed witness that a monomial is genuinely cross-coupled: positive coefficient, both exponents
positive, and two distinct coordinates. This is the concrete replacement for the abstract
`crossCoupled : Prop` field of `MatrixOverPolynomial`. -/
structure CrossCoupledMonomial {C : Type} (m : PolynomialPayloadMonomial C) : Prop where
  /-- The monomial contributes with a positive coefficient. -/
  coeff_pos : 0 < m.coeff
  /-- The first coordinate is genuinely read. -/
  leftExp_pos : 0 < m.leftExp
  /-- The second coordinate is genuinely read. -/
  rightExp_pos : 0 < m.rightExp
  /-- The two coordinates are distinct, so the monomial couples two payload channels. -/
  coords_distinct : m.leftCoord ≠ m.rightCoord

/-- Typed witness that a single monomial dominates at coordinate `i` relative to a base count
vector. Every clause is algebraic: a coefficient positivity, a coordinate identification, an
exponent equation, and positivity of the cofactor's monomial support at the base vector. -/
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

/-- A dominating monomial strictly increases when its target coordinate strictly increases and no
coordinate decreases. This is where the dominance witness is consumed. -/
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

/-- Data for a polynomial payload observer over a duplicating recursive family: a finite monomial
table and an algebraic net-dominance witness at the family's distinguished coordinate, relative to
the left- and right-hand-side count vectors. -/
structure PolynomialPayloadObserverData (F : DuplicatingRecursiveFamily) where
  /-- The finite monomial table. -/
  table : PolynomialPayloadTable F.schema.PayloadCoord
  /-- Algebraic dominance at the distinguished coordinate, relative to the left-hand-side counts. -/
  dominates :
    PolynomialPayloadDominates table F.distinguishedPayload
      (fun c => F.schema.payloadCount c F.schema.lhs)
      (fun c => F.schema.payloadCount c F.schema.rhs)

/-- The rule strictly increases the value of a dominating table. The algebraic dominance witness
and the family's distinguished-coordinate strict-increase certificate are both consumed. -/
theorem polynomialPayloadObserverData_rule_strict_increase
    {F : DuplicatingRecursiveFamily} (D : PolynomialPayloadObserverData F) :
    polynomialPayloadEval D.table (fun c => F.schema.payloadCount c F.schema.lhs) <
      polynomialPayloadEval D.table (fun c => F.schema.payloadCount c F.schema.rhs) :=
  polynomialPayloadEval_lt_of_dominates F.distinguished_payload_count_strict D.table D.dominates

/-- The polynomial payload observer induced by dominance data.

Its `orient_forces_payload_drop` certificate is discharged by refuting its antecedent: a dominating
table strictly increases across the rule, so the observer can never strictly orient it. That
refutation is stated separately and non-vacuously as
`polynomialPayloadObserver_cannot_orient_rule`. -/
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

/-- **The dominating observer cannot strictly orient the rule instance.** Stated directly, so the
structural certificate above is not the only record of the fact. -/
theorem polynomialPayloadObserver_cannot_orient_rule
    {F : DuplicatingRecursiveFamily} (D : PolynomialPayloadObserverData F) :
    ¬ (polynomialPayloadEval D.table (fun c => F.schema.payloadCount c F.schema.rhs) <
        polynomialPayloadEval D.table (fun c => F.schema.payloadCount c F.schema.lhs)) := by
  have hrise := polynomialPayloadObserverData_rule_strict_increase D
  omega

/-- **Pump-free dominance theorem.** Algebraic net dominance already refutes global orientation at
the family's declared duplicating step. No pump hypothesis is needed for this one-step conclusion. -/
theorem polynomialPayloadObserver_no_global_orientation_withoutPump
    {F : DuplicatingRecursiveFamily} (D : PolynomialPayloadObserverData F) :
    ¬ F.GloballyOrients (polynomialPayloadObserver D) := by
  intro hOrient
  exact polynomialPayloadObserver_cannot_orient_rule D (hOrient F.duplicating_step)

/-- **Dominance-conditioned non-orientation.** A polynomial payload observer built from an
algebraic dominance witness cannot globally orient its family. The dominance predicate is used in
the proof, through `polynomialPayloadObserverData_rule_strict_increase`. -/
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

/-- The concrete monomial satisfies the typed cross-coupling witness. -/
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

/-- Non-vacuity: the concrete table satisfies the algebraic dominance predicate. -/
theorem crossCoupledTable_dominates :
    PolynomialPayloadDominates crossCoupledTable true unitCounts raisedTargetCounts := by
  refine ⟨[], crossCoupledMonomial, [], rfl, crossCoupledMonomial_dominatingAt, ?_, ?_⟩
  · decide
  · simp [polynomialPayloadEval]

/-- The positive control's table value rises strictly. -/
theorem crossCoupledTable_eval_strict_increase :
    polynomialPayloadEval crossCoupledTable unitCounts <
      polynomialPayloadEval crossCoupledTable raisedTargetCounts :=
  polynomialPayloadEval_lt_of_dominates unitCounts_target_lt _ crossCoupledTable_dominates

/-! ## 6. Concrete two-coordinate orienting escape that violates dominance

The control witness. The table reads only the `false` coordinate. From the low vector to the high
vector, `true` rises while `false` falls; the table therefore strictly decreases and orients the
pair in the termination direction. The table cannot satisfy dominance at `true`. This makes the
dominance hypothesis load-bearing for non-orientation rather than merely for a stronger inequality. -/

/-- Single-coordinate monomial `1 * count false ^ 1 * count false ^ 0`, blind to `true`. -/
def escapeMonomial : PolynomialPayloadMonomial Bool where
  coeff := 1
  leftCoord := false
  leftExp := 1
  rightCoord := false
  rightExp := 0

/-- The one-row escape table. -/
def escapeTable : PolynomialPayloadTable Bool := [escapeMonomial]

/-- Lhs counts for the escape control: both coordinates occur once. -/
def escapeCountsLow : Bool → Nat := fun _ => 1

/-- Rhs counts for the escape control: `true` rises to two while `false` falls to zero. -/
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

/-- The escape control is not merely a tie in one direction: the table fails to strictly increase,
which is exactly the conclusion `polynomialPayloadEval_lt_of_dominates` delivers under dominance. -/
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

/-- The escape retains the global theorem's pump hypothesis: at the distinguished `true`
coordinate, the natural parameter of `(false, K)` supplies counts above every threshold. -/
theorem escapeFamily_hasUnboundedPayloadPump :
    escapeFamily.HasUnboundedPayloadPump escapeFamily.distinguishedPayload := by
  intro K
  exact ⟨(false, K), by simp [escapeFamily, escapeSchema]⟩

/-- Polynomial-table observer for the escape family. It is visible and sensitive on the `false`
coordinate that the table actually reads. It is deliberately not a `polynomialPayloadObserver`,
because the latter requires dominance at the distinguished `true` coordinate. -/
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
