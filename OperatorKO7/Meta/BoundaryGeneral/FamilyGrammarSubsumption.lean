import OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure
import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.QuadraticBarrier_Schema
import OperatorKO7.Meta.QuadraticCrossTermBarrier_Schema
import OperatorKO7.Meta.MultilinearBarrier_Schema
import OperatorKO7.Meta.PolynomialBarrierGeneral_Schema
import OperatorKO7.Meta.MaxBarrier_Schema

/-!
# Attained-value subsumption carrier for the step-duplicating measure families

## What this module is for

The scalar grammar closure of `Meta/BoundaryGeneral/DirectMeasureGrammarClosure.lean` and the
enumerated step-duplicating family barriers (`AdditiveMeasure`, `AffineMeasure`,
`QuadraticCounterMeasure`, `CrossTermQuadraticMeasure`, `BoundedMultilinearMeasure`,
`BoundedPolynomialMeasure`, `MaxMeasure`) speak about different objects. The grammar closure is a
statement about the closed reflected syntax `MeasureExpr` on the canonical `(counter, payload)`
carrier; the family barriers are statements about record-valued constructor-local measures on an
arbitrary `StepDuplicatingSchema`. There is no pointwise embedding of the record families into
`MeasureExpr`, and this module does not attempt one.

What the two sides *do* share is a value-pair reading: at every index of the relevant binder tuple
there is a source value and a target value in `Nat`, and orientation is exactly `target < source` at
every index. That common reading is `AttainedValueFamily`, and it is the shared semantic layer this
module supplies.

## Choice discipline

`AttainedValueFamily` stores two `ι → Nat` functions and nothing else. It deliberately does **not**
store a selected global pump curve `Nat → S.T`, because manufacturing such a curve from
`∀ k, ∃ t, k ≤ M.eval t` requires `Classical.choose`. Every unbounded corollary below instead fixes
the threshold `K` first and then obtains one term locally with `rcases hunbounded K with ⟨s, hs⟩`.
The attained-carrier core and the seven per-family corollaries are therefore choice-free.

## Layer separation

`MeasureExpr` is a *proper syntax-restricted sublayer* of the attained carrier, and
`eval_counterMonotone` is the reason: every grammar denotation is nondecreasing in the counter
coordinate. Consequently a single grammar expression can never realize both frozen sections of a
family at ordered counters once a strict counter-reversal witness exists
(`no_grammar_sections_of_strict_reversal`). Each family below supplies that witness: unconditionally
for additive, affine, restricted quadratic and max, and under the family's own live side condition
for cross-term (`CrossTermBoundedAtBase`), multilinear (`MultilinearDominatedAtBase`), and
polynomial (an explicit strict reversal at some attained scalar).

Trust: Mathlib-only; no `sorry`, no `admit`, no new top-level `axiom`, no `native_decide`, no
`bv_decide`, no `@[csimp]`, no `unsafe`, no `partial`, and no `Classical.choose` anywhere in this
module.

Relation: schema-level duplicating root step `recur b s (succ n) → wrap s (recur b s n)`, and the
canonical `(counter, payload)` duplicating step of the grammar closure.
Closure: root / single-step only. Nothing here is a contextual-closure or `StepStar` statement.
Property: non-orientation (impossibility) of the duplicating step, plus adapter equivalences.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.FamilyGrammarSubsumption

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure

/-! ## 1. The choice-free attained value-pair carrier -/

/-- A family of attained source/target value pairs indexed by `ι`.

This records only the two `Nat`-valued readings at each index. It stores no term, no measure record,
and in particular no selected pump curve, so nothing in this structure can smuggle in a choice
function. -/
structure AttainedValueFamily (ι : Type) where
  /-- Attained value on the source side of the duplicating step. -/
  srcVal : ι → Nat
  /-- Attained value on the target side of the duplicating step. -/
  tgtVal : ι → Nat

/-- A value-pair family orients when the target value is strictly below the source value at every
index. This is the common reading of every duplicating-step orientation predicate below. -/
def OrientsAttained {ι : Type} (P : AttainedValueFamily ι) : Prop :=
  ∀ i, P.tgtVal i < P.srcVal i

/-! ## 2. Refutation principles on the shared carrier -/

/-- A single index at which the source value fails to exceed the target value refutes orientation. -/
theorem not_orientsAttained_at {ι : Type} {P : AttainedValueFamily ι} {i : ι}
    (h : P.srcVal i ≤ P.tgtVal i) : ¬ OrientsAttained P := by
  intro horients
  exact Nat.not_lt_of_ge h (horients i)

/-- Existential form: some index with a non-strict source/target reversal refutes orientation on the
attained carrier. -/
theorem not_orientsAttained_of_exists_le {ι : Type} {P : AttainedValueFamily ι}
    (h : ∃ i, P.srcVal i ≤ P.tgtVal i) : ¬ OrientsAttained P := by
  obtain ⟨i, hi⟩ := h
  exact not_orientsAttained_at hi

/-! ## 3. The grammar adapter -/

/-- The exact binder tuple of `DirectMeasureGrammarClosure.OrientsDupStep`: a counter, a payload,
and a strictly positive duplicated-copy size. Packaging the binders as an index type is what lets
the grammar side and the schema side share one carrier. -/
structure DupStepIndex where
  /-- Counter coordinate on the target side; the source side sits at `counter + 1`. -/
  counter : Nat
  /-- Payload coordinate before the duplicated copy is added. -/
  payload : Nat
  /-- Size of the duplicated payload copy. -/
  copy : Nat
  /-- The duplicated copy is nonempty, matching the `1 ≤ L` binder of `OrientsDupStep`. -/
  copy_pos : 1 ≤ copy

/-- Adapter from a scalar measure on the canonical `(counter, payload)` carrier into the attained
value-pair carrier. -/
def grammarFamily (m : Nat → Nat → Nat) : AttainedValueFamily DupStepIndex where
  srcVal := fun i => m (i.counter + 1) i.payload
  tgtVal := fun i => m i.counter (i.payload + i.copy)

@[simp] theorem grammarFamily_srcVal (m : Nat → Nat → Nat) (i : DupStepIndex) :
    (grammarFamily m).srcVal i = m (i.counter + 1) i.payload := rfl

@[simp] theorem grammarFamily_tgtVal (m : Nat → Nat → Nat) (i : DupStepIndex) :
    (grammarFamily m).tgtVal i = m i.counter (i.payload + i.copy) := rfl

/-- **Grammar adapter equivalence.** Orientation on the attained carrier is the same statement as
`OrientsDupStep`, binder for binder. -/
theorem grammarFamily_orientsAttained_iff (m : Nat → Nat → Nat) :
    OrientsAttained (grammarFamily m) ↔ OrientsDupStep m := by
  constructor
  · intro h c p L hL
    exact h ⟨c, p, L, hL⟩
  · intro h i
    exact h i.counter i.payload i.copy i.copy_pos

/-! ## 4. The schema adapter -/

/-- Adapter from any scalar evaluation on a step-duplicating schema into the attained value-pair
carrier, indexed by the `(b, s, n)` binder tuple of the family orientation predicates. -/
def schemaFamily {S : StepDuplicatingSchema} (eval : S.T → Nat) :
    AttainedValueFamily (S.T × S.T × S.T) where
  srcVal := fun t => eval (S.recur t.1 t.2.1 (S.succ t.2.2))
  tgtVal := fun t => eval (S.wrap t.2.1 (S.recur t.1 t.2.1 t.2.2))

@[simp] theorem schemaFamily_srcVal {S : StepDuplicatingSchema} (eval : S.T → Nat)
    (t : S.T × S.T × S.T) :
    (schemaFamily (S := S) eval).srcVal t = eval (S.recur t.1 t.2.1 (S.succ t.2.2)) := rfl

@[simp] theorem schemaFamily_tgtVal {S : StepDuplicatingSchema} (eval : S.T → Nat)
    (t : S.T × S.T × S.T) :
    (schemaFamily (S := S) eval).tgtVal t = eval (S.wrap t.2.1 (S.recur t.1 t.2.1 t.2.2)) := rfl

/-- **Schema adapter equivalence.** Orientation on the attained carrier is the same statement as the
literal duplicating-step orientation predicate shared by every family barrier in the stack. -/
theorem schemaFamily_orientsAttained_iff {S : StepDuplicatingSchema} (eval : S.T → Nat) :
    OrientsAttained (schemaFamily (S := S) eval) ↔
      (∀ (b s n : S.T), eval (S.wrap s (S.recur b s n)) < eval (S.recur b s (S.succ n))) := by
  constructor
  · intro h b s n
    exact h (b, s, n)
  · intro h t
    exact h t.1 t.2.1 t.2.2

/-- Refute a family orientation predicate from one attained non-strict reversal at
`(base, s, base)`. This is the single entry point used by all seven corollaries below. -/
theorem not_family_orients_of_base_reversal {S : StepDuplicatingSchema} (eval : S.T → Nat)
    {w : S.T}
    (h : eval (S.recur S.base w (S.succ S.base)) ≤ eval (S.wrap w (S.recur S.base w S.base))) :
    ¬ (∀ (b s n : S.T), eval (S.wrap s (S.recur b s n)) < eval (S.recur b s (S.succ n))) := by
  intro horients
  have hattained : OrientsAttained (schemaFamily (S := S) eval) :=
    (schemaFamily_orientsAttained_iff (S := S) eval).2 horients
  have hrev :
      (schemaFamily (S := S) eval).srcVal (S.base, w, S.base) ≤
        (schemaFamily (S := S) eval).tgtVal (S.base, w, S.base) := by
    simpa using h
  exact not_orientsAttained_at hrev hattained

/-! ## 5. Scalar-dominated vector orders: strict reversal is required -/

/-- Adapter from a vector measure together with a scalar functional into the attained carrier. -/
def vecScalarFamily {d : Nat} (M : VecMeasure d) (pi : (Fin d → Nat) → Nat) :
    AttainedValueFamily DupStepIndex where
  srcVal := fun i => pi (M.eval (i.counter + 1) i.payload)
  tgtVal := fun i => pi (M.eval i.counter (i.payload + i.copy))

@[simp] theorem vecScalarFamily_srcVal {d : Nat} (M : VecMeasure d)
    (pi : (Fin d → Nat) → Nat) (i : DupStepIndex) :
    (vecScalarFamily M pi).srcVal i = pi (M.eval (i.counter + 1) i.payload) := rfl

@[simp] theorem vecScalarFamily_tgtVal {d : Nat} (M : VecMeasure d)
    (pi : (Fin d → Nat) → Nat) (i : DupStepIndex) :
    (vecScalarFamily M pi).tgtVal i = pi (M.eval i.counter (i.payload + i.copy)) := rfl

/-- **Strict reversal refutes scalar-dominated vector orientation.**

A `DominatedByScalar` order only forces the scalar to *fail to increase* across the duplicating
step, so a non-strict reversal `srcVal ≤ tgtVal` is consistent with orientation and is not enough.
The witness must be strict: `srcVal i < tgtVal i`. -/
theorem not_vecOrients_of_strict_scalar_reversal {d : Nat}
    (M : VecMeasure d) (R : (Fin d → Nat) → (Fin d → Nat) → Prop)
    (pi : (Fin d → Nat) → Nat)
    (hdom : DominatedByScalar R pi)
    (hrev : ∃ i, (vecScalarFamily M pi).srcVal i < (vecScalarFamily M pi).tgtVal i) :
    ¬ VecOrients M R := by
  intro horients
  obtain ⟨i, hi⟩ := hrev
  simp only [vecScalarFamily_srcVal, vecScalarFamily_tgtVal] at hi
  have hle := hdom _ _ (horients i.counter i.payload i.copy i.copy_pos)
  exact Nat.not_lt_of_ge hle hi

/-! ## 6. The reusable dominance calculation, in the attained scalar -/

/-- **Attained-scalar dominance.** A coefficient gap of one makes the target-side affine reading
dominate the source-side affine reading for every sufficiently large *attained value* `x`.

The quantifier is over the attained scalar, never over a pump index: successor and wrapper iterates
of a schema may grow exponentially in their index, so no affine-in-index premise is available and
none is used. The threshold is explicit, `K := sourceConst`. -/
theorem attained_dominance_of_coeff_gap
    (sourceConst sourceCoeff targetConst targetCoeff : Nat)
    (hcoeff : sourceCoeff + 1 ≤ targetCoeff) :
    ∃ K : Nat, ∀ x : Nat, K ≤ x →
      sourceConst + sourceCoeff * x ≤ targetConst + targetCoeff * x := by
  refine ⟨sourceConst, ?_⟩
  intro x hx
  calc sourceConst + sourceCoeff * x
      ≤ x + sourceCoeff * x := Nat.add_le_add hx (Nat.le_refl (sourceCoeff * x))
    _ = (sourceCoeff + 1) * x := by ring
    _ ≤ targetCoeff * x := Nat.mul_le_mul_right x hcoeff
    _ ≤ targetConst + targetCoeff * x := Nat.le_add_left _ _

/-- Strict companion of `attained_dominance_of_coeff_gap`, used to build the counter-reversal
witnesses of the layer-separation theorems. One unit above the source constant turns non-strict
dominance into a strict reversal. -/
theorem attained_strict_reversal_of_coeff_gap
    (sourceConst sourceCoeff targetConst targetCoeff x : Nat)
    (hcoeff : sourceCoeff + 1 ≤ targetCoeff) (hx : sourceConst < x) :
    sourceConst + sourceCoeff * x < targetConst + targetCoeff * x := by
  calc sourceConst + sourceCoeff * x
      < x + sourceCoeff * x := Nat.add_lt_add_right hx (sourceCoeff * x)
    _ = (sourceCoeff + 1) * x := by ring
    _ ≤ targetCoeff * x := Nat.mul_le_mul_right x hcoeff
    _ ≤ targetConst + targetCoeff * x := Nat.le_add_left _ _

/-! ## 7. Counter monotonicity of the grammar, and the layer-separation principle -/

/-- **Grammar counter monotonicity.** Every reflected grammar measure is nondecreasing in the
counter coordinate, by structural induction over the seven constructors. This is the syntactic
restriction that makes `MeasureExpr` a proper sublayer of the attained carrier: a grammar denotation
can never reverse the counter order. -/
theorem eval_counterMonotone (e : MeasureExpr) :
    ∀ c c' p, c ≤ c' → e.eval c p ≤ e.eval c' p := by
  induction e with
  | counter => intro c c' p h; exact h
  | payload => intro c c' p _; exact Nat.le_refl p
  | const n => intro c c' p _; exact Nat.le_refl n
  | add e f ihe ihf =>
      intro c c' p h; exact Nat.add_le_add (ihe c c' p h) (ihf c c' p h)
  | mul e f ihe ihf =>
      intro c c' p h; exact Nat.mul_le_mul (ihe c c' p h) (ihf c c' p h)
  | max e f ihe ihf =>
      intro c c' p h; exact max_le_max (ihe c c' p h) (ihf c c' p h)
  | smul n e ihe =>
      intro c c' p h; exact Nat.mul_le_mul (Nat.le_refl n) (ihe c c' p h)

/-- **Layer separation.** Suppose a family's two frozen sections were simultaneously realized by a
single grammar expression `e`, the source section at counter `cSrc` and the target section at the
lower counter `cTgt`. Counter monotonicity then forces `tgt x ≤ src x` at every attained scalar, so
an explicit strict counter-reversal witness `src x < tgt x` makes that simultaneous agreement
impossible.

This is the exact sense in which `MeasureExpr` is a syntax-restricted sublayer: the attained carrier
hosts the family sections without restriction, while the grammar cannot host both of them at once. -/
theorem no_grammar_sections_of_strict_reversal
    (e : MeasureExpr) (cSrc cTgt : Nat) (hc : cTgt ≤ cSrc)
    (src tgt : Nat → Nat)
    (hsrc : ∀ x, src x = e.eval cSrc x) (htgt : ∀ x, tgt x = e.eval cTgt x)
    (x : Nat) (hrev : src x < tgt x) : False := by
  have hmono : e.eval cTgt x ≤ e.eval cSrc x := eval_counterMonotone e cTgt cSrc x hc
  rw [hsrc x, htgt x] at hrev
  exact Nat.not_lt_of_ge hmono hrev

/-! ## 8. Additive family -/

/-- Attained-carrier adapter for the additive family. -/
def additiveFamily {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    AttainedValueFamily (S.T × S.T × S.T) := schemaFamily (S := S) M.eval

theorem additiveFamily_orientsAttained_iff {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    OrientsAttained (additiveFamily M) ↔
      (∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  schemaFamily_orientsAttained_iff (S := S) M.eval

/-- Source section of the additive family, frozen at `b = n = base`, as a function of the attained
step value. -/
def additiveSourceSection {S : StepDuplicatingSchema} (M : AdditiveMeasure S) (x : Nat) : Nat :=
  (M.w_recur + M.w_base + (M.w_succ + M.w_base)) + 1 * x

/-- Target section of the additive family, frozen at `b = n = base`. The duplicated payload is why
the target reads the attained step value twice. -/
def additiveTargetSection {S : StepDuplicatingSchema} (M : AdditiveMeasure S) (x : Nat) : Nat :=
  (M.w_wrap + (M.w_recur + M.w_base + M.w_base)) + 2 * x

theorem additive_source_eval {S : StepDuplicatingSchema} (M : AdditiveMeasure S) (s : S.T) :
    M.eval (S.recur S.base s (S.succ S.base)) = additiveSourceSection M (M.eval s) := by
  rw [M.eval_recur, M.eval_succ, M.eval_base]
  simp only [additiveSourceSection]
  ring

theorem additive_target_eval {S : StepDuplicatingSchema} (M : AdditiveMeasure S) (s : S.T) :
    M.eval (S.wrap s (S.recur S.base s S.base)) = additiveTargetSection M (M.eval s) := by
  rw [M.eval_wrap, M.eval_recur, M.eval_base]
  simp only [additiveTargetSection]
  ring

/-- The additive coefficient gap is unconditional and carries no measure data: the source section
reads one copy of the attained step value and the target section reads two. -/
theorem additive_coeffGap : (1 : Nat) + 1 ≤ 2 := by omega

/-- Strict counter-reversal witness for the additive family. Unconditional. -/
theorem additive_strict_reversal {S : StepDuplicatingSchema} (M : AdditiveMeasure S)
    {x : Nat} (hx : M.w_recur + M.w_base + (M.w_succ + M.w_base) < x) :
    additiveSourceSection M x < additiveTargetSection M x := by
  simp only [additiveSourceSection, additiveTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ 1 _ 2 x additive_coeffGap hx

/-- **Additive corollary via the attained carrier.** Statement-preserving with respect to
`no_additive_orients_dup_step`: no unboundedness hypothesis, identical conclusion. The attained
value is produced locally from the wrapper iterate, never from a chosen curve. -/
theorem no_additive_orients_dup_step_via_attainedCarrier
    {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  obtain ⟨K, hK⟩ :=
    attained_dominance_of_coeff_gap
      (M.w_recur + M.w_base + (M.w_succ + M.w_base)) 1
      (M.w_wrap + (M.w_recur + M.w_base + M.w_base)) 2 additive_coeffGap
  have hattained : K ≤ M.eval (wrapIter S K) := eval_wrapIter_ge M K
  refine not_family_orients_of_base_reversal (S := S) M.eval (w := wrapIter S K) ?_
  rw [additive_source_eval, additive_target_eval]
  simp only [additiveSourceSection, additiveTargetSection]
  exact hK _ hattained

/-- Layer separation for the additive family: no single grammar expression realizes both frozen
sections at ordered counters. Unconditional. -/
theorem additive_sections_not_simultaneously_grammar
    {S : StepDuplicatingSchema} (M : AdditiveMeasure S)
    (e : MeasureExpr) (cSrc cTgt : Nat) (hc : cTgt ≤ cSrc)
    (hsrc : ∀ x, additiveSourceSection M x = e.eval cSrc x)
    (htgt : ∀ x, additiveTargetSection M x = e.eval cTgt x) : False :=
  no_grammar_sections_of_strict_reversal e cSrc cTgt hc
    (additiveSourceSection M) (additiveTargetSection M) hsrc htgt
    (M.w_recur + M.w_base + (M.w_succ + M.w_base) + 1)
    (additive_strict_reversal M (by omega))

/-! ## 9. Affine family -/

/-- Attained-carrier adapter for the affine family. -/
def affineFamily {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    AttainedValueFamily (S.T × S.T × S.T) := schemaFamily (S := S) M.eval

theorem affineFamily_orientsAttained_iff {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    OrientsAttained (affineFamily M) ↔
      (∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  schemaFamily_orientsAttained_iff (S := S) M.eval

/-- Frozen source constant of the affine family. -/
def affineSourceConst {S : StepDuplicatingSchema} (M : AffineMeasure S) : Nat :=
  M.recur_const + M.recur_base * M.c_base +
    M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)

/-- Frozen target constant of the affine family. -/
def affineTargetConst {S : StepDuplicatingSchema} (M : AffineMeasure S) : Nat :=
  M.wrap_const +
    M.wrap_right * (M.recur_const + M.recur_base * M.c_base + M.recur_counter * M.c_base)

/-- Frozen target coefficient of the affine family: the wrapper keeps its own visible copy of the
attained step value on top of the recursive one. -/
def affineTargetCoeff {S : StepDuplicatingSchema} (M : AffineMeasure S) : Nat :=
  M.wrap_left + M.wrap_right * M.recur_step

/-- Frozen source section of the affine family. -/
def affineSourceSection {S : StepDuplicatingSchema} (M : AffineMeasure S) (x : Nat) : Nat :=
  affineSourceConst M + M.recur_step * x

/-- Frozen target section of the affine family. -/
def affineTargetSection {S : StepDuplicatingSchema} (M : AffineMeasure S) (x : Nat) : Nat :=
  affineTargetConst M + affineTargetCoeff M * x

theorem affine_source_eval {S : StepDuplicatingSchema} (M : AffineMeasure S) (s : S.T) :
    M.eval (S.recur S.base s (S.succ S.base)) = affineSourceSection M (M.eval s) := by
  rw [M.eval_recur, M.eval_succ, M.eval_base]
  simp only [affineSourceSection, affineSourceConst]
  ring

theorem affine_target_eval {S : StepDuplicatingSchema} (M : AffineMeasure S) (s : S.T) :
    M.eval (S.wrap s (S.recur S.base s S.base)) = affineTargetSection M (M.eval s) := by
  rw [M.eval_wrap, M.eval_recur, M.eval_base]
  simp only [affineTargetSection, affineTargetConst, affineTargetCoeff]
  ring

/-- The affine coefficient gap is unconditional: it follows from the two positive wrapper
coefficients already required by the `AffineMeasure` record. -/
theorem affine_coeffGap {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    M.recur_step + 1 ≤ affineTargetCoeff M := by
  have hone : 1 * M.recur_step ≤ M.wrap_right * M.recur_step :=
    Nat.mul_le_mul_right M.recur_step M.h_wrap_right_pos
  have hleft : 1 ≤ M.wrap_left := M.h_wrap_left_pos
  simp only [affineTargetCoeff]
  omega

/-- Strict counter-reversal witness for the affine family. Unconditional. -/
theorem affine_strict_reversal {S : StepDuplicatingSchema} (M : AffineMeasure S)
    {x : Nat} (hx : affineSourceConst M < x) :
    affineSourceSection M x < affineTargetSection M x := by
  simp only [affineSourceSection, affineTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ _ _ _ x (affine_coeffGap M) hx

/-- **Affine corollary via the attained carrier.** Statement-preserving with respect to
`no_affine_orients_dup_step_of_unbounded`, including the `HasUnboundedRange` premise verbatim. -/
theorem no_affine_orients_dup_step_of_unbounded_via_attainedCarrier
    {S : StepDuplicatingSchema} (M : AffineMeasure S) (hunbounded : HasUnboundedRange M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  obtain ⟨K, hK⟩ :=
    attained_dominance_of_coeff_gap (affineSourceConst M) M.recur_step
      (affineTargetConst M) (affineTargetCoeff M) (affine_coeffGap M)
  rcases hunbounded K with ⟨s, hs⟩
  refine not_family_orients_of_base_reversal (S := S) M.eval (w := s) ?_
  rw [affine_source_eval, affine_target_eval]
  simp only [affineSourceSection, affineTargetSection]
  exact hK _ hs

/-- Layer separation for the affine family. Unconditional. -/
theorem affine_sections_not_simultaneously_grammar
    {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (e : MeasureExpr) (cSrc cTgt : Nat) (hc : cTgt ≤ cSrc)
    (hsrc : ∀ x, affineSourceSection M x = e.eval cSrc x)
    (htgt : ∀ x, affineTargetSection M x = e.eval cTgt x) : False :=
  no_grammar_sections_of_strict_reversal e cSrc cTgt hc
    (affineSourceSection M) (affineTargetSection M) hsrc htgt
    (affineSourceConst M + 1) (affine_strict_reversal M (by omega))

/-! ## 10. Restricted quadratic family -/

/-- Attained-carrier adapter for the restricted quadratic family. -/
def quadraticFamily {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S) :
    AttainedValueFamily (S.T × S.T × S.T) := schemaFamily (S := S) M.eval

theorem quadraticFamily_orientsAttained_iff {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) :
    OrientsAttained (quadraticFamily M) ↔
      (∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  schemaFamily_orientsAttained_iff (S := S) M.eval

/-- Frozen source constant of the restricted quadratic family. The pure counter-square term is
frozen here and contributes nothing to the attained step coefficient. -/
def quadraticSourceConst {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S) : Nat :=
  M.recur_const + M.recur_base * M.c_base +
    M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) +
    M.recur_quad * (M.succ_bias + M.succ_scale * M.c_base) *
      (M.succ_bias + M.succ_scale * M.c_base)

/-- Frozen target constant of the restricted quadratic family. -/
def quadraticTargetConst {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S) : Nat :=
  M.wrap_const +
    M.wrap_right * (M.recur_const + M.recur_base * M.c_base + M.recur_counter * M.c_base +
      M.recur_quad * M.c_base * M.c_base)

/-- Frozen target coefficient of the restricted quadratic family. -/
def quadraticTargetCoeff {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S) : Nat :=
  M.wrap_left + M.wrap_right * M.recur_step

/-- Frozen source section of the restricted quadratic family. -/
def quadraticSourceSection {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) (x : Nat) : Nat :=
  quadraticSourceConst M + M.recur_step * x

/-- Frozen target section of the restricted quadratic family. -/
def quadraticTargetSection {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) (x : Nat) : Nat :=
  quadraticTargetConst M + quadraticTargetCoeff M * x

theorem quadratic_source_eval {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (s : S.T) :
    M.eval (S.recur S.base s (S.succ S.base)) = quadraticSourceSection M (M.eval s) := by
  rw [M.eval_recur, M.eval_succ, M.eval_base]
  simp only [quadraticSourceSection, quadraticSourceConst]
  ring

theorem quadratic_target_eval {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (s : S.T) :
    M.eval (S.wrap s (S.recur S.base s S.base)) = quadraticTargetSection M (M.eval s) := by
  rw [M.eval_wrap, M.eval_recur, M.eval_base]
  simp only [quadraticTargetSection, quadraticTargetConst, quadraticTargetCoeff]
  ring

/-- The restricted quadratic coefficient gap is unconditional. -/
theorem quadratic_coeffGap {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S) :
    M.recur_step + 1 ≤ quadraticTargetCoeff M := by
  have hone : 1 * M.recur_step ≤ M.wrap_right * M.recur_step :=
    Nat.mul_le_mul_right M.recur_step M.h_wrap_right_pos
  have hleft : 1 ≤ M.wrap_left := M.h_wrap_left_pos
  simp only [quadraticTargetCoeff]
  omega

/-- Strict counter-reversal witness for the restricted quadratic family. Unconditional. -/
theorem quadratic_strict_reversal {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    {x : Nat} (hx : quadraticSourceConst M < x) :
    quadraticSourceSection M x < quadraticTargetSection M x := by
  simp only [quadraticSourceSection, quadraticTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ _ _ _ x (quadratic_coeffGap M) hx

/-- **Restricted quadratic corollary via the attained carrier.** Statement-preserving with respect
to `no_quadratic_counter_orients_dup_step_of_unbounded`. -/
theorem no_quadratic_counter_orients_dup_step_of_unbounded_via_attainedCarrier
    {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (hunbounded : HasUnboundedRangeQ M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  obtain ⟨K, hK⟩ :=
    attained_dominance_of_coeff_gap (quadraticSourceConst M) M.recur_step
      (quadraticTargetConst M) (quadraticTargetCoeff M) (quadratic_coeffGap M)
  rcases hunbounded K with ⟨s, hs⟩
  refine not_family_orients_of_base_reversal (S := S) M.eval (w := s) ?_
  rw [quadratic_source_eval, quadratic_target_eval]
  simp only [quadraticSourceSection, quadraticTargetSection]
  exact hK _ hs

/-- Layer separation for the restricted quadratic family. Unconditional. -/
theorem quadratic_sections_not_simultaneously_grammar
    {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (e : MeasureExpr) (cSrc cTgt : Nat) (hc : cTgt ≤ cSrc)
    (hsrc : ∀ x, quadraticSourceSection M x = e.eval cSrc x)
    (htgt : ∀ x, quadraticTargetSection M x = e.eval cTgt x) : False :=
  no_grammar_sections_of_strict_reversal e cSrc cTgt hc
    (quadraticSourceSection M) (quadraticTargetSection M) hsrc htgt
    (quadraticSourceConst M + 1) (quadratic_strict_reversal M (by omega))

/-! ## 11. Bounded cross-term quadratic family -/

/-- Attained-carrier adapter for the bounded cross-term quadratic family. -/
def crossTermFamily {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S) :
    AttainedValueFamily (S.T × S.T × S.T) := schemaFamily (S := S) M.eval

theorem crossTermFamily_orientsAttained_iff {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) :
    OrientsAttained (crossTermFamily M) ↔
      (∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  schemaFamily_orientsAttained_iff (S := S) M.eval

/-- Frozen source constant of the bounded cross-term family. -/
def crossTermSourceConst {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S) : Nat :=
  M.recur_const + M.recur_base * M.c_base +
    M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) +
    M.recur_quad * (M.succ_bias + M.succ_scale * M.c_base) *
      (M.succ_bias + M.succ_scale * M.c_base)

/-- Frozen source coefficient of the bounded cross-term family: the cross term contributes the
source counter value to the attained step coefficient. -/
def crossTermSourceCoeff {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S) : Nat :=
  M.recur_step + M.recur_cross * (M.succ_bias + M.succ_scale * M.c_base)

/-- Frozen target constant of the bounded cross-term family. -/
def crossTermTargetConst {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S) : Nat :=
  M.wrap_const +
    M.wrap_right * (M.recur_const + M.recur_base * M.c_base + M.recur_counter * M.c_base +
      M.recur_quad * M.c_base * M.c_base)

/-- Frozen target coefficient of the bounded cross-term family. -/
def crossTermTargetCoeff {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S) : Nat :=
  M.wrap_left + M.wrap_right * (M.recur_step + M.recur_cross * M.c_base)

/-- Frozen source section of the bounded cross-term family. -/
def crossTermSourceSection {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) (x : Nat) : Nat :=
  crossTermSourceConst M + crossTermSourceCoeff M * x

/-- Frozen target section of the bounded cross-term family. -/
def crossTermTargetSection {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) (x : Nat) : Nat :=
  crossTermTargetConst M + crossTermTargetCoeff M * x

theorem crossTerm_source_eval {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (s : S.T) :
    M.eval (S.recur S.base s (S.succ S.base)) = crossTermSourceSection M (M.eval s) := by
  rw [M.eval_recur, M.eval_succ, M.eval_base]
  simp only [crossTermSourceSection, crossTermSourceConst, crossTermSourceCoeff]
  ring

theorem crossTerm_target_eval {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (s : S.T) :
    M.eval (S.wrap s (S.recur S.base s S.base)) = crossTermTargetSection M (M.eval s) := by
  rw [M.eval_wrap, M.eval_recur, M.eval_base]
  simp only [crossTermTargetSection, crossTermTargetConst, crossTermTargetCoeff]
  ring

/-- The cross-term coefficient gap **is** the live `CrossTermBoundedAtBase` side condition, kept
verbatim. It is not discharged unconditionally, and no weaker substitute is used. -/
theorem crossTerm_coeffGap {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (hbounded : CrossTermBoundedAtBase M) :
    crossTermSourceCoeff M + 1 ≤ crossTermTargetCoeff M := by
  simp only [crossTermSourceCoeff, crossTermTargetCoeff]
  simpa [CrossTermBoundedAtBase] using hbounded

/-- Strict counter-reversal witness for the cross-term family, under `CrossTermBoundedAtBase`. -/
theorem crossTerm_strict_reversal {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (hbounded : CrossTermBoundedAtBase M)
    {x : Nat} (hx : crossTermSourceConst M < x) :
    crossTermSourceSection M x < crossTermTargetSection M x := by
  simp only [crossTermSourceSection, crossTermTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ _ _ _ x (crossTerm_coeffGap M hbounded) hx

/-- **Bounded cross-term corollary via the attained carrier.** Statement-preserving with respect to
`no_cross_quadratic_orients_dup_step_of_unbounded`, with both premises verbatim. -/
theorem no_cross_quadratic_orients_dup_step_of_unbounded_via_attainedCarrier
    {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (hunbounded : HasUnboundedRangeX M)
    (hbounded : CrossTermBoundedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  obtain ⟨K, hK⟩ :=
    attained_dominance_of_coeff_gap (crossTermSourceConst M) (crossTermSourceCoeff M)
      (crossTermTargetConst M) (crossTermTargetCoeff M) (crossTerm_coeffGap M hbounded)
  rcases hunbounded K with ⟨s, hs⟩
  refine not_family_orients_of_base_reversal (S := S) M.eval (w := s) ?_
  rw [crossTerm_source_eval, crossTerm_target_eval]
  simp only [crossTermSourceSection, crossTermTargetSection]
  exact hK _ hs

/-- Layer separation for the cross-term family, under `CrossTermBoundedAtBase`. -/
theorem crossTerm_sections_not_simultaneously_grammar
    {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (hbounded : CrossTermBoundedAtBase M)
    (e : MeasureExpr) (cSrc cTgt : Nat) (hc : cTgt ≤ cSrc)
    (hsrc : ∀ x, crossTermSourceSection M x = e.eval cSrc x)
    (htgt : ∀ x, crossTermTargetSection M x = e.eval cTgt x) : False :=
  no_grammar_sections_of_strict_reversal e cSrc cTgt hc
    (crossTermSourceSection M) (crossTermTargetSection M) hsrc htgt
    (crossTermSourceConst M + 1)
    (crossTerm_strict_reversal M hbounded (by omega))

/-! ## 12. Bounded multilinear family -/

/-- Attained-carrier adapter for the bounded multilinear family. -/
def multilinearFamily {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S) :
    AttainedValueFamily (S.T × S.T × S.T) := schemaFamily (S := S) M.eval

theorem multilinearFamily_orientsAttained_iff {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) :
    OrientsAttained (multilinearFamily M) ↔
      (∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  schemaFamily_orientsAttained_iff (S := S) M.eval

/-- Frozen source constant of the bounded multilinear family. -/
def multilinearSourceConst {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) : Nat :=
  M.recur_const + M.recur_base * M.c_base +
    M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) +
    M.constPartSum M.c_base (M.succ_bias + M.succ_scale * M.c_base)

/-- Frozen source coefficient of the bounded multilinear family. -/
def multilinearSourceCoeff {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) : Nat :=
  M.recur_step + M.stepCoeffSum M.c_base (M.succ_bias + M.succ_scale * M.c_base)

/-- Frozen target constant of the bounded multilinear family. -/
def multilinearTargetConst {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) : Nat :=
  M.wrap_const +
    M.wrap_right * (M.recur_const + M.recur_base * M.c_base + M.recur_counter * M.c_base +
      M.constPartSum M.c_base M.c_base)

/-- Frozen target coefficient of the bounded multilinear family. -/
def multilinearTargetCoeff {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) : Nat :=
  M.wrap_left + M.wrap_right * (M.recur_step + M.stepCoeffSum M.c_base M.c_base)

/-- Frozen source section of the bounded multilinear family. -/
def multilinearSourceSection {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (x : Nat) : Nat :=
  multilinearSourceConst M + multilinearSourceCoeff M * x

/-- Frozen target section of the bounded multilinear family. -/
def multilinearTargetSection {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (x : Nat) : Nat :=
  multilinearTargetConst M + multilinearTargetCoeff M * x

theorem multilinear_source_eval {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (s : S.T) :
    M.eval (S.recur S.base s (S.succ S.base)) = multilinearSourceSection M (M.eval s) := by
  rw [M.eval_recur, M.eval_succ, M.eval_base, M.monomialSum_eq_constPart_add_stepCoeff]
  simp only [multilinearSourceSection, multilinearSourceConst, multilinearSourceCoeff]
  ring

theorem multilinear_target_eval {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (s : S.T) :
    M.eval (S.wrap s (S.recur S.base s S.base)) = multilinearTargetSection M (M.eval s) := by
  rw [M.eval_wrap, M.eval_recur, M.eval_base, M.monomialSum_eq_constPart_add_stepCoeff]
  simp only [multilinearTargetSection, multilinearTargetConst, multilinearTargetCoeff]
  ring

/-- The multilinear coefficient gap **is** the live `MultilinearDominatedAtBase` side condition,
kept verbatim. -/
theorem multilinear_coeffGap {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (hdom : MultilinearDominatedAtBase M) :
    multilinearSourceCoeff M + 1 ≤ multilinearTargetCoeff M := by
  simp only [multilinearSourceCoeff, multilinearTargetCoeff]
  simpa [MultilinearDominatedAtBase] using hdom

/-- Strict counter-reversal witness for the multilinear family, under
`MultilinearDominatedAtBase`. -/
theorem multilinear_strict_reversal {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (hdom : MultilinearDominatedAtBase M)
    {x : Nat} (hx : multilinearSourceConst M < x) :
    multilinearSourceSection M x < multilinearTargetSection M x := by
  simp only [multilinearSourceSection, multilinearTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ _ _ _ x (multilinear_coeffGap M hdom) hx

/-- **Bounded multilinear corollary via the attained carrier.** Statement-preserving with respect to
`no_multilinear_orients_dup_step_of_unbounded`, with both premises verbatim. -/
theorem no_multilinear_orients_dup_step_of_unbounded_via_attainedCarrier
    {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (hunbounded : HasUnboundedRangeML M)
    (hdom : MultilinearDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  obtain ⟨K, hK⟩ :=
    attained_dominance_of_coeff_gap (multilinearSourceConst M) (multilinearSourceCoeff M)
      (multilinearTargetConst M) (multilinearTargetCoeff M) (multilinear_coeffGap M hdom)
  rcases hunbounded K with ⟨s, hs⟩
  refine not_family_orients_of_base_reversal (S := S) M.eval (w := s) ?_
  rw [multilinear_source_eval, multilinear_target_eval]
  simp only [multilinearSourceSection, multilinearTargetSection]
  exact hK _ hs

/-- Layer separation for the multilinear family, under `MultilinearDominatedAtBase`. -/
theorem multilinear_sections_not_simultaneously_grammar
    {S : StepDuplicatingSchema} (M : BoundedMultilinearMeasure S)
    (hdom : MultilinearDominatedAtBase M)
    (e : MeasureExpr) (cSrc cTgt : Nat) (hc : cTgt ≤ cSrc)
    (hsrc : ∀ x, multilinearSourceSection M x = e.eval cSrc x)
    (htgt : ∀ x, multilinearTargetSection M x = e.eval cTgt x) : False :=
  no_grammar_sections_of_strict_reversal e cSrc cTgt hc
    (multilinearSourceSection M) (multilinearTargetSection M) hsrc htgt
    (multilinearSourceConst M + 1)
    (multilinear_strict_reversal M hdom (by omega))

/-! ## 13. Generalized polynomial family -/

/-- Attained-carrier adapter for the generalized polynomial family. -/
def polynomialFamily {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S) :
    AttainedValueFamily (S.T × S.T × S.T) := schemaFamily (S := S) M.eval

theorem polynomialFamily_orientsAttained_iff {S : StepDuplicatingSchema}
    (M : BoundedPolynomialMeasure S) :
    OrientsAttained (polynomialFamily M) ↔
      (∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  schemaFamily_orientsAttained_iff (S := S) M.eval

theorem polynomial_source_eval {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (s : S.T) :
    M.eval (S.recur S.base s (S.succ S.base)) = M.sourceFrozenAtBase (M.eval s) := by
  rw [M.eval_recur, M.eval_succ, M.eval_base]
  simp [BoundedPolynomialMeasure.sourceFrozenAtBase, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm, Nat.mul_add]

theorem polynomial_target_eval {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (s : S.T) :
    M.eval (S.wrap s (S.recur S.base s S.base)) = M.targetFrozenAtBase (M.eval s) := by
  rw [M.eval_wrap, M.eval_recur, M.eval_base]
  simp [BoundedPolynomialMeasure.targetFrozenAtBase, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm, Nat.mul_add]

/-- **Generalized polynomial corollary via the attained carrier.** Arbitrary exponents leave no
coefficient algebra, so the live `EventuallyDominatedAtBase` premise is consumed directly and kept
verbatim. Statement-preserving with respect to `no_polynomial_orients_dup_step_of_unbounded`. -/
theorem no_polynomial_orients_dup_step_of_unbounded_via_attainedCarrier
    {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (hunbounded : HasUnboundedRangePoly M)
    (hdom : EventuallyDominatedAtBase M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  obtain ⟨K, hK⟩ := hdom
  rcases hunbounded K with ⟨s, hs⟩
  refine not_family_orients_of_base_reversal (S := S) M.eval (w := s) ?_
  rw [polynomial_source_eval, polynomial_target_eval]
  exact hK (M.eval s) hs

/-- Layer separation for the generalized polynomial family. Arbitrary exponents leave no
unconditional coefficient gap, so an explicit strict counter-reversal witness at some attained
scalar is required and is taken as a hypothesis. -/
theorem polynomial_sections_not_simultaneously_grammar
    {S : StepDuplicatingSchema} (M : BoundedPolynomialMeasure S)
    (hrev : ∃ x, M.sourceFrozenAtBase x < M.targetFrozenAtBase x)
    (e : MeasureExpr) (cSrc cTgt : Nat) (hc : cTgt ≤ cSrc)
    (hsrc : ∀ x, M.sourceFrozenAtBase x = e.eval cSrc x)
    (htgt : ∀ x, M.targetFrozenAtBase x = e.eval cTgt x) : False := by
  obtain ⟨x, hx⟩ := hrev
  exact no_grammar_sections_of_strict_reversal e cSrc cTgt hc
    (fun y => M.sourceFrozenAtBase y) (fun y => M.targetFrozenAtBase y) hsrc htgt x hx

/-! ## 14. Max-plus family -/

/-- Attained-carrier adapter for the max-plus family. -/
def maxFamily {S : StepDuplicatingSchema} (M : MaxMeasure S) :
    AttainedValueFamily (S.T × S.T × S.T) := schemaFamily (S := S) M.eval

theorem maxFamily_orientsAttained_iff {S : StepDuplicatingSchema} (M : MaxMeasure S) :
    OrientsAttained (maxFamily M) ↔
      (∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  schemaFamily_orientsAttained_iff (S := S) M.eval

/-- Branch-stabilization threshold for the max family: above it both frozen recursor maxima select
the step branch. -/
def maxThreshold {S : StepDuplicatingSchema} (M : MaxMeasure S) : Nat :=
  max (M.recur_base + M.c_base) (M.recur_counter + (M.succ_const + M.c_base))

/-- Frozen source section of the max-plus family. -/
def maxSourceSection {S : StepDuplicatingSchema} (M : MaxMeasure S) (x : Nat) : Nat :=
  M.recur_const +
    max (M.recur_base + M.c_base)
      (max (M.recur_step + x) (M.recur_counter + (M.succ_const + M.c_base)))

/-- Frozen target section of the max-plus family. -/
def maxTargetSection {S : StepDuplicatingSchema} (M : MaxMeasure S) (x : Nat) : Nat :=
  M.wrap_const +
    max (M.wrap_left + x)
      (M.wrap_right +
        (M.recur_const +
          max (M.recur_base + M.c_base)
            (max (M.recur_step + x) (M.recur_counter + M.c_base))))

theorem max_source_eval {S : StepDuplicatingSchema} (M : MaxMeasure S) (s : S.T) :
    M.eval (S.recur S.base s (S.succ S.base)) = maxSourceSection M (M.eval s) := by
  simp only [M.eval_recur, M.eval_succ, M.eval_base, maxSourceSection]

theorem max_target_eval {S : StepDuplicatingSchema} (M : MaxMeasure S) (s : S.T) :
    M.eval (S.wrap s (S.recur S.base s S.base)) = maxTargetSection M (M.eval s) := by
  simp only [M.eval_wrap, M.eval_recur, M.eval_base, maxTargetSection]

/-- Above the stabilization threshold the frozen source max selects the step branch. -/
theorem maxSourceSection_stabilized {S : StepDuplicatingSchema} (M : MaxMeasure S)
    {x : Nat} (hx : maxThreshold M ≤ x) :
    maxSourceSection M x = M.recur_const + (M.recur_step + x) := by
  have h0 : M.recur_base + M.c_base ≤ maxThreshold M := le_max_left _ _
  have h1 : M.recur_counter + (M.succ_const + M.c_base) ≤ maxThreshold M := le_max_right _ _
  have hb : M.recur_base + M.c_base ≤ M.recur_step + x := by omega
  have hc : M.recur_counter + (M.succ_const + M.c_base) ≤ M.recur_step + x := by omega
  simp only [maxSourceSection]
  rw [max_eq_left hc, max_eq_right hb]

/-- **Max branch stabilization gives a strict counter reversal.** Above the threshold both frozen
recursor maxima select the step branch, so the wrapper keeps a visible copy of the same stabilized
branch and adds its positive right offset: the target strictly exceeds the source. Unconditional
given the `MaxMeasure` record's positive right-wrapper offset. -/
theorem max_strict_reversal {S : StepDuplicatingSchema} (M : MaxMeasure S)
    {x : Nat} (hx : maxThreshold M ≤ x) :
    maxSourceSection M x < maxTargetSection M x := by
  have h0 : M.recur_base + M.c_base ≤ maxThreshold M := le_max_left _ _
  have h1 : M.recur_counter + (M.succ_const + M.c_base) ≤ maxThreshold M := le_max_right _ _
  have hb : M.recur_base + M.c_base ≤ M.recur_step + x := by omega
  have hc' : M.recur_counter + M.c_base ≤ M.recur_step + x := by omega
  have hinner :
      max (M.recur_base + M.c_base) (max (M.recur_step + x) (M.recur_counter + M.c_base)) =
        M.recur_step + x := by
    rw [max_eq_left hc', max_eq_right hb]
  have htail :
      M.wrap_right + (M.recur_const + (M.recur_step + x)) ≤
        max (M.wrap_left + x) (M.wrap_right + (M.recur_const + (M.recur_step + x))) :=
    le_max_right _ _
  have hpos : 1 ≤ M.wrap_right := M.h_wrap_right_pos
  rw [maxSourceSection_stabilized M hx]
  simp only [maxTargetSection]
  rw [hinner]
  omega

/-- **Max-plus corollary via the attained carrier.** Statement-preserving with respect to
`no_max_orients_dup_step_of_unbounded`, with the `HasUnboundedRangeMax` premise verbatim. The
attained value is obtained locally once the branch-stabilization threshold is fixed. -/
theorem no_max_orients_dup_step_of_unbounded_via_attainedCarrier
    {S : StepDuplicatingSchema} (M : MaxMeasure S)
    (hunbounded : HasUnboundedRangeMax M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  rcases hunbounded (maxThreshold M) with ⟨s, hs⟩
  refine not_family_orients_of_base_reversal (S := S) M.eval (w := s) ?_
  rw [max_source_eval, max_target_eval]
  exact Nat.le_of_lt (max_strict_reversal M hs)

/-- Layer separation for the max family. Unconditional: the branch-stabilization threshold itself is
a strict counter-reversal witness. -/
theorem max_sections_not_simultaneously_grammar
    {S : StepDuplicatingSchema} (M : MaxMeasure S)
    (e : MeasureExpr) (cSrc cTgt : Nat) (hc : cTgt ≤ cSrc)
    (hsrc : ∀ x, maxSourceSection M x = e.eval cSrc x)
    (htgt : ∀ x, maxTargetSection M x = e.eval cTgt x) : False :=
  no_grammar_sections_of_strict_reversal e cSrc cTgt hc
    (maxSourceSection M) (maxTargetSection M) hsrc htgt
    (maxThreshold M) (max_strict_reversal M (Nat.le_refl _))

/-! ## 15. Strict scalar-reversal transport for the vector orders

These are transport corollaries only. They consume a strict reversal of the *scalar* reading and
refute vector orientation. No claim is made that a `VecMeasure` agrees with any single grammar
expression, and none is needed. -/

/-- **Componentwise transport.** A strict reversal in any single coordinate refutes componentwise
vector orientation. -/
theorem not_vecOrients_componentwise_of_strict_coordinate_reversal {d : Nat}
    (M : VecMeasure d) (i : Fin d)
    (hrev : ∃ k : DupStepIndex,
      M.eval (k.counter + 1) k.payload i < M.eval k.counter (k.payload + k.copy) i) :
    ¬ VecOrients M VecLt := by
  refine not_vecOrients_of_strict_scalar_reversal M VecLt (fun u => u i)
    (vecLt_dominatedByScalar i) ?_
  obtain ⟨k, hk⟩ := hrev
  exact ⟨k, by simpa using hk⟩

/-- **Tracked-primary lexicographic transport.** A strict reversal in the designated primary
coordinate refutes primary-first vector orientation. -/
theorem not_vecOrients_primaryFirst_of_strict_primary_reversal {d : Nat}
    (M : VecMeasure d) (i : Fin d)
    (hrev : ∃ k : DupStepIndex,
      M.eval (k.counter + 1) k.payload i < M.eval k.counter (k.payload + k.copy) i) :
    ¬ VecOrients M (PrimaryFirstLt i) := by
  refine not_vecOrients_of_strict_scalar_reversal M (PrimaryFirstLt i) (fun u => u i)
    (primaryFirstLt_dominatedByScalar i) ?_
  obtain ⟨k, hk⟩ := hrev
  exact ⟨k, by simpa using hk⟩

/-- **Weighted-projection transport.** A strict reversal in a natural-weighted coordinate sum
refutes orientation under any ambient order dominated by that sum. This covers fixed-row readings
(a singleton list with unit weight) and row sums (the full coordinate list, all weights one). -/
theorem not_vecOrients_weighted_of_strict_weighted_reversal {d : Nat}
    (M : VecMeasure d) (w : Fin d → Nat) (l : List (Fin d))
    (R : (Fin d → Nat) → (Fin d → Nat) → Prop)
    (hdom : DominatedByScalar R (weightedProj w l))
    (hrev : ∃ k : DupStepIndex,
      weightedProj w l (M.eval (k.counter + 1) k.payload) <
        weightedProj w l (M.eval k.counter (k.payload + k.copy))) :
    ¬ VecOrients M R := by
  refine not_vecOrients_of_strict_scalar_reversal M R (weightedProj w l) hdom ?_
  obtain ⟨k, hk⟩ := hrev
  exact ⟨k, by simpa using hk⟩

/-! ## 16. Comparison capstones -/

/-- **Carrier comparison.** Both the grammar side and the schema side land in the same attained
value-pair carrier, with orientation preserved and reflected in each case. This is the precise sense
in which the attained carrier is the shared semantic layer of the two developments.

The grammar leg and the schema leg are separate biconditionals; nothing here identifies a record
family with a `MeasureExpr`. -/
theorem attainedCarrier_is_shared_layer :
    (∀ m : Nat → Nat → Nat, OrientsAttained (grammarFamily m) ↔ OrientsDupStep m)
    ∧ (∀ (S : StepDuplicatingSchema) (eval : S.T → Nat),
        OrientsAttained (schemaFamily (S := S) eval) ↔
          (∀ (b s n : S.T),
            eval (S.wrap s (S.recur b s n)) < eval (S.recur b s (S.succ n)))) :=
  ⟨fun m => grammarFamily_orientsAttained_iff m,
    fun S eval => schemaFamily_orientsAttained_iff (S := S) eval⟩

/-- **Sublayer capstone.** `MeasureExpr` is a proper syntax-restricted sublayer: its denotations are
counter-monotone, and consequently no grammar expression realizes both frozen sections of a family
at ordered counters once a strict counter-reversal witness is available. The four unconditional
families and the three conditional families supply that witness under exactly their live side
conditions. -/
theorem measureExpr_is_counterMonotone_sublayer :
    (∀ (e : MeasureExpr) (c c' p : Nat), c ≤ c' → e.eval c p ≤ e.eval c' p)
    ∧ (∀ (e : MeasureExpr) (cSrc cTgt : Nat), cTgt ≤ cSrc →
        ∀ src tgt : Nat → Nat,
          (∀ x, src x = e.eval cSrc x) → (∀ x, tgt x = e.eval cTgt x) →
          ∀ x, src x < tgt x → False) :=
  ⟨fun e c c' p h => eval_counterMonotone e c c' p h,
    fun e cSrc cTgt hc src tgt hsrc htgt x hrev =>
      no_grammar_sections_of_strict_reversal e cSrc cTgt hc src tgt hsrc htgt x hrev⟩

/-! ## 17. Reflected record-family grammar

`MeasureExpr` remains the closed coordinate grammar and the separation theorem above remains
load-bearing.  The following companion grammar reflects the seven record-valued scalar families
themselves, together with precisely the hypotheses in their public barrier statements.  This gives
the paper a literal family-level structural-induction theorem without pretending that an arbitrary
schema record is a `MeasureExpr`.

Every constructor is interpreted by the record's live evaluator.  The generic theorem below closes
all seven constructors through the attained-value carrier, so it is stronger than a name catalog:
it returns the actual non-orientation proposition for the stored measure and retains every original
side condition in the constructor type. -/

/-- Reflected grammar of the seven scalar record families closed by the attained-carrier program. -/
inductive ReflectedScalarFamilyGrammar (S : StepDuplicatingSchema) where
  | additive (M : AdditiveMeasure S)
  | affine (M : AffineMeasure S) (unbounded : HasUnboundedRange M)
  | quadratic (M : QuadraticCounterMeasure S) (unbounded : HasUnboundedRangeQ M)
  | crossQuadratic (M : CrossTermQuadraticMeasure S) (unbounded : HasUnboundedRangeX M)
      (dominated : CrossTermBoundedAtBase M)
  | multilinear (M : BoundedMultilinearMeasure S) (unbounded : HasUnboundedRangeML M)
      (dominated : MultilinearDominatedAtBase M)
  | polynomial (M : BoundedPolynomialMeasure S) (unbounded : HasUnboundedRangePoly M)
      (dominated : EventuallyDominatedAtBase M)
  | maxPlus (M : MaxMeasure S) (unbounded : HasUnboundedRangeMax M)

/-- The live evaluator stored by a reflected family-code constructor. -/
def ReflectedScalarFamilyGrammar.eval {S : StepDuplicatingSchema} :
    ReflectedScalarFamilyGrammar S → S.T → Nat
  | .additive M => M.eval
  | .affine M _ => M.eval
  | .quadratic M _ => M.eval
  | .crossQuadratic M _ _ => M.eval
  | .multilinear M _ _ => M.eval
  | .polynomial M _ _ => M.eval
  | .maxPlus M _ => M.eval

/-- Orientation proposition interpreted from a reflected family code. -/
def ReflectedScalarFamilyGrammar.Orients {S : StepDuplicatingSchema}
    (F : ReflectedScalarFamilyGrammar S) : Prop :=
  ∀ b s n : S.T,
    F.eval (S.wrap s (S.recur b s n)) < F.eval (S.recur b s (S.succ n))

/-- Attained-value interpretation of a reflected family code. -/
def ReflectedScalarFamilyGrammar.toAttained {S : StepDuplicatingSchema}
    (F : ReflectedScalarFamilyGrammar S) : AttainedValueFamily (S.T × S.T × S.T) :=
  schemaFamily F.eval

/-- The family-code orientation proposition is preserved and reflected by the common attained
carrier. -/
theorem ReflectedScalarFamilyGrammar.orientsAttained_iff {S : StepDuplicatingSchema}
    (F : ReflectedScalarFamilyGrammar S) :
    OrientsAttained F.toAttained ↔ F.Orients :=
  schemaFamily_orientsAttained_iff F.eval

/-- **Single structural-induction closure theorem.** Every constructor of the reflected scalar
record-family grammar fails to orient the duplicating step.  Each branch is discharged by the
statement-preserving attained-carrier corollary and therefore keeps the predecessor theorem's full
hypothesis surface. -/
theorem reflectedScalarFamilyGrammar_no_orients {S : StepDuplicatingSchema}
    (F : ReflectedScalarFamilyGrammar S) : ¬ F.Orients := by
  cases F with
  | additive M => exact no_additive_orients_dup_step_via_attainedCarrier M
  | affine M hunbounded =>
      exact no_affine_orients_dup_step_of_unbounded_via_attainedCarrier M hunbounded
  | quadratic M hunbounded =>
      exact no_quadratic_counter_orients_dup_step_of_unbounded_via_attainedCarrier M hunbounded
  | crossQuadratic M hunbounded hdom =>
      exact no_cross_quadratic_orients_dup_step_of_unbounded_via_attainedCarrier M hunbounded hdom
  | multilinear M hunbounded hdom =>
      exact no_multilinear_orients_dup_step_of_unbounded_via_attainedCarrier M hunbounded hdom
  | polynomial M hunbounded hdom =>
      exact no_polynomial_orients_dup_step_of_unbounded_via_attainedCarrier M hunbounded hdom
  | maxPlus M hunbounded =>
      exact no_max_orients_dup_step_of_unbounded_via_attainedCarrier M hunbounded

/-- The same structural theorem stated directly on the common attained-value carrier. -/
theorem reflectedScalarFamilyGrammar_no_orientsAttained {S : StepDuplicatingSchema}
    (F : ReflectedScalarFamilyGrammar S) : ¬ OrientsAttained F.toAttained := by
  intro h
  exact reflectedScalarFamilyGrammar_no_orients F (F.orientsAttained_iff.mp h)

/-- Non-vacuity: the reflected grammar has a constructor for every additive measure record. -/
theorem ReflectedScalarFamilyGrammar.additive_inhabited {S : StepDuplicatingSchema}
    (M : AdditiveMeasure S) : Nonempty (ReflectedScalarFamilyGrammar S) :=
  ⟨.additive M⟩

#print axioms ReflectedScalarFamilyGrammar
#print axioms ReflectedScalarFamilyGrammar.eval
#print axioms ReflectedScalarFamilyGrammar.Orients
#print axioms ReflectedScalarFamilyGrammar.toAttained
#print axioms ReflectedScalarFamilyGrammar.orientsAttained_iff
#print axioms reflectedScalarFamilyGrammar_no_orients
#print axioms reflectedScalarFamilyGrammar_no_orientsAttained
#print axioms ReflectedScalarFamilyGrammar.additive_inhabited

end OperatorKO7.Meta.BoundaryGeneral.FamilyGrammarSubsumption
