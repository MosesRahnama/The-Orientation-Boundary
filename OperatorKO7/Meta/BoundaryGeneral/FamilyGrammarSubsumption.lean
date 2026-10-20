import OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure
import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.QuadraticBarrier_Schema
import OperatorKO7.Meta.QuadraticCrossTermBarrier_Schema
import OperatorKO7.Meta.MultilinearBarrier_Schema
import OperatorKO7.Meta.PolynomialBarrierGeneral_Schema
import OperatorKO7.Meta.MaxBarrier_Schema

/-!
# Attained-value carrier for step-duplicating measures

`MeasureExpr` is a closed grammar of scalar measures on the `(counter, payload)` carrier. The seven record-valued measure families instead evaluate terms of an arbitrary `StepDuplicatingSchema`; this module states no embedding of those records into `MeasureExpr`.

`AttainedValueFamily` associates each binder tuple with source and target values in `Nat`. Orientation holds exactly when each target value is below its source value. The grammar and schema adapters map their readings into this carrier and preserve and reflect orientation.

The carrier stores no term, measure record, or selected pump curve. Unbounded corollaries fix the threshold first and obtain an attained term locally, so no `Classical.choose` is needed. `MeasureExpr` is nondecreasing in the counter coordinate. Thus one expression cannot realize both family sections at ordered counters when a strict reversal holds at an attained value. Additive, affine, restricted-quadratic, and max sections always have such a reversal; cross-term and multilinear require their stated side conditions, and generalized polynomial requires an explicit reversal hypothesis.

Trust: Mathlib-only; no `sorry`, `admit`, top-level `axiom`, `native_decide`, `bv_decide`, `@[csimp]`, `unsafe`, `partial`, or `Classical.choose` occurs in this module.
Relation: the schema duplicating root step and the grammar counter/payload step. Closure: root and single-step only, with no contextual-closure or `StepStar` claim. Property: non-orientation and adapter equivalences.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.FamilyGrammarSubsumption

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure

/-! ## 1. The choice-free attained value-pair carrier -/

/-- This structure records only the two `Nat`-valued readings at each index. It stores no term, measure record, or selected pump curve, so the structure contains no selection function. -/
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

/-- Adapter from a scalar measure on the two-coordinate `(counter, payload)` carrier to attained value pairs. -/
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

/-- `DominatedByScalar` only requires the scalar not to increase across the duplicating step. A non-strict reversal `srcVal ≤ tgtVal` is therefore insufficient; a strict inequality `srcVal i < tgtVal i` is required. -/
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

/-- If `sourceCoeff + 1 ≤ targetCoeff` and `sourceConst < x`, the target affine reading is strictly greater than the source reading. -/
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

/-- If one grammar expression realizes both family sections at ordered counters, counter monotonicity forces `tgt x ≤ src x` for every attained scalar. A strict reversal `src x < tgt x` at one such scalar rules out that joint representation. -/
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

/-- Above the additive source threshold, the target section is strictly greater than the source section. -/
theorem additive_strict_reversal {S : StepDuplicatingSchema} (M : AdditiveMeasure S)
    {x : Nat} (hx : M.w_recur + M.w_base + (M.w_succ + M.w_base) < x) :
    additiveSourceSection M x < additiveTargetSection M x := by
  simp only [additiveSourceSection, additiveTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ 1 _ 2 x additive_coeffGap hx

/-- Every additive measure fails to orient the duplicating step, without an unboundedness premise. -/
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

/-- Above `affineSourceConst`, the affine target section is strictly greater than the source section. -/
theorem affine_strict_reversal {S : StepDuplicatingSchema} (M : AffineMeasure S)
    {x : Nat} (hx : affineSourceConst M < x) :
    affineSourceSection M x < affineTargetSection M x := by
  simp only [affineSourceSection, affineTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ _ _ _ x (affine_coeffGap M) hx

/-- An affine measure with unbounded range cannot orient the duplicating step. -/
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

/-- Above `quadraticSourceConst`, the restricted-quadratic target section is strictly greater than the source section. -/
theorem quadratic_strict_reversal {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    {x : Nat} (hx : quadraticSourceConst M < x) :
    quadraticSourceSection M x < quadraticTargetSection M x := by
  simp only [quadraticSourceSection, quadraticTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ _ _ _ x (quadratic_coeffGap M) hx

/-- An unbounded restricted-quadratic measure cannot orient the duplicating step. -/
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

/-- Under `CrossTermBoundedAtBase`, values above `crossTermSourceConst` give a strict reversal from the source to the target section. -/
theorem crossTerm_strict_reversal {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S)
    (hbounded : CrossTermBoundedAtBase M)
    {x : Nat} (hx : crossTermSourceConst M < x) :
    crossTermSourceSection M x < crossTermTargetSection M x := by
  simp only [crossTermSourceSection, crossTermTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ _ _ _ x (crossTerm_coeffGap M hbounded) hx

/-- An unbounded cross-term quadratic measure satisfying `CrossTermBoundedAtBase` cannot orient the duplicating step. -/
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

/-- Under `MultilinearDominatedAtBase`, values above `multilinearSourceConst` give a strict reversal from the source to the target section. -/
theorem multilinear_strict_reversal {S : StepDuplicatingSchema}
    (M : BoundedMultilinearMeasure S) (hdom : MultilinearDominatedAtBase M)
    {x : Nat} (hx : multilinearSourceConst M < x) :
    multilinearSourceSection M x < multilinearTargetSection M x := by
  simp only [multilinearSourceSection, multilinearTargetSection]
  exact attained_strict_reversal_of_coeff_gap _ _ _ _ x (multilinear_coeffGap M hdom) hx

/-- An unbounded multilinear measure satisfying `MultilinearDominatedAtBase` cannot orient the duplicating step. -/
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

/-- An unbounded polynomial measure satisfying `EventuallyDominatedAtBase` cannot orient the duplicating step. -/
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

/-- The generalized polynomial family has no unconditional coefficient gap. Layer separation requires an attained scalar where the source section is strictly below the target section. -/
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

/-- An unbounded max-plus measure cannot orient the duplicating step. -/
theorem no_max_orients_dup_step_of_unbounded_via_attainedCarrier
    {S : StepDuplicatingSchema} (M : MaxMeasure S)
    (hunbounded : HasUnboundedRangeMax M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  rcases hunbounded (maxThreshold M) with ⟨s, hs⟩
  refine not_family_orients_of_base_reversal (S := S) M.eval (w := s) ?_
  rw [max_source_eval, max_target_eval]
  exact Nat.le_of_lt (max_strict_reversal M hs)

/-- Once both frozen recursor maxima select the step branch, the positive right-wrapper offset makes the target section strictly greater than the source. -/
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

/-- The grammar and schema adapters both preserve and reflect orientation through `AttainedValueFamily`; this comparison does not identify a record family with a `MeasureExpr`. -/
theorem attainedCarrier_is_shared_layer :
    (∀ m : Nat → Nat → Nat, OrientsAttained (grammarFamily m) ↔ OrientsDupStep m)
    ∧ (∀ (S : StepDuplicatingSchema) (eval : S.T → Nat),
        OrientsAttained (schemaFamily (S := S) eval) ↔
          (∀ (b s n : S.T),
            eval (S.wrap s (S.recur b s n)) < eval (S.recur b s (S.succ n)))) :=
  ⟨fun m => grammarFamily_orientsAttained_iff m,
    fun S eval => schemaFamily_orientsAttained_iff (S := S) eval⟩

/-- Every `MeasureExpr` is counter-monotone, so one expression cannot realize both family sections at ordered counters when an attained value has strict counter reversal. Additive, affine, restricted-quadratic, and max sections always have such a reversal; cross-term and multilinear require their stated conditions, and generalized polynomial requires an explicit reversal. -/
theorem measureExpr_is_counterMonotone_sublayer :
    (∀ (e : MeasureExpr) (c c' p : Nat), c ≤ c' → e.eval c p ≤ e.eval c' p)
    ∧ (∀ (e : MeasureExpr) (cSrc cTgt : Nat), cTgt ≤ cSrc →
        ∀ src tgt : Nat → Nat,
          (∀ x, src x = e.eval cSrc x) → (∀ x, tgt x = e.eval cTgt x) →
          ∀ x, src x < tgt x → False) :=
  ⟨fun e c c' p h => eval_counterMonotone e c c' p h,
    fun e cSrc cTgt hc src tgt hsrc htgt x hrev =>
      no_grammar_sections_of_strict_reversal e cSrc cTgt hc src tgt hsrc htgt x hrev⟩

/-! ## Reflected record-family grammar

`MeasureExpr` remains the closed coordinate grammar. `ReflectedScalarFamilyGrammar` stores one of seven record-valued scalar families with the hypotheses required by its corresponding barrier theorem. Its evaluator uses the stored measure, and the structural theorem proves that each constructor fails to orient through the attained-value carrier.
-/

/-- Grammar for the seven scalar record families, retaining each required hypothesis. -/
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

/-- Every constructor in `ReflectedScalarFamilyGrammar` fails to orient the duplicating step through the attained-value result, with the hypotheses carried by its constructor. -/
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

/-- Every additive measure record has an additive constructor in `ReflectedScalarFamilyGrammar`. -/
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
