import OperatorKO7.Meta.NonlinearMethodLawCarrier
import OperatorKO7.Meta.MatrixBarrierArcticNatural
import OperatorKO7.Meta.MatrixBarrierTropicalNatural_Schema
import OperatorKO7.Meta.DominancePremiseSharpness

/-!
# The exact law behind the unconstrained nonlinear direct row

`Meta/NonlinearUnconstrainedSplit.lean` types the `arbitraryRelationLawBoundary` row as an exact
law-carrier dichotomy, and `Meta/NonlinearMethodLawCarrier.lean` discharges it through
`arbitrary_relation_law_no_first_order_method_or_licensed_escape`. That discharge is carrier
bound: `NonlinearMethodLawCarrier` fixes `relation = Step`, so for every other relation the
right disjunct holds because no carrier exists at all.
`arbitrary_relation_law_boundary_vacuous_off_step` compiles that reading, so the row's strength is
visible in Lean and not only in prose.

This module supplies the non-vacuous replacement the row was standing in for: one law, stated for
an arbitrary step-duplicating schema and an arbitrary natural-valued interpretation, that blocks
the duplicating step.

The law is that the wrapper keeps its two arguments at a fixed cost while advancing the counter
adds at most a fixed gain. Alleged orientation itself supplies a positive value, and repeated
wrapping pumps that value past the fixed counter gain. No separate unbounded-range hypothesis is
needed. The
additive, natural-matrix, affine, arctic, and ordered-carrier families all satisfy it, which is why
each of them is blocked; the tropical family does not, which is why it escapes
(`Meta/MatrixBarrierTropicalNatural_Schema.lean`).

Relation: the schema duplicating step at the root. Closure: root.
External trust: none. Mathlib only.
Named method: unconstrained nonlinear direct interpretations over the naturals.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-! ## The exact law -/

/-- **The exact law.** A natural-valued direct interpretation in which the wrapper keeps both of
its arguments at a fixed cost and advancing the counter adds at most a fixed gain. No linearity,
no compositionality, no matrix or polynomial shape, and no range hypothesis. -/
structure UnconstrainedDirectLaw (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  /-- The fixed cost the wrapper pays on top of its two arguments. -/
  wrapCost : Nat
  /-- The wrapper keeps both arguments. -/
  wrap_keeps_arguments : ∀ x y, wrapCost + eval x + eval y ≤ eval (S.wrap x y)
  /-- The fixed gain of one counter step. -/
  succGain : Nat
  /-- Advancing the counter by one adds at most the fixed gain. -/
  counter_gain : ∀ b s n, eval (S.recur b s (S.succ n)) ≤ succGain + eval (S.recur b s n)

/-- Repeated wrapping with one fixed seed. -/
def seedWrapIter (S : StepDuplicatingSchema) (seed : S.T) : Nat → S.T
  | 0 => seed
  | k + 1 => S.wrap seed (seedWrapIter S seed k)

/-- A positive seed pumps past every finite index using wrapper retention alone. -/
theorem eval_seedWrapIter_ge_index {S : StepDuplicatingSchema} (L : UnconstrainedDirectLaw S)
    (seed : S.T) (hseed : 1 ≤ L.eval seed) (k : Nat) :
    k + 1 ≤ L.eval (seedWrapIter S seed k) := by
  induction k with
  | zero => simpa [seedWrapIter] using hseed
  | succ k ih =>
      have hw := L.wrap_keeps_arguments seed (seedWrapIter S seed k)
      simp only [seedWrapIter]
      omega

/-- **The unconstrained nonlinear direct barrier.** No interpretation satisfying the exact law
orients the duplicating step, for any order whose strict comparison forces a strict decrease of
the value. Alleged orientation supplies a positive seed; wrapper retention pumps it beyond the
fixed counter gain; the same orientation then bounds it below that gain. -/
theorem no_unconstrainedDirect_orients_dup_step
    {S : StepDuplicatingSchema} (L : UnconstrainedDirectLaw S) :
    ¬ (∀ (b s n : S.T),
      L.eval (S.wrap s (S.recur b s n)) < L.eval (S.recur b s (S.succ n))) := by
  intro h
  let seed : S.T := S.recur S.base S.base (S.succ S.base)
  have hseed : 1 ≤ L.eval seed := by
    have h0 := h S.base S.base S.base
    dsimp [seed]
    omega
  let t : S.T := seedWrapIter S seed L.succGain
  have ht : L.succGain + 1 ≤ L.eval t := by
    exact eval_seedWrapIter_ge_index L seed hseed L.succGain
  have hlow := L.wrap_keeps_arguments t (S.recur S.base t S.base)
  have hstep := h S.base t S.base
  have hcap := L.counter_gain S.base t S.base
  omega

/-- The same statement through an arbitrary comparison relation, matching the shape of the
matrix and arctic barriers. -/
theorem no_unconstrainedDirect_orients_dup_step_of_tracked
    {S : StepDuplicatingSchema} (L : UnconstrainedDirectLaw S)
    {R : Nat → Nat → Prop} (hR : ∀ {u v : Nat}, R u v → u < v) :
    ¬ (∀ (b s n : S.T),
      R (L.eval (S.wrap s (S.recur b s n))) (L.eval (S.recur b s (S.succ n)))) := fun h =>
  no_unconstrainedDirect_orients_dup_step L (fun b s n => hR (h b s n))

/-- System-level form. -/
theorem no_global_orients_unconstrainedDirect
    {Sys : StepDuplicatingSystem} (L : UnconstrainedDirectLaw Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys L.eval (· < ·) := fun h =>
  no_unconstrainedDirect_orients_dup_step L (fun b s n => h (Sys.dup_step b s n))

/-! ## Every additive interpretation satisfies the law -/

/-- With a positive successor weight the additive successor chain grows at least linearly. -/
theorem additive_eval_succIter_ge {S : StepDuplicatingSchema}
    (M : AdditiveMeasure S) (hsucc : 1 ≤ M.w_succ) (k : Nat) :
    k ≤ M.eval (succIter S k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hs : M.eval (succIter S (k + 1)) = M.w_succ + M.eval (succIter S k) :=
        M.eval_succ (succIter S k)
      omega

/-- Every additive measure satisfies the exact law, so the additive barrier is the law's first
instance. No positivity or unboundedness premise is needed. -/
def AdditiveMeasure.toUnconstrainedDirectLaw {S : StepDuplicatingSchema}
    (M : AdditiveMeasure S) : UnconstrainedDirectLaw S where
  eval := M.eval
  wrapCost := M.w_wrap
  wrap_keeps_arguments := fun x y => by rw [M.eval_wrap]
  succGain := M.w_succ
  counter_gain := fun b s n => by
    rw [M.eval_recur, M.eval_recur, M.eval_succ]
    omega

/-! ## Both remaining clauses are load-bearing -/

/-- Dropping the wrapper clause: `botRightWeight` keeps its left argument but forgets its right
one, and it orients the duplicating step. -/
theorem unconstrainedDirectLaw_wrap_clause_necessary :
    (∀ x y : FreeTerm, botRightWeight y ≤ botRightWeight (freeSchema.wrap x y)) = False := by
  simp only [eq_iff_iff, iff_false, not_forall]
  refine ⟨FreeTerm.base, FreeTerm.succ FreeTerm.base, ?_⟩
  simp [freeSchema, botRightWeight]

/-- Proposition-valued form of the wrapper-clause counterexample. -/
theorem unconstrainedDirectLaw_wrap_clause_fails :
    ¬ ∀ x y : FreeTerm, botRightWeight y ≤ botRightWeight (freeSchema.wrap x y) := by
  intro h
  exact Eq.mp unconstrainedDirectLaw_wrap_clause_necessary h

/-- With the wrapper clause dropped the duplicating step is oriented, so the clause cannot be
weakened to "keeps the left argument only". -/
theorem unconstrainedDirectLaw_wrap_clause_escape :
    ∀ (b s n : FreeTerm),
      botRightWeight (freeSchema.wrap s (freeSchema.recur b s n)) <
        botRightWeight (freeSchema.recur b s (freeSchema.succ n)) := by
  intro b s n
  simp only [freeSchema, botRightWeight]
  omega

/-- The cross-coupled witness retains both wrapper arguments exactly. -/
theorem crossCoupledWeight_keeps_wrapper_arguments :
    ∀ x y : FreeTerm,
      0 + crossCoupledWeight x + crossCoupledWeight y ≤
        crossCoupledWeight (freeSchema.wrap x y) := by
  intro x y
  simp [freeSchema, crossCoupledWeight]

/-- Exact value of the cross-coupled witness on the successor pump. -/
theorem crossCoupledWeight_succIter (k : Nat) :
    crossCoupledWeight (succIter freeSchema k) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [succIter]
      change 1 + crossCoupledWeight (succIter freeSchema k) = (k + 1) + 1
      rw [ih]
      omega

/-- No fixed counter gain bounds the cross-coupled witness. -/
theorem crossCoupledWeight_has_no_counter_gain :
    ∀ g : Nat, ¬ ∀ b s n : FreeTerm,
      crossCoupledWeight (freeSchema.recur b s (freeSchema.succ n)) ≤
        g + crossCoupledWeight (freeSchema.recur b s n) := by
  intro g h
  have hbad := h FreeTerm.base (succIter freeSchema g) FreeTerm.base
  change
    crossCoupledWeight
        (FreeTerm.recur FreeTerm.base (succIter freeSchema g) (FreeTerm.succ FreeTerm.base)) <=
      g + crossCoupledWeight
        (FreeTerm.recur FreeTerm.base (succIter freeSchema g) FreeTerm.base) at hbad
  simp only [crossCoupledWeight] at hbad
  rw [crossCoupledWeight_succIter] at hbad
  omega

/-- **The counter-gain clause is load-bearing.** The cross-coupled witness retains both wrapper
arguments, orients the duplicating step, and admits no fixed counter gain. -/
theorem unconstrainedDirectLaw_counter_clause_escape :
    (∀ x y : FreeTerm,
      0 + crossCoupledWeight x + crossCoupledWeight y ≤
        crossCoupledWeight (freeSchema.wrap x y))
      ∧ (∀ (b s n : FreeTerm),
        crossCoupledWeight (freeSchema.wrap s (freeSchema.recur b s n)) <
          crossCoupledWeight (freeSchema.recur b s (freeSchema.succ n)))
      ∧ (∀ g : Nat, ¬ ∀ b s n : FreeTerm,
        crossCoupledWeight (freeSchema.recur b s (freeSchema.succ n)) ≤
          g + crossCoupledWeight (freeSchema.recur b s n)) :=
  ⟨crossCoupledWeight_keeps_wrapper_arguments,
    crossCoupledWeight_strictly_orients,
    crossCoupledWeight_has_no_counter_gain⟩

/-- The tropical escape has bounded range. This fact is no longer a sharpness premise: the exact
law needs no independent unboundedness clause. -/
theorem tropicalEscapeWeight_le_five (t : FreeTerm) : tropicalEscapeWeight t ≤ 5 := by
  induction t with
  | base => simp [tropicalEscapeWeight]
  | succ t ih => simp [tropicalEscapeWeight]
  | wrap x y ihx ihy => simp [tropicalEscapeWeight]
  | recur b s n ihb ihs ihn => simp [tropicalEscapeWeight]

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.NonlinearMethodLawCarrier

/-! ## What the carrier dichotomy actually proves -/

/-- **The carrier dichotomy is vacuous off `Step`.** For every relation other than the KO7 step
relation the right disjunct of `arbitrary_relation_law_boundary` holds because the carrier type
admits no inhabitant over that relation at all, not because a first-order method was ruled out.
The non-vacuous replacement is
`OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_unconstrainedDirect_orients_dup_step`. -/
theorem arbitrary_relation_law_boundary_vacuous_off_step
    (R : NonlinearRelation) (hne : R ≠ Step) :
    ¬ ∃ carrier : NonlinearMethodLawCarrier, carrier.relation = R := by
  rintro ⟨carrier, hrel⟩
  exact hne (hrel.symm.trans (nonlinearMethodLawCarrier_relation_eq_step carrier))

/-- The dichotomy's non-`Step` half is exactly the emptiness above, so the row carries no
statement about first-order methods for any relation other than `Step`. -/
theorem arbitrary_relation_law_boundary_off_step_is_emptiness
    (R : NonlinearRelation) (hne : R ≠ Step) :
    (¬ ∃ law : NonlinearMethodLaw, relation_has_direct_first_order_method R law) ∧
      (¬ ∃ carrier : NonlinearMethodLawCarrier, carrier.relation = R) := by
  refine ⟨?_, arbitrary_relation_law_boundary_vacuous_off_step R hne⟩
  rintro ⟨law, carrier, hrel, -, -⟩
  exact arbitrary_relation_law_boundary_vacuous_off_step R hne ⟨carrier, hrel⟩

end OperatorKO7.NonlinearMethodLawCarrier
