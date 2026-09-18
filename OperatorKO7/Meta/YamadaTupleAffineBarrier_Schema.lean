import OperatorKO7.Meta.BarrierPumpDischarge_Schema
import OperatorKO7.Meta.FreeStepDuplicatingSyntax

/-!
# Yamada Tuple Affine-Strict-Coordinate Barrier: Schema Layer

Schema-generic half of the Yamada-fragment tuple barrier.

Proves: a first-order tuple interpretation whose designated strict coordinate is a
constructor-local affine measure cannot orient the step-duplicating schema step
`recur b s (succ n) -> wrap s (recur b s n)`. The strict coordinate lands in the
existing affine barrier class, so the unconditional affine discharge applies.
Does not prove: a barrier for unrestricted Yamada tuple interpretations. The
cross-coupled first component (`crossCoupledTupleEval_orients` in
`Meta/Methods/AlgebraicInterpretationRows.lean`) still orients every duplicating
instance, so the paper's unrestricted `Tuple interpretations & escape` row stays true.
This module closes only the affine strict-coordinate fragment.

Porting note: source is Yamada 2022 (JAR, tuple interpretations for TRS
termination), first-order single-sort fixed-width fragment. Lean carrier is
`YamadaAffineTupleMeasure`: width `d`, pointwise tuple `eval`, designated
`strictIdx`, and an `AffineMeasure` strict projection with pointwise equality.
Only the strict-coordinate projection and its affine constructor laws are
formalized; monotonicity of the remaining coordinates is out of scope and unused.
Embedding: shallow (schema terms to `Nat` vectors). Classical axioms: none used.

Relation: the schema duplicating step at the root (`recur b s (succ n)` to
`wrap s (recur b s n)`), and `GlobalOrients` on any system containing it.
Closure: root; global versions quantify over every step of the system.
Strategy: not applicable (single designated step, no strategy restriction).
Trust: kernel-only. No `sorry`, `axiom`, `native_decide`, `@[csimp]`, `unsafe`,
`partial`, or `opaque`. Mathlib plus the existing barrier stack only.
Scope: unconditional for the affine strict-coordinate fragment; nonlinear or
non-affine strict coordinates are outside this module.
Non-vacuity witness: `freeYamadaWitness` on `freeSchema` at width one.
-/

set_option autoImplicit false

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Yamada-style tuple fragment with an affine strict coordinate. Only the
designated strict coordinate carries constructor laws (via `strictAffine`); the
remaining coordinates are unconstrained payload. -/
structure YamadaAffineTupleMeasure (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → (Fin d → Nat)
  strictIdx : Fin d
  strictAffine : AffineMeasure S
  strict_is_coord : ∀ t, eval t strictIdx = strictAffine.eval t

/-- Unconditional barrier: no affine strict-coordinate tuple orients the
duplicating step on its strict coordinate. Delegates to the discharged affine
barrier through the strict projection. -/
theorem no_yamadaAffineTuple_orients_dup_step
    {S : StepDuplicatingSchema} {d : Nat} (M : YamadaAffineTupleMeasure S d) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) M.strictIdx <
        M.eval (S.recur b s (S.succ n)) M.strictIdx) := by
  intro h
  apply no_affine_orients_dup_step M.strictAffine
  intro b s n
  simpa [M.strict_is_coord] using h b s n

/-- Minimal order abstraction for the Yamada affine fragment. The only
assumption is that strict comparison forces strict decrease on the designated
tuple coordinate. -/
structure YamadaAffineTupleOrder (S : StepDuplicatingSchema) (d : Nat) where
  tuple : YamadaAffineTupleMeasure S d
  gt : S.T → S.T → Prop
  sound : ∀ {x y : S.T}, gt x y → tuple.eval y tuple.strictIdx < tuple.eval x tuple.strictIdx

/-- Any order certified by an affine strict-coordinate tuple inherits the
Yamada-fragment barrier on the duplicating schema step. -/
theorem no_yamadaAffineTupleOrder_orients_dup_step
    {S : StepDuplicatingSchema} {d : Nat} (W : YamadaAffineTupleOrder S d) :
    ¬ (∀ (b s n : S.T),
      W.gt (S.recur b s (S.succ n)) (S.wrap s (S.recur b s n))) := by
  intro h
  apply no_yamadaAffineTuple_orients_dup_step W.tuple
  intro b s n
  exact W.sound (h b s n)

/-- The Yamada affine fragment also fails globally on any system containing
the duplicating step. -/
theorem no_global_orients_yamadaAffineTupleOrder
    {Sys : StepDuplicatingSystem} {d : Nat}
    (W : YamadaAffineTupleOrder Sys.toStepDuplicatingSchema d) :
    ¬ GlobalOrients Sys (fun t => t) (fun x y => W.gt y x) := by
  intro h
  apply no_yamadaAffineTupleOrder_orients_dup_step W
  intro b s n
  exact h (Sys.dup_step b s n)

/-- Structural size on the free syntax. Satisfies the affine constructor laws
with all coefficients one. -/
def freeSizeEval : FreeTerm → Nat
  | .base => 1
  | .succ t => 1 + freeSizeEval t
  | .wrap x y => 1 + freeSizeEval x + freeSizeEval y
  | .recur b s n => 1 + freeSizeEval b + freeSizeEval s + freeSizeEval n

/-- The size function packaged as an affine measure on the free schema. -/
def freeSizeAffine : AffineMeasure freeSchema where
  eval := freeSizeEval
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  eval_base := rfl
  eval_succ := by intro t; simp [freeSchema, freeSizeEval]
  eval_wrap := by intro x y; simp [freeSchema, freeSizeEval]
  eval_recur := by intro b s n; simp [freeSchema, freeSizeEval]
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

/-- Canonical width-one tuple witness on the free schema. -/
def freeYamadaWitness : YamadaAffineTupleMeasure freeSchema 1 where
  eval := fun t _ => freeSizeEval t
  strictIdx := ⟨0, Nat.zero_lt_one⟩
  strictAffine := freeSizeAffine
  strict_is_coord := by intro t; rfl

/-- The Yamada affine fragment class is nonempty. -/
theorem yamadaAffineTupleMeasure_nonempty :
    Nonempty (YamadaAffineTupleMeasure freeSchema 1) :=
  ⟨freeYamadaWitness⟩

/-- The witness strict coordinate is non-degenerate. -/
theorem freeSizeAffine_nonconstant :
    freeSizeAffine.eval (FreeTerm.succ FreeTerm.base) ≠
      freeSizeAffine.eval FreeTerm.base := by
  decide

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
