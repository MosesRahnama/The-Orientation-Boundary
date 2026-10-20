import Mathlib.Tactic
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax

/-!
# L12 typed direct-measure barrier: no additive binder-transparent measure orients the
well-typed duplicating beta family of System T

Relation: `Step` (full, contextual, one step; the family `dupRedex g -> dupContractum g` is a root
beta step).
Closure: one step; the barrier concerns the root step of the family and needs no contextual
closure.
Strategy: full `Step`; no strategy restriction enters the statement.
Trust: kernel-only; no axioms beyond the Lean baseline.
Scope: the well-typed duplicating family `dupRedex g` over well-typed closed `g`, and every
application-additive, binder-transparent, variable-constant measure `TypedDirectMeasure c`.

The untyped M2 barrier `no_directHOMeasure_orients_duplicating_beta` uses the pump redex
`(λ0. v0 v0) arg`, whose body is self-application and so is not simply typable. This module states
the same barrier for a well-typed carrier: the redex `(λf : nat → nat. f (f zero)) g` reduces to
`g (g zero)`, the pump `pump = λx. (λy. y) x` has type `nat → nat` and evaluates to `2 * c` under
every member, and orientation forces every attained value strictly below `2 * c`. The no-go holds
for every `c`, including `c = 0`.

`Closed` records free-variable-freeness; `hasType_nil_closed` proves that every term typed in the
empty context is closed, so the scope over well-typed closed `g` is exactly
`HasType [] g (nat → nat)`.

`churchIndex_measure_separates` exhibits a reader outside the direct-measure class that counts
occurrences of the head abstraction's own bound variable. It is a separation fact only and is not
an orientation of `Step`.

Does not prove: an impossibility for every termination method; HORPO and reducibility prove this
calculus terminating.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingTypedDirectMeasureBarrier

open OperatorKO7.HigherOrderRewritingSystemT

/-! ## Closedness -/

/-- `FreeAt k t` holds when the variable with de Bruijn index `k` occurs free in `t`, with the
tracked index raised by one for every binder crossed. -/
def FreeAt (k : Nat) : SysTTerm → Prop
  | .var n => n = k
  | .lam _ b => FreeAt (k + 1) b
  | .app f a => FreeAt k f ∨ FreeAt k a
  | .zero => False
  | .succ t => FreeAt k t
  | .natrec z s n => FreeAt k z ∨ FreeAt k s ∨ FreeAt k n

/-- `Closed t` holds when `t` has no free variable at any de Bruijn index. -/
def Closed (t : SysTTerm) : Prop := ∀ k, ¬ FreeAt k t

private theorem getElem?_some_lt {Γ : List SysTTy} {n : Nat} {A : SysTTy}
    (h : Γ[n]? = some A) : n < Γ.length := by
  induction Γ generalizing n with
  | nil => simp at h
  | cons B Γ ih =>
      cases n with
      | zero => simp
      | succ n =>
          have h' : Γ[n]? = some A := by simpa using h
          have hlt := ih h'
          simp only [List.length_cons]
          omega

/-- Proves: a term typed in context `Γ` has no free variable at any index at or above
`Γ.length`; in particular every term typed in the empty context is closed.
Does not prove: type uniqueness, subject reduction, or any rewriting property.
Relation: the typing judgment `HasType` against the free-variable predicate `FreeAt`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every System T term, every de Bruijn context, every index.
-/
theorem hasType_not_freeAt_of_length_le : ∀ {Γ : List SysTTy} {t : SysTTerm} {A : SysTTy},
    HasType Γ t A → ∀ k, Γ.length ≤ k → ¬ FreeAt k t := by
  intro Γ t A h
  induction h with
  | var hlook =>
      intro k hk hfree
      have hlt := getElem?_some_lt hlook
      simp only [FreeAt] at hfree
      omega
  | lam hbody ih =>
      intro k hk hfree
      exact ih (k + 1) (by simp only [List.length_cons]; omega) hfree
  | app hf ha ihf iha =>
      intro k hk hfree
      rcases hfree with hf' | ha'
      · exact ihf k hk hf'
      · exact iha k hk ha'
  | zero =>
      intro k _ hfree
      exact hfree
  | succ ht ih =>
      intro k hk hfree
      exact ih k hk hfree
  | natrec hz hs hn ihz ihs ihn =>
      intro k hk hfree
      rcases hfree with hz' | hs' | hn'
      · exact ihz k hk hz'
      · exact ihs k hk hs'
      · exact ihn k hk hn'

/-- Proves: every term typed in the empty context is closed.
Does not prove: the converse; a closed term need not be well typed at any type.
Relation: `HasType` against `Closed`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every System T term and every type.
-/
theorem hasType_nil_closed {t : SysTTerm} {A : SysTTy} (h : HasType [] t A) : Closed t :=
  fun k => hasType_not_freeAt_of_length_le h k (Nat.zero_le k)

/-! ## Typed direct measures -/

/-- A typed direct measure: values add across application, pass through binders, and read the
constant `c` at every variable occurrence. Values on `zero`, `succ`, and `natrec` are free. -/
structure TypedDirectMeasure (c : Nat) where
  eval : SysTTerm → Nat
  eval_app : ∀ f a, eval (SysTTerm.app f a) = eval f + eval a
  eval_lam : ∀ A b, eval (SysTTerm.lam A b) = eval b
  eval_var : ∀ i, eval (SysTTerm.var i) = c

/-! ## The well-typed duplicating family -/

/-- The duplicating body `f (f zero)`, with `f` at index `0`. It contains no binder. -/
def dupBody : SysTTerm := .app (.var 0) (.app (.var 0) .zero)

/-- The duplicating redex `(λf : nat → nat. f (f zero)) g`. -/
def dupRedex (g : SysTTerm) : SysTTerm := .app (.lam (.arrow .nat .nat) dupBody) g

/-- The duplicating contractum `g (g zero)`. -/
def dupContractum (g : SysTTerm) : SysTTerm := .app g (.app g .zero)

example : subst 0 (.succ .zero) dupBody = dupContractum (.succ .zero) := by decide

example : subst 0 (.lam .nat (.var 0)) dupBody =
    dupContractum (.lam .nat (.var 0)) := by decide

/-- Proves: `subst 0 g dupBody` is `dupContractum g` for every `g`; the body has no binder, so the
substitution inserts `g` unchanged at both occurrences.
Does not prove: a substitution law for a body with binders.
Relation: equality of `subst`; not a rewrite relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every term `g`.
-/
theorem subst_dupBody_eq_dupContractum (g : SysTTerm) :
    subst 0 g dupBody = dupContractum g := rfl

/-- Proves: the duplicating redex takes the root beta step to the contractum for every `g`; the
root step needs no closedness premise because the body carries no binder.
Does not prove: orientation of any measure, or any typing property.
Relation: `Step` (full, contextual, one step; this family is a root beta step).
Closure: one step at the root of the family.
Strategy: full `Step`.
Trust: kernel-only.
Scope: the family `dupRedex g -> dupContractum g` over every term `g`; the typed scope restricts
`g` to well-typed closed terms through `hasType_dupRedex` and `hasType_nil_closed`.
-/
theorem dupRedex_step (g : SysTTerm) : Step (dupRedex g) (dupContractum g) := by
  show Step (.app (.lam (.arrow .nat .nat) dupBody) g) (subst 0 g dupBody)
  exact Step.beta (.arrow .nat .nat) dupBody g

/-- Proves: the duplicating body is typed `nat` in the context `[nat → nat]`.
Does not prove: that the body is closed; the body has the free variable `0`.
Relation: the typing judgment `HasType`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the single context `[nat → nat]`.
-/
theorem hasType_dupBody : HasType [.arrow .nat .nat] dupBody .nat :=
  HasType.app (HasType.var rfl) (HasType.app (HasType.var rfl) HasType.zero)

/-- Proves: the duplicating redex is typed `nat` in the empty context for every well-typed `g` of
type `nat → nat`.
Does not prove: subject reduction, or typing at any other type.
Relation: the typing judgment `HasType`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the family `dupRedex g` over well-typed closed `g`.
-/
theorem hasType_dupRedex {g : SysTTerm} (hg : HasType [] g (.arrow .nat .nat)) :
    HasType [] (dupRedex g) .nat :=
  HasType.app (HasType.lam hasType_dupBody) hg

/-- Proves: the duplicating contractum is typed `nat` in the empty context for every well-typed `g`
of type `nat → nat`.
Does not prove: subject reduction, or typing at any other type.
Relation: the typing judgment `HasType`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the family `dupContractum g` over well-typed closed `g`.
-/
theorem hasType_dupContractum {g : SysTTerm} (hg : HasType [] g (.arrow .nat .nat)) :
    HasType [] (dupContractum g) .nat :=
  HasType.app hg (HasType.app hg HasType.zero)

/-! ## The exact threshold -/

/-- A typed direct measure orients the well-typed duplicating family when every well-typed `g`
strictly decreases from the redex to the contractum.
Relation: `Step` (full, contextual, one step; the family is a root beta step).
Closure: one step.
Strategy: full `Step`.
Trust: kernel-only.
Scope: the family `dupRedex g` over well-typed closed `g`.
Does not prove: an impossibility for every termination method; HORPO and reducibility prove this
calculus terminating.
-/
def OrientsTypedDup {c : Nat} (M : TypedDirectMeasure c) : Prop :=
  ∀ g : SysTTerm, HasType [] g (.arrow .nat .nat) →
    M.eval (dupContractum g) < M.eval (dupRedex g)

/-- Proves: the redex evaluates to `(2 * c + eval zero) + eval g`.
Does not prove: a value for `zero`; the structure leaves it free.
Relation: equality of `TypedDirectMeasure.eval`; not a rewrite relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every member and every term `g`.
-/
theorem eval_dupRedex {c : Nat} (M : TypedDirectMeasure c) (g : SysTTerm) :
    M.eval (dupRedex g) = (2 * c + M.eval .zero) + M.eval g := by
  simp only [dupRedex, dupBody, M.eval_app, M.eval_lam, M.eval_var]
  omega

/-- Proves: the contractum evaluates to `2 * eval g + eval zero`.
Does not prove: a value for `zero`; the structure leaves it free.
Relation: equality of `TypedDirectMeasure.eval`; not a rewrite relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every member and every term `g`.
-/
theorem eval_dupContractum {c : Nat} (M : TypedDirectMeasure c) (g : SysTTerm) :
    M.eval (dupContractum g) = 2 * M.eval g + M.eval .zero := by
  simp only [dupContractum, M.eval_app]
  omega

/-- Proves: a member orients the well-typed duplicating family exactly when every attained value
of a well-typed closed `g` lies strictly below `2 * c`; the offset `eval zero` cancels between
redex and contractum.
Does not prove: that any member satisfies the threshold; the pointwise characterization does not
make the family orientable, and `no_typedDirectMeasure_orients_duplicating_beta` refutes that.
Relation: `Step` (full, contextual, one step; the family is a root beta step).
Closure: one step.
Strategy: full `Step`.
Trust: kernel-only.
Scope: every member `M` of `TypedDirectMeasure c` and the family `dupRedex g` over well-typed
closed `g`.
Does not prove: an impossibility for every termination method; HORPO and reducibility prove this
calculus terminating.
-/
theorem orientsTypedDup_iff_below_threshold {c : Nat} (M : TypedDirectMeasure c) :
    OrientsTypedDup M ↔
      ∀ g : SysTTerm, HasType [] g (.arrow .nat .nat) → M.eval g < 2 * c := by
  constructor
  · intro hOrients g hg
    have h := hOrients g hg
    rw [eval_dupContractum M g, eval_dupRedex M g] at h
    omega
  · intro hBelow g hg
    have h := hBelow g hg
    rw [eval_dupContractum M g, eval_dupRedex M g]
    omega

/-! ## The typed pump -/

/-- The identity function `λx. x` at type `nat → nat`. -/
def idFn : SysTTerm := .lam .nat (.var 0)

/-- The typed pump `λx. (λy. y) x`. Its body applies a function to a bound variable, so it is
well typed at `nat → nat`, unlike the untyped self-application pump of the M2 lane. -/
def pump : SysTTerm := .lam .nat (.app idFn (.var 0))

/-- Proves: the pump is typed `nat → nat` in the empty context.
Does not prove: typing of any other term, or a value of `eval` on the pump.
Relation: the typing judgment `HasType`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the single term `pump`.
-/
theorem hasType_pump : HasType [] pump (.arrow .nat .nat) :=
  HasType.lam (HasType.app (HasType.lam (HasType.var rfl)) (HasType.var rfl))

/-- Proves: every member evaluates the pump to `2 * c`, the exact threshold, by additivity and the
variable law alone.
Does not prove: orientation of the pump, or a value for `zero`.
Relation: equality of `TypedDirectMeasure.eval`; not a rewrite relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every member `TypedDirectMeasure c`; check instances at `c = 0` and `c = 3` are below.
-/
theorem eval_pump {c : Nat} (M : TypedDirectMeasure c) : M.eval pump = 2 * c := by
  simp only [pump, idFn, M.eval_app, M.eval_lam, M.eval_var]
  omega

/-- Proves: no typed direct measure orients the well-typed duplicating family, for every `c`
including `c = 0`. Orientation would force `M.eval pump < 2 * c`, while additivity and the
variable law force `M.eval pump = 2 * c`; the threshold is attained, so it cannot be strict.
Does not prove: an impossibility for every termination method; HORPO and reducibility prove this
calculus terminating. The theorem is about the direct additive class only.
Relation: `Step` (full, contextual, one step; the family `dupRedex g` is a root beta step).
Closure: one step.
Strategy: full `Step`.
Trust: kernel-only; the reach file checks the axiom set is empty.
Scope: the family `dupRedex g` over well-typed closed `g`, and every member `TypedDirectMeasure c`.
-/
theorem no_typedDirectMeasure_orients_duplicating_beta (c : Nat) (M : TypedDirectMeasure c) :
    ¬ OrientsTypedDup M := by
  intro hOrients
  have hlt : M.eval pump < 2 * c :=
    (orientsTypedDup_iff_below_threshold M).mp hOrients pump hasType_pump
  have heq : M.eval pump = 2 * c := eval_pump M
  omega

/-! ## Non-vacuity: a concrete member for every `c` -/

/-- The concrete evaluator: an additive node count that ignores binders and counts `c` per
variable occurrence. Every node contributes one, so `zero` contributes one and each `succ` and
`natrec` node adds one. -/
def typedMeasureEval (c : Nat) : SysTTerm → Nat
  | .var _ => c
  | .lam _ b => typedMeasureEval c b
  | .app f a => typedMeasureEval c f + typedMeasureEval c a
  | .zero => 1
  | .succ t => typedMeasureEval c t + 1
  | .natrec z s n => typedMeasureEval c z + typedMeasureEval c s + typedMeasureEval c n + 1

/-- Proves: the concrete evaluator is additive across application.
Does not prove: a value on any other constructor beyond its defining equation.
Relation: equality of `typedMeasureEval`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c`, every function and argument.
-/
theorem typedMeasureEval_app (c : Nat) (f a : SysTTerm) :
    typedMeasureEval c (.app f a) = typedMeasureEval c f + typedMeasureEval c a := rfl

/-- Proves: the concrete evaluator passes through binders.
Does not prove: a value on any other constructor beyond its defining equation.
Relation: equality of `typedMeasureEval`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c`, every binder type and body.
-/
theorem typedMeasureEval_lam (c : Nat) (A : SysTTy) (b : SysTTerm) :
    typedMeasureEval c (.lam A b) = typedMeasureEval c b := rfl

/-- Proves: the concrete evaluator returns `c` at every variable occurrence.
Does not prove: a value on any other constructor beyond its defining equation.
Relation: equality of `typedMeasureEval`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c` and every index.
-/
theorem typedMeasureEval_var (c : Nat) (i : Nat) :
    typedMeasureEval c (.var i) = c := rfl

/-- The concrete inhabitant of `TypedDirectMeasure c` for every `c`, built from the additive node
count. -/
def typedMeasureWitness (c : Nat) : TypedDirectMeasure c where
  eval := typedMeasureEval c
  eval_app := typedMeasureEval_app c
  eval_lam := typedMeasureEval_lam c
  eval_var := typedMeasureEval_var c

example : (typedMeasureWitness 0).eval pump = 0 := by decide

example : (typedMeasureWitness 3).eval pump = 6 := by decide

/-- Proves: the direct-measure class is inhabited for every `c`, so the no-go is not vacuous.
Does not prove: that every member is a node count; the class is quantified in full.
Relation: `Nonempty` of the measure structure; not a rewrite relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `c : Nat`.
-/
theorem typedDirectMeasure_nonempty (c : Nat) : Nonempty (TypedDirectMeasure c) :=
  ⟨typedMeasureWitness c⟩

/-! ## Separation: a counter-coordinate reader outside the direct class -/

/-- `occursAt j t` counts occurrences of the variable with de Bruijn index `j` in `t`, with the
tracked index raised by one for every binder crossed. -/
def occursAt (j : Nat) : SysTTerm → Nat
  | .var n => if n = j then 1 else 0
  | .lam _ b => occursAt (j + 1) b
  | .app f a => occursAt j f + occursAt j a
  | .zero => 0
  | .succ t => occursAt j t
  | .natrec z s n => occursAt j z + occursAt j s + occursAt j n

/-- Proves: the Church body contains exactly `n` occurrences of the outer abstraction's variable,
which sits at index `1` inside the inner binder.
Does not prove: a count for any other term.
Relation: equality of `occursAt`; not a rewrite relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem occursAt_churchBody : ∀ n, occursAt 1 (churchBody n) = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hvar : occursAt 1 (.var 1) = 1 := by decide
      have hstep : occursAt 1 (churchBody (n + 1)) =
          occursAt 1 (.var 1) + occursAt 1 (churchBody n) := rfl
      rw [hstep, hvar, ih]
      omega

/-- The body of the head abstraction of an applicative spine, if the spine has an abstraction at
its head. -/
def headAbstractionBody : SysTTerm → Option SysTTerm
  | .lam _ b => some b
  | .app f _ => headAbstractionBody f
  | _ => none

/-- The counter-coordinate reader: the number of occurrences of the head abstraction's own bound
variable in its body, and zero when the spine has no head abstraction. -/
def headBoundVarOccurrences (t : SysTTerm) : Nat :=
  match headAbstractionBody t with
  | some b => occursAt 0 b
  | none => 0

/-- Proves: on the Church family the reader returns the index `n`.
Does not prove: a value on any other term.
Relation: equality of `headBoundVarOccurrences`; not a rewrite relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem headBoundVarOccurrences_churchApp (n : Nat) :
    headBoundVarOccurrences (churchApp n) = n := by
  simp only [churchApp, church, headBoundVarOccurrences, headAbstractionBody]
  exact occursAt_churchBody n

/-- Proves: there is a term measure that reads the head abstraction's own variable-occurrence
count and increases by one along the Church family. This reader lies outside the direct-measure
class of `TypedDirectMeasure`, which is application-additive and binder-transparent.
Does not prove: that this measure orients `Step`, or any termination property; it is a separation
fact only.
Relation: not a rewrite relation; a counting function on `SysTTerm`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the Church family `churchApp n`; the witness is `headBoundVarOccurrences`.
-/
theorem churchIndex_measure_separates :
    ∃ μ : SysTTerm → Nat, ∀ n, μ (churchApp (n + 1)) = μ (churchApp n) + 1 :=
  ⟨headBoundVarOccurrences, fun n => by
    rw [headBoundVarOccurrences_churchApp (n + 1),
        headBoundVarOccurrences_churchApp n]⟩

end OperatorKO7.HigherOrderRewritingTypedDirectMeasureBarrier
