import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

/-!
# Gradual typing cast boundary

Calculus. Types `GTy := nat | bool | dyn`. Terms `GTm := litN n | litB b | succ t | toDyn t | fromDyn A t`.
Static typing `HasGTy`: `litN n : nat`, `litB b : bool`, `succ t : nat` when `t : nat`, `toDyn t : dyn`
when `t : nat` or `t : bool`, `fromDyn A t : A` when `t : dyn` and `A ≠ dyn`. Values
`GVal := vN n | vB b | vD tag v`, where `vD` stores the run-time tag. Evaluation: `litN n` maps to
`vN n`; `litB b` maps to `vB b`; `succ t` maps to `vN (n+1)` when `eval t = some (vN n)`, else `none`;
`toDyn t` maps to `vD nat v` or `vD bool v` from a natural or Boolean value, else `none`;
`fromDyn A t` maps to `v` when `eval t = some (vD A v)`, and to `none` when the tag is not `A`.

This is the framework's lift-or-refuse on the gradual-typing boundary of Siek and Taha (2006).
Two programs of static type `nat` can differ on whether they fail at a cast. The local tag check
inside the cast is the licensed channel (pay). The cast-free fragment is safe outright (refuse).

The blame theorem of Wadler and Findler (2009) is the ESTABLISHED transport statement relating
cast failure to blame. It is cited here only as background and is never re-derived. This module
proves the static-type collision, the local cast-tag license, and cast-free safety only.

Relation: equality on static-type observations and equality on augmented cast observations.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-checked Lean only; no external theorem is re-derived or assumed.
Scope: the calculus and local cast boundary defined in this file; no general gradual-language
      blame theorem or contextual equivalence theorem is claimed.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.GradualCastBoundary

open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.Confusability
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

#check @OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive.TypedBoundary
#check @OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive.TypedBoundary.verdict_not_observation_function
#check @OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary.OperationallyInexpressibleAt
#check @OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel.FactorsThrough
#check @OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary.not_factorsThrough_of_collision
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.Licensed
#check @OperatorKO7.Meta.OperationalInexpressibility.Confusability.augmentObserver
#check @OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse.LicensedOn

/-- The three gradual types used by the local calculus. -/
inductive GTy : Type where
  | nat : GTy
  | bool : GTy
  | dyn : GTy

/-- Terms of the local gradual calculus. -/
inductive GTm : Type where
  | litN : Nat → GTm
  | litB : Bool → GTm
  | succ : GTm → GTm
  | toDyn : GTm → GTm
  | fromDyn : GTy → GTm → GTm

/-- Static typing for the local gradual calculus. -/
inductive HasGTy : GTm → GTy → Prop where
  | litN (n : Nat) : HasGTy (.litN n) .nat
  | litB (b : Bool) : HasGTy (.litB b) .bool
  | succ {t : GTm} : HasGTy t .nat → HasGTy (.succ t) .nat
  | toDynNat {t : GTm} : HasGTy t .nat → HasGTy (.toDyn t) .dyn
  | toDynBool {t : GTm} : HasGTy t .bool → HasGTy (.toDyn t) .dyn
  | fromDyn {A : GTy} {t : GTm} : HasGTy t .dyn → A ≠ .dyn → HasGTy (.fromDyn A t) A

/-- Run-time values. A dynamic value stores both its tag and payload. -/
inductive GVal : Type where
  | vN : Nat → GVal
  | vB : Bool → GVal
  | vD : GTy → GVal → GVal

/-- Static type inference for the local calculus. -/
def infer : GTm → Option GTy
  | .litN _ => some .nat
  | .litB _ => some .bool
  | .succ t =>
      match infer t with
      | some .nat => some .nat
      | _ => none
  | .toDyn t =>
      match infer t with
      | some .nat => some .dyn
      | some .bool => some .dyn
      | _ => none
  | .fromDyn .nat t =>
      match infer t with
      | some .dyn => some .nat
      | _ => none
  | .fromDyn .bool t =>
      match infer t with
      | some .dyn => some .bool
      | _ => none
  | .fromDyn .dyn _ => none

/--
Proves: successful inference yields the corresponding static typing derivation.
Does not prove: evaluation safety or cast success.
Relation: `HasGTy`, the static typing judgment of this module.
Closure: not applicable.
Strategy: structural induction on the term.
Trust: kernel-checked Lean only.
Scope: all terms and all three gradual types.
-/
theorem infer_sound {t : GTm} {A : GTy} (h : infer t = some A) : HasGTy t A := by
  induction t generalizing A with
  | litN n =>
      cases h
      exact HasGTy.litN n
  | litB b =>
      cases h
      exact HasGTy.litB b
  | succ t ih =>
      cases ht : infer t with
      | none =>
          simp [infer, ht] at h
      | some B =>
          cases B with
          | nat =>
              simp [infer, ht] at h
              cases h
              exact HasGTy.succ (ih ht)
          | bool =>
              simp [infer, ht] at h
          | dyn =>
              simp [infer, ht] at h
  | toDyn t ih =>
      cases ht : infer t with
      | none =>
          simp [infer, ht] at h
      | some B =>
          cases B with
          | nat =>
              simp [infer, ht] at h
              cases h
              exact HasGTy.toDynNat (ih ht)
          | bool =>
              simp [infer, ht] at h
              cases h
              exact HasGTy.toDynBool (ih ht)
          | dyn =>
              simp [infer, ht] at h
  | fromDyn B t ih =>
      cases B with
      | nat =>
          cases ht : infer t with
          | none =>
              simp [infer, ht] at h
          | some C =>
              cases C with
              | nat =>
                  simp [infer, ht] at h
              | bool =>
                  simp [infer, ht] at h
              | dyn =>
                  simp [infer, ht] at h
                  cases h
                  exact HasGTy.fromDyn (ih ht) (by
                    intro hbad
                    cases hbad)
      | bool =>
          cases ht : infer t with
          | none =>
              simp [infer, ht] at h
          | some C =>
              cases C with
              | nat =>
                  simp [infer, ht] at h
              | bool =>
                  simp [infer, ht] at h
              | dyn =>
                  simp [infer, ht] at h
                  cases h
                  exact HasGTy.fromDyn (ih ht) (by
                    intro hbad
                    cases hbad)
      | dyn =>
          simp [infer] at h

/--
Proves: every static typing derivation is reproduced by `infer`.
Does not prove: evaluation safety or cast success.
Relation: `HasGTy`, the static typing judgment of this module.
Closure: not applicable.
Strategy: induction on the typing derivation.
Trust: kernel-checked Lean only.
Scope: all terms and all three gradual types.
-/
theorem infer_complete {t : GTm} {A : GTy} (h : HasGTy t A) : infer t = some A := by
  induction h with
  | litN => rfl
  | litB => rfl
  | succ _ ih =>
      simp [infer, ih]
  | toDynNat _ ih =>
      simp [infer, ih]
  | toDynBool _ ih =>
      simp [infer, ih]
  | @fromDyn A t _ hA ih =>
      cases A with
      | nat =>
          simp [infer, ih]
      | bool =>
          simp [infer, ih]
      | dyn =>
          exact (hA rfl).elim

/-- Big-step evaluator. Cast failure and any ill-shaped primitive use return `none`. -/
def eval : GTm → Option GVal
  | .litN n => some (.vN n)
  | .litB b => some (.vB b)
  | .succ t =>
      match eval t with
      | some (.vN n) => some (.vN (n + 1))
      | _ => none
  | .toDyn t =>
      match eval t with
      | some (.vN n) => some (.vD .nat (.vN n))
      | some (.vB b) => some (.vD .bool (.vB b))
      | _ => none
  | .fromDyn .nat t =>
      match eval t with
      | some (.vD .nat v) => some v
      | _ => none
  | .fromDyn .bool t =>
      match eval t with
      | some (.vD .bool v) => some v
      | _ => none
  | .fromDyn .dyn t =>
      match eval t with
      | some (.vD .dyn v) => some v
      | _ => none

/-- Evaluation safety means that evaluation returns a value rather than cast failure. -/
def Safe (t : GTm) : Prop := (eval t).isSome

/-- Executable safety observation. -/
def safe? : GTm → Bool := fun t => (eval t).isSome

/-- A well-tagged dynamic natural cast that succeeds. -/
def good : GTm := .fromDyn .nat (.toDyn (.litN 3))

/-- A statically identical natural cast whose run-time Boolean tag makes the cast fail. -/
def bad : GTm := .fromDyn .nat (.toDyn (.litB true))

/--
Proves: `good` has inferred static type `nat`.
Does not prove: that all terms inferred as `nat` are safe.
Relation: equality of inferred types.
Closure: not applicable.
Strategy: computation by the definitions.
Trust: kernel-checked Lean only.
Scope: the concrete term `good`.
-/
theorem infer_good : infer good = some .nat := by
  rfl

/--
Proves: `bad` also has inferred static type `nat`.
Does not prove: run-time cast safety for `bad`.
Relation: equality of inferred types.
Closure: not applicable.
Strategy: computation by the definitions.
Trust: kernel-checked Lean only.
Scope: the concrete term `bad`.
-/
theorem infer_bad : infer bad = some .nat := by
  rfl

/--
Proves: `good` evaluates to the natural value three.
Does not prove: a general cast-safety theorem.
Relation: big-step evaluation `eval`.
Closure: not applicable.
Strategy: computation by the definitions.
Trust: kernel-checked Lean only.
Scope: the concrete term `good`.
-/
theorem eval_good : eval good = some (.vN 3) := by
  rfl

/--
Proves: `bad` fails at its run-time cast.
Does not prove: that every cast from `dyn` to `nat` fails.
Relation: big-step evaluation `eval`.
Closure: not applicable.
Strategy: computation by the definitions.
Trust: kernel-checked Lean only.
Scope: the concrete term `bad`.
-/
theorem eval_bad : eval bad = none := by
  rfl

/--
Proves: the static observer `infer` collides on `good` and `bad` while `safe?` separates them.
Does not prove: a collision for every static type or every gradual language.
Relation: observer-fiber collision for `infer` and target `safe?`.
Closure: not applicable.
Strategy: explicit two-term witness.
Trust: kernel-checked Lean only.
Scope: the concrete terms `good` and `bad`.
-/
theorem static_type_collides : OperationallyInexpressibleAt infer safe? good bad := by
  exact ⟨rfl, by decide⟩

/--
Proves: run-time safety does not factor through the static type observer alone.
Does not prove: that static typing gives no useful safety information.
Relation: `FactorsThrough infer safe?`.
Closure: not applicable.
Strategy: the explicit collision and `not_factorsThrough_of_collision`.
Trust: kernel-checked Lean only.
Scope: this local gradual calculus.
-/
theorem static_type_does_not_license_safety : ¬ FactorsThrough infer safe? := by
  exact not_factorsThrough_of_collision static_type_collides

/-- The collision packaged as the universal typed-boundary primitive. -/
def gradualBoundary : TypedBoundary where
  State := GTm
  Obs := Option GTy
  Verdict := Bool
  observe := infer
  verdict := safe?
  s₁ := good
  s₂ := bad
  obs_eq := rfl
  verdict_ne := by decide

/--
Proves: the gradual cast collision obeys the universal boundary law.
Does not prove: a general theorem about all gradual calculi.
Relation: the `TypedBoundary` observation and verdict functions.
Closure: not applicable.
Strategy: specialization of `TypedBoundary.verdict_not_observation_function`.
Trust: kernel-checked Lean only.
Scope: `gradualBoundary`.
-/
theorem gradualBoundary_obeys_law :
    ¬ ∃ f : gradualBoundary.Obs → gradualBoundary.Verdict,
      ∀ s : gradualBoundary.State,
        gradualBoundary.verdict s = f (gradualBoundary.observe s) :=
  TypedBoundary.verdict_not_observation_function gradualBoundary

/-- The local run-time tag inspected by a cast, without evaluating the cast itself. -/
def castTag : GTm → Option GTy
  | .fromDyn _ u =>
      match eval u with
      | some (.vD tag _) => some tag
      | _ => none
  | _ => none

/--
Proves: a cast succeeds exactly when the dynamic argument exposes the requested run-time tag.
Does not prove: a whole-program blame theorem or a property of casts in another calculus.
Relation: equality between the cast's requested type and the local run-time tag.
Closure: not applicable.
Strategy: case analysis on the evaluated dynamic argument and requested type.
Trust: kernel-checked Lean only.
Scope: every `fromDyn A u` term of this local calculus.
-/
theorem tag_licenses_cast_safety (A : GTy) (u : GTm) :
    safe? (.fromDyn A u) = true ↔ castTag (.fromDyn A u) = some A := by
  cases hu : eval u with
  | none =>
      cases A <;> simp [safe?, eval, castTag, hu]
  | some v =>
      cases v with
      | vN n =>
          cases A <;> simp [safe?, eval, castTag, hu]
      | vB b =>
          cases A <;> simp [safe?, eval, castTag, hu]
      | vD tag v =>
          cases tag <;> cases A <;> simp [safe?, eval, castTag, hu]

private inductive ValHasGTy : GVal → GTy → Prop where
  | nat (n : Nat) : ValHasGTy (.vN n) .nat
  | bool (b : Bool) : ValHasGTy (.vB b) .bool
  | dynNat (n : Nat) : ValHasGTy (.vD .nat (.vN n)) .dyn
  | dynBool (b : Bool) : ValHasGTy (.vD .bool (.vB b)) .dyn

private theorem eval_hasGTy {t : GTm} {A : GTy} {v : GVal}
    (ht : HasGTy t A) (he : eval t = some v) : ValHasGTy v A := by
  induction ht generalizing v with
  | litN n =>
      simp [eval] at he
      cases he
      exact ValHasGTy.nat n
  | litB b =>
      simp [eval] at he
      cases he
      exact ValHasGTy.bool b
  | @succ t ht ih =>
      cases hu : eval t with
      | none =>
          simp [eval, hu] at he
      | some w =>
          have hw := ih hu
          cases hw with
          | nat n =>
              simp [eval, hu] at he
              cases he
              exact ValHasGTy.nat (n + 1)
  | @toDynNat t ht ih =>
      cases hu : eval t with
      | none =>
          simp [eval, hu] at he
      | some w =>
          have hw := ih hu
          cases hw with
          | nat n =>
              simp [eval, hu] at he
              cases he
              exact ValHasGTy.dynNat n
  | @toDynBool t ht ih =>
      cases hu : eval t with
      | none =>
          simp [eval, hu] at he
      | some w =>
          have hw := ih hu
          cases hw with
          | bool b =>
              simp [eval, hu] at he
              cases he
              exact ValHasGTy.dynBool b
  | @fromDyn A t ht hA ih =>
      cases hu : eval t with
      | none =>
          cases A <;> simp [eval, hu] at he
      | some w =>
          have hw := ih hu
          cases hw with
          | dynNat n =>
              cases A with
              | nat =>
                  simp [eval, hu] at he
                  cases he
                  exact ValHasGTy.nat n
              | bool =>
                  simp [eval, hu] at he
              | dyn =>
                  exact (hA rfl).elim
          | dynBool b =>
              cases A with
              | nat =>
                  simp [eval, hu] at he
              | bool =>
                  simp [eval, hu] at he
                  cases he
                  exact ValHasGTy.bool b
              | dyn =>
                  exact (hA rfl).elim

private theorem eval_some_of_safe_true {t : GTm} (h : safe? t = true) :
    ∃ v, eval t = some v := by
  cases he : eval t with
  | none =>
      simp [safe?, he] at h
  | some v =>
      exact ⟨v, rfl⟩

private theorem eval_typed_of_infer_safe {t : GTm} {A : GTy}
    (hi : infer t = some A) (hs : safe? t = true) :
    ∃ v, eval t = some v ∧ ValHasGTy v A := by
  obtain ⟨v, hv⟩ := eval_some_of_safe_true hs
  exact ⟨v, hv, eval_hasGTy (infer_sound hi) hv⟩

/-- Immediate subterms are safe at the points where this local calculus has one immediate operand. -/
def ImmediateSubtermsSafe : GTm → Prop
  | .litN _ => True
  | .litB _ => True
  | .succ u => safe? u = true
  | .toDyn u => safe? u = true
  | .fromDyn _ u => safe? u = true

/-- The retained set for the pay branch: statically well-typed terms with safe immediate operands. -/
def wellTypedImmediateSafe : Set GTm :=
  {t | (∃ A, infer t = some A) ∧ ImmediateSubtermsSafe t}

private def localSafetyDecoder : Option GTy × Option GTy → Bool
  | (some .nat, some .nat) => true
  | (some .bool, some .bool) => true
  | (some .dyn, some .dyn) => true
  | (some _, some _) => false
  | (some _, none) => true
  | (none, _) => false

private theorem localSafetyDecoder_correct {t : GTm}
    (ht : t ∈ wellTypedImmediateSafe) :
    safe? t = localSafetyDecoder (augmentObserver infer castTag t) := by
  rcases ht with ⟨⟨A, hi⟩, himm⟩
  have hty : HasGTy t A := infer_sound hi
  cases hty with
  | litN n =>
      rfl
  | litB b =>
      rfl
  | succ hu =>
      have hui : infer _ = some .nat := infer_complete hu
      obtain ⟨v, hev, hvty⟩ := eval_typed_of_infer_safe hui himm
      cases hvty with
      | nat n =>
          simp [safe?, eval, hev, augmentObserver, castTag, localSafetyDecoder, infer, hui]
  | toDynNat hu =>
      have hui : infer _ = some .nat := infer_complete hu
      obtain ⟨v, hev, hvty⟩ := eval_typed_of_infer_safe hui himm
      cases hvty with
      | nat n =>
          simp [safe?, eval, hev, augmentObserver, castTag, localSafetyDecoder, infer, hui]
  | toDynBool hu =>
      have hui : infer _ = some .bool := infer_complete hu
      obtain ⟨v, hev, hvty⟩ := eval_typed_of_infer_safe hui himm
      cases hvty with
      | bool b =>
          simp [safe?, eval, hev, augmentObserver, castTag, localSafetyDecoder, infer, hui]
  | @fromDyn B u hu hB =>
      have hui : infer u = some .dyn := infer_complete hu
      obtain ⟨v, hev, hvty⟩ := eval_typed_of_infer_safe hui himm
      cases hvty with
      | dynNat n =>
          cases A with
          | nat =>
              simp [safe?, eval, hev, augmentObserver, castTag, localSafetyDecoder, infer, hui]
          | bool =>
              simp [safe?, eval, hev, augmentObserver, castTag, localSafetyDecoder, infer, hui]
          | dyn =>
              exact (hB rfl).elim
      | dynBool b =>
          cases A with
          | nat =>
              simp [safe?, eval, hev, augmentObserver, castTag, localSafetyDecoder, infer, hui]
          | bool =>
              simp [safe?, eval, hev, augmentObserver, castTag, localSafetyDecoder, infer, hui]
          | dyn =>
              exact (hB rfl).elim

/--
Proves: static type plus the local cast tag licenses safety on well-typed terms with safe immediate operands.
Does not prove: a global license on arbitrary terms or a blame theorem.
Relation: `LicensedOn wellTypedImmediateSafe (augmentObserver infer castTag) safe?`.
Closure: restricted to the retained set `wellTypedImmediateSafe`.
Strategy: decode safety from the augmented observation and use observer equality.
Trust: kernel-checked Lean only.
Scope: the local three-type calculus and the stated retained set.
-/
theorem augmented_observer_licenses :
    LicensedOn wellTypedImmediateSafe (augmentObserver infer castTag) safe? := by
  intro x hx y hy hxy
  calc
    safe? x = localSafetyDecoder (augmentObserver infer castTag x) :=
      localSafetyDecoder_correct hx
    _ = localSafetyDecoder (augmentObserver infer castTag y) :=
      congrArg localSafetyDecoder hxy
    _ = safe? y := (localSafetyDecoder_correct hy).symm

/-- Cast-free terms contain only literals and natural successor. -/
inductive CastFree : GTm → Prop where
  | litN (n : Nat) : CastFree (.litN n)
  | litB (b : Bool) : CastFree (.litB b)
  | succ {t : GTm} : CastFree t → CastFree (.succ t)

/--
Proves: every cast-free statically well-typed term evaluates without cast failure.
Does not prove: that every well-typed term with casts is safe.
Relation: `HasGTy` and big-step evaluation `eval`.
Closure: structural closure generated by `CastFree`.
Strategy: induction on the cast-free syntax witness and inversion of static typing.
Trust: kernel-checked Lean only.
Scope: every local term `t` and type `A` with exactly the displayed two premises.
-/
theorem castFree_wellTyped_safe {t : GTm} {A : GTy}
    (hfree : CastFree t) (ht : HasGTy t A) : Safe t := by
  induction hfree generalizing A with
  | litN n =>
      cases ht
      simp [Safe, eval]
  | litB b =>
      cases ht
      simp [Safe, eval]
  | @succ t hfree ih =>
      cases ht with
      | succ hu =>
          have hs : Safe t := ih hu
          cases he : eval t with
          | none =>
              simp [Safe, he] at hs
          | some v =>
              have hvty := eval_hasGTy hu he
              cases hvty with
              | nat n =>
                  simp [Safe, eval, he]

/--
Proves: the calculus contains positive and negative witnesses for the static collision and cast-free safety claims.
Does not prove: completeness of these examples or a theorem about another gradual language.
Relation: static typing `HasGTy`, inference `infer`, evaluation safety `Safe`, and `CastFree`.
Closure: not applicable.
Strategy: explicit constructor witnesses and decidable evaluation fixtures.
Trust: kernel-checked Lean only.
Scope: `good`, `bad`, one ill-typed successor, and one cast-free natural successor.
-/
theorem nonvacuity_fixtures :
    HasGTy good .nat ∧ Safe good ∧
      HasGTy bad .nat ∧ ¬ Safe bad ∧
      infer (.succ (.litB true)) = none ∧ ¬ Safe (.succ (.litB true)) ∧
      CastFree (.succ (.litN 1)) ∧ HasGTy (.succ (.litN 1)) .nat ∧
      Safe (.succ (.litN 1)) := by
  refine ⟨infer_sound infer_good, ?_, infer_sound infer_bad, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Safe, good, eval]
  · simp [Safe, bad, eval]
  · simp [Safe, eval]
  · exact CastFree.succ (CastFree.litN 1)
  · exact HasGTy.succ (HasGTy.litN 1)
  · simp [Safe, eval]

end OperatorKO7.Meta.UniversalBoundary.GradualCastBoundary
