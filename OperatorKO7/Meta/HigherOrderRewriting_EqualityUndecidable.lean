import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.HigherOrderRewriting_PrimrecRepresentation
import OperatorKO7.Meta.HigherOrderRewriting_Confluence

/-!
# Extensional equality of closed System T terms of type `nat → nat` is not computable

L7b has landed: every unary `Nat.Primrec` function is represented by a closed System T
term, via `primrecRepresentation`. This module reduces Mathlib's halting problem to
extensional equality `ExtEqNat` against the constant-zero function `zeroFn`. Rice's
theorem does not apply: System T is total. The hardness is Π⁰₁ hardness of
`∀ n, t n = 0`.

Relation: `Step` of the shared System T carrier, and its reflexive-transitive
closure `StepStar`. `ExtEqNat` is joinability of `app t (natLit n)` with
`app u (natLit n)` at every numeral.
Closure: `StepStar` (joinability, not a single-step diamond).
Strategy: full `Step`, not `stepLO`. Confluence of `StepStar` is imported from
`HigherOrderRewriting_Confluence` and is used only to identify the two normal
reducts `natLit (f n)` and `zero`.
Trust: kernel-only plus Mathlib `ComputablePred.halting_problem`,
`Nat.Partrec.Code.primrec_evaln`, `evaln_complete`, and L7b
`primrecRepresentation`. `Classical.choice` appears through `Classical.choose`
of that existence proof. No extra named premise survives: `haltStep` is
primitive recursive in this file, and representation is discharged by L7b.
Item 8 remains conditional on a computable `Code → SysTTerm` map and on an
instance `[Primcodable SysTTerm]` (this lane does not derive that instance).
Scope: closed terms of type `nat → nat`; the predicate is `ExtEqNat · zeroFn`
on the L7b representative of `haltStep c`.

Does not prove: that a computable encoding of `SysTTerm` exists, or that
syntactic equality of System T terms is undecidable without that encoding.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingEqualityUndecidable

open OperatorKO7.HigherOrderRewritingSystemT
open OperatorKO7.HigherOrderRewritingPrimrecRepresentation
open OperatorKO7.HigherOrderRewritingConfluence
open Nat.Partrec.Code

/-! ## NameGate -/

#check Nat.Partrec.Code
#check @Nat.Partrec.Code.eval
#check @Nat.Partrec.Code.evaln
#check @Nat.Partrec.Code.primrec_evaln
#check @Nat.Partrec.Code.evaln_complete
#check @Nat.Partrec.Code.evaln_mono
#check @ComputablePred
#check @ComputablePred.not
#check @ComputablePred.of_eq
#check @ComputablePred.halting_problem
#check @Primrec
#check @Primrec.nat_iff
#check @Nat.Primrec
#check @Represents
#check @primrecRepresentation
#check @Primrec.option_isSome
#check @Primrec.cond
#check @Primrec.ite
#check @stepStar_confluent
#check @normalForm_unique

/-! ## Numerals are normal and rigid -/

/--
Proves: `zero` has no `Step` successor.
Does not prove: normality of any compound term.
Relation: `Step`.
Closure: one step (none exist).
Trust: kernel-only.
Scope: the term `zero`.
-/
theorem isNormal_zero : IsNormal .zero := by
  intro u h
  cases h

/--
Proves: `succ` preserves normality.
Does not prove: normality of `natrec` or application.
Relation: `Step`.
Closure: one step (none exist when the argument is normal).
Trust: kernel-only.
Scope: every `IsNormal` argument of `succ`.
-/
theorem isNormal_succ {t : SysTTerm} (ht : IsNormal t) : IsNormal (.succ t) := by
  intro u h
  cases h with
  | succ h' => exact ht _ h'

/--
Proves: every Church-free numeral `natLit n` is `Step`-normal.
Does not prove: uniqueness of that normal form among all reducts of a term.
Relation: `Step`.
Closure: one step (none exist).
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem isNormal_natLit : ∀ n, IsNormal (natLit n) := by
  intro n
  induction n with
  | zero => exact isNormal_zero
  | succ _n ih => exact isNormal_succ ih

/--
Proves: a normal term is a `StepStar`-fixed point.
Does not prove: existence of a normal form.
Relation: `Step`.
Closure: `StepStar`.
Trust: kernel-only.
Scope: every normal `SysTTerm`.
-/
theorem stepStar_of_isNormal {t u : SysTTerm} (hn : IsNormal t) (h : StepStar t u) :
    u = t := by
  induction h with
  | refl => rfl
  | tail _hstar hstep ih =>
      cases ih
      exact absurd hstep (hn _)

/--
Proves: `natLit` is injective.
Does not prove: injectivity of any other System T encoding.
Relation: equality of `SysTTerm`.
Closure: not applicable.
Trust: kernel-only.
Scope: `natLit : Nat → SysTTerm`.
-/
theorem natLit_injective : Function.Injective natLit := by
  intro m n h
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ _ => cases h
  | succ m ih =>
      cases n with
      | zero => cases h
      | succ n =>
          injection h with h'
          exact congrArg Nat.succ (ih h')

/-! ## The constant-zero function as a System T term -/

/-- The closed term `λx. 0` of type `nat → nat`. -/
def zeroFn : SysTTerm := .lam .nat .zero

/--
Proves: `zeroFn` applied to any numeral beta-reduces to `zero`.
Does not prove: that this is the unique one-step, only that the root beta fires.
Relation: `Step`.
Closure: `StepStar` (exactly one `Step.beta`).
Strategy: full `Step`.
Trust: kernel-only.
Scope: every numeral.
-/
theorem zeroFn_apply : ∀ n, StepStar (.app zeroFn (natLit n)) .zero := by
  intro n
  exact Relation.ReflTransGen.single (Step.beta .nat .zero (natLit n))

/--
Proves: two closed `nat → nat` terms are extensionally equal when, at every
numeral, their applications join under `StepStar`.
Does not prove: syntactic equality, or equality at non-numeral arguments.
Relation: `StepStar` joinability at each numeral.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only.
Scope: every pair of `SysTTerm` (no typing hypothesis).
-/
def ExtEqNat (t u : SysTTerm) : Prop :=
  ∀ n, ∃ v, StepStar (.app t (natLit n)) v ∧ StepStar (.app u (natLit n)) v

/--
Proves: a representing term is extensionally equal to `zeroFn` exactly when the
represented function is identically zero.
Does not prove: uniqueness of the representing term.
Relation: `StepStar` joinability (`ExtEqNat`) against `zeroFn`.
Closure: reflexive-transitive; confluence of `StepStar` identifies the two
normal reducts `natLit (f n)` and `zero`.
Strategy: full `Step`.
Trust: imported `stepStar_confluent` / `normalForm_unique`; numeral rigidity
from this module.
Scope: every `Represents t f`.
-/
theorem represents_extEq_zeroFn_iff {t : SysTTerm} {f : ℕ → ℕ}
    (hrep : Represents t f) :
    ExtEqNat t zeroFn ↔ ∀ n, f n = 0 := by
  constructor
  · intro hjoin n
    obtain ⟨v, htv, hzv⟩ := hjoin n
    obtain ⟨w, hwZ, hwV⟩ := stepStar_confluent (zeroFn_apply n) hzv
    have wZ : w = .zero := stepStar_of_isNormal isNormal_zero hwZ
    have vZ : StepStar v .zero := wZ ▸ hwV
    have htZ : StepStar (.app t (natLit n)) .zero :=
      Relation.ReflTransGen.trans htv vZ
    have hEq : natLit (f n) = .zero :=
      normalForm_unique (hrep.2 n) htZ (isNormal_natLit (f n)) isNormal_zero
    exact natLit_injective (show natLit (f n) = natLit 0 from hEq)
  · intro hf n
    refine ⟨.zero, ?_, zeroFn_apply n⟩
    have hnf : natLit (f n) = .zero := by rw [hf n]; rfl
    exact hnf ▸ hrep.2 n

/-! ## The primitive-recursive halt-step function -/

/-- Indicator of `evaln k c 0`: `1` if the fuelled evaluator of `c` at `0` succeeds
in `k` steps, `0` otherwise. -/
def haltStep (c : Nat.Partrec.Code) (k : ℕ) : ℕ :=
  if (evaln k c 0).isSome then 1 else 0

/--
Proves: `haltStep c` is a unary `Nat.Primrec` function, for every code `c`.
Does not prove: that the map `c ↦ haltStep c` is primitive recursive as a
binary function (only each slice is).
Relation: not a rewrite relation.
Closure: not applicable.
Trust: `Nat.Partrec.Code.primrec_evaln` composed with pairing, constants,
`Primrec.option_isSome`, and `Primrec.cond`, then `Primrec.nat_iff`.
Scope: every `c : Nat.Partrec.Code`.
-/
theorem haltStep_primrec : ∀ c, Nat.Primrec (haltStep c) := by
  intro c
  refine (Primrec.nat_iff (f := haltStep c)).1 ?_
  have hArg : Primrec fun k : ℕ => ((k, c), (0 : ℕ)) :=
    Primrec.pair (Primrec.pair (Primrec.id (α := ℕ)) (Primrec.const c)) (Primrec.const 0)
  have hEval : Primrec fun k : ℕ => evaln k c 0 :=
    primrec_evaln.comp hArg
  have hSome : Primrec fun k : ℕ => (evaln k c 0).isSome :=
    Primrec.option_isSome.comp hEval
  exact (Primrec.cond hSome (Primrec.const (1 : ℕ)) (Primrec.const (0 : ℕ))).of_eq fun k => by
    simp only [haltStep]
    cases (evaln k c 0).isSome <;> rfl

/--
Proves: code `c` halts on input `0` if and only if `haltStep c k = 1` for some fuel `k`.
Does not prove: a bound on that fuel, or anything about inputs other than `0`.
Relation: not a rewrite relation.
Closure: not applicable.
Trust: `evaln_complete`.
Scope: every `c : Nat.Partrec.Code`, input `0`.
-/
theorem halts_iff_exists_haltStep (c : Nat.Partrec.Code) :
    (eval c 0).Dom ↔ ∃ k, haltStep c k = 1 := by
  constructor
  · intro hDom
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hDom
    obtain ⟨k, hk⟩ := (evaln_complete (c := c) (n := 0) (x := x)).mp hx
    refine ⟨k, ?_⟩
    have : (evaln k c 0).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨x, Option.mem_def.mp hk⟩
    simp [haltStep, this]
  · intro ⟨k, hk⟩
    have hs : (evaln k c 0).isSome = true := by
      simp only [haltStep] at hk
      split_ifs at hk with h
      exact h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    exact Part.dom_iff_mem.mpr
      ⟨x, evaln_complete.mpr ⟨k, Option.mem_def.mpr hx⟩⟩

private theorem haltStep_zero_or_one (c : Nat.Partrec.Code) (k : ℕ) :
    haltStep c k = 0 ∨ haltStep c k = 1 := by
  simp only [haltStep]
  cases (evaln k c 0).isSome <;> simp

private theorem forall_haltStep_zero_iff (c : Nat.Partrec.Code) :
    (∀ n, haltStep c n = 0) ↔ ¬ (eval c 0).Dom := by
  rw [halts_iff_exists_haltStep]
  constructor
  · intro hall ⟨k, hk⟩
    have hk0 := hall k
    simp [hk0] at hk
  · intro hnone n
    cases haltStep_zero_or_one c n with
    | inl h0 => exact h0
    | inr h1 => exact absurd ⟨n, h1⟩ hnone

private theorem extEq_zeroFn_iff_not_halts {t : SysTTerm} {c : Nat.Partrec.Code}
    (hrep : Represents t (haltStep c)) :
    ExtEqNat t zeroFn ↔ ¬ (eval c 0).Dom :=
  (represents_extEq_zeroFn_iff hrep).trans (forall_haltStep_zero_iff c)

private theorem computablePred_of_not_halts_of_iff
    {p : Nat.Partrec.Code → Prop}
    (hp : ComputablePred p)
    (hIff : ∀ c, p c ↔ ¬ (eval c 0).Dom) :
    False := by
  have hHalt : ComputablePred fun c => (eval c 0).Dom :=
    ComputablePred.of_eq (ComputablePred.not hp) fun c => by
      constructor
      · intro hnP
        by_contra hnd
        exact hnP ((hIff c).mpr hnd)
      · intro hDom hnP
        exact (hIff c).mp hnP hDom
  exact ComputablePred.halting_problem 0 hHalt

/--
Proves: extensional equality of the L7b representative of `haltStep c` with
`zeroFn` is not a `ComputablePred` on `Nat.Partrec.Code`.
Does not prove: that `ExtEqNat` on arbitrary term pairs is uncomputable
(that is the next theorem, and it needs a computable `Code → SysTTerm` map).
The representation premise of the original L7a plan is discharged:
`primrecRepresentation` supplies the term, so this theorem is unconditional.
Relation: `ExtEqNat` against `zeroFn`, on `StepStar`.
Closure: reflexive-transitive joinability at every numeral.
Strategy: full `Step`.
Trust: `primrecRepresentation` (L7b, proven), `haltStep_primrec` (this file),
`ComputablePred.halting_problem 0`, `Classical.choose`.
Scope: the family `c ↦ ExtEqNat (choose (primrecRepresentation (haltStep c) _)) zeroFn`.
-/
theorem systemT_natFun_equality_not_computable_of_representation :
    ¬ ComputablePred
        (fun c : Nat.Partrec.Code =>
          ExtEqNat
            (Classical.choose (primrecRepresentation (haltStep c) (haltStep_primrec c)))
            zeroFn) := by
  intro hP
  refine computablePred_of_not_halts_of_iff hP fun c => ?_
  exact extEq_zeroFn_iff_not_halts
    (Classical.choose_spec (primrecRepresentation (haltStep c) (haltStep_primrec c)))

/--
Proves: if `SysTTerm` is `Primcodable` and there is a computable map from codes
to System T terms that represents `haltStep`, then `ExtEqNat` on term pairs is
not a `ComputablePred`.
Does not prove: that `Primcodable SysTTerm` holds, or that such a computable map
exists. Both remain explicit hypotheses. This lane does not derive
`Primcodable SysTTerm`.
Relation: `ExtEqNat` on `SysTTerm × SysTTerm`.
Closure: reflexive-transitive joinability at every numeral.
Strategy: full `Step`.
Trust: the same reduction as
`systemT_natFun_equality_not_computable_of_representation`, composed with the
computable map.
Scope: every instance `[Primcodable SysTTerm]` and every computable
representing family `T`.
-/
theorem systemT_natFun_equality_undecidable_of_representation_and_computable_code
    [Primcodable SysTTerm]
    (hT : ∃ T : Nat.Partrec.Code → SysTTerm,
      Computable T ∧ ∀ c, Represents (T c) (haltStep c)) :
    ¬ ComputablePred (fun p : SysTTerm × SysTTerm => ExtEqNat p.1 p.2) := by
  intro hPred
  obtain ⟨T, hTComp, hTRep⟩ := hT
  have hSlice : ComputablePred fun c : Nat.Partrec.Code => ExtEqNat (T c) zeroFn := by
    obtain ⟨decPair, hCompPair⟩ := hPred
    refine ⟨fun c => decPair (T c, zeroFn), ?_⟩
    exact hCompPair.comp (Computable.pair hTComp (Computable.const zeroFn))
  exact computablePred_of_not_halts_of_iff hSlice fun c =>
    extEq_zeroFn_iff_not_halts (hTRep c)

/-! ## Non-vacuity -/

/--
Proves: `evaln` of the constant-zero code at fuel `0` yields `haltStep = 0`.
Does not prove: the value at any positive fuel.
Relation: not a rewrite relation.
Closure: not applicable.
Trust: kernel unfolding of `evaln`.
Scope: `Code.zero`, fuel `0`.
-/
theorem haltStep_zero_at_zero : haltStep zero 0 = 0 := by
  simp [haltStep, evaln]

/--
Proves: `evaln` of the constant-zero code at fuel `1` succeeds, so `haltStep = 1`.
Does not prove: a general closed form for `haltStep`.
Relation: not a rewrite relation.
Closure: not applicable.
Trust: kernel unfolding of `evaln`.
Scope: `Code.zero`, fuel `1`.
-/
theorem haltStep_zero_at_one : haltStep zero 1 = 1 := by
  simp [haltStep, evaln, Bind.bind, Pure.pure]

/--
Proves: `zeroFn` represents the constant-zero function.
Does not prove: that `zeroFn` is the term `Classical.choose` returns for that
function.
Relation: `HasType [] zeroFn (nat → nat)` and `StepStar` of application to
numerals.
Closure: reflexive-transitive (one beta).
Strategy: full `Step`.
Trust: kernel-only.
Scope: the term `zeroFn`.
-/
theorem represents_zeroFn : Represents zeroFn (fun _ => 0) :=
  ⟨HasType.lam HasType.zero, zeroFn_apply⟩

#print axioms systemT_natFun_equality_not_computable_of_representation

end OperatorKO7.HigherOrderRewritingEqualityUndecidable
