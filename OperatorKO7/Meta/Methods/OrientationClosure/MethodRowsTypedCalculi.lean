import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsPathOrders
import Mathlib.Tactic

/-!
# Typed-calculi method rows (Tier C fragment theorems)

Rows: `horpoAdmittance`, `cpoAdmittance`, `generalSchemaAdmittance`, `sizedTypesAdmittance`.

Subject: Gödel's System T recursor `rec(b, s, 0) → b`, `rec(b, s, S n) → @(@(s, n), rec(b, s, n))`
over simply typed applicative terms (sorts, arrow types, typed variables, typed function symbols of
fixed arity, binary application `@`), and the free recursor as its first-order shadow: the adapter
`toA` reads the free wrapper `wrap(s, y)` as the application `@(s, y)`, which turns the free
two-rule system into the typed iterator rules `iter(b, s, 0) → b`, `iter(b, s, S n) → @(s, iter(b, s, n))`.

Each row implements the clauses of its pinned source that the recursor rule needs, proves
admission from those clauses, and proves fragment soundness through an embedding into the recursive
path order of `MethodRowsPathOrders` (application minimal in the precedence), whose
well-foundedness is `RPO.wf`. No row uses the termination already proved for the free recursor.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders

/-! ## 1. Simple types, typed signatures and applicative terms -/

/-- Simple types over a set of sorts (Blanqui, Jouannaud and Rubio, LMCS 11(4:3) 2015,
Definition 2.1; Jouannaud and Rubio, J. ACM 54(1) 2007, Section 2). -/
inductive HTy (S : Type) : Type where
  | sort (a : S)
  | arrow (A B : HTy S)
  deriving DecidableEq

/-- Structural size of a type. -/
def HTy.size {S : Type} : HTy S → Nat
  | .sort _ => 1
  | .arrow A B => A.size + B.size + 1

/-- Codomain of an optional arrow type. -/
def HTy.cod? {S : Type} : Option (HTy S) → Option (HTy S)
  | some (.arrow _ B) => some B
  | _ => none

/-- Applicative symbols: a function symbol of fixed arity, or binary application `@`. -/
inductive ASym (F : Type) : Type where
  | fn (f : F)
  | ap
  deriving DecidableEq

/-- A typed signature: the argument types and the output type of every function symbol
(J. ACM 2007, Section 2: `f : σ₁ × … × σₙ ⇒ σ`; LMCS 2015, Definition 3.1). -/
structure TSig (S F : Type) : Type where
  dom : F → List (HTy S)
  cod : F → HTy S

section Typing

variable {S F V : Type}

mutual
/-- The type of an applicative term under the variable typing `Γ`: a variable has its declared
type, `f(t⃗)` the output type of `f`, and `@(t, u)` the codomain of the type of `t`. -/
def tyOf (sig : TSig S F) (Γ : V → HTy S) : Term (ASym F) V → Option (HTy S)
  | .var x => some (Γ x)
  | .app (.fn f) _ => some (sig.cod f)
  | .app .ap args => tyOfAp sig Γ args
/-- The type of an application from its argument list `[t, u]`. -/
def tyOfAp (sig : TSig S F) (Γ : V → HTy S) : List (Term (ASym F) V) → Option (HTy S)
  | [t, _] => HTy.cod? (tyOf sig Γ t)
  | _ => none
end

theorem tyOf_var (sig : TSig S F) (Γ : V → HTy S) (x : V) :
    tyOf sig Γ (.var x : Term (ASym F) V) = some (Γ x) := rfl

theorem tyOf_fn (sig : TSig S F) (Γ : V → HTy S) (f : F) (args : List (Term (ASym F) V)) :
    tyOf sig Γ (.app (.fn f) args) = some (sig.cod f) := rfl

theorem tyOf_ap (sig : TSig S F) (Γ : V → HTy S) (t u : Term (ASym F) V) :
    tyOf sig Γ (.app .ap [t, u]) = HTy.cod? (tyOf sig Γ t) := rfl

/-- The typing judgment of simply typed applicative terms (J. ACM 2007, Figure 1, restricted to
variables, function symbols and application). -/
inductive HasTy (sig : TSig S F) (Γ : V → HTy S) : Term (ASym F) V → HTy S → Prop
  | var (x : V) : HasTy sig Γ (.var x) (Γ x)
  | fn (f : F) (args : List (Term (ASym F) V)) (hlen : args.length = (sig.dom f).length)
      (hargs : ∀ p ∈ args.zip (sig.dom f), HasTy sig Γ p.1 p.2) :
      HasTy sig Γ (.app (.fn f) args) (sig.cod f)
  | ap {t u : Term (ASym F) V} {A B : HTy S} (ht : HasTy sig Γ t (.arrow A B))
      (hu : HasTy sig Γ u A) : HasTy sig Γ (.app .ap [t, u]) B

/-- A typable term has the type computed by `tyOf`. -/
theorem HasTy.tyOf_eq {sig : TSig S F} {Γ : V → HTy S} {t : Term (ASym F) V} {A : HTy S}
    (h : HasTy sig Γ t A) : tyOf sig Γ t = some A := by
  induction h with
  | var x => rfl
  | fn f args _ _ _ => rfl
  | ap _ _ iht _ => rw [tyOf_ap, iht]; rfl

/-- Equal types, both defined: the type condition of terms of equivalent types (Jouannaud and
Rubio, LICS 1999, Section 3.1). -/
def TyEq (sig : TSig S F) (Γ : V → HTy S) (s t : Term (ASym F) V) : Prop :=
  ∃ σ, tyOf sig Γ s = some σ ∧ tyOf sig Γ t = some σ

/-- Partial left-flattening: `t = @(t₁, …, tₙ)` with `n ≥ 2`, that is, `t` is `t₁` applied to
`t₂, …, tₙ` in this order (LICS 1999, Definition 3.1 case 5; J. ACM 2007, Definition 3.1
case 7). -/
inductive LeftFlat : Term (ASym F) V → List (Term (ASym F) V) → Prop
  | two (t u : Term (ASym F) V) : LeftFlat (.app .ap [t, u]) [t, u]
  | more {t : Term (ASym F) V} {ts : List (Term (ASym F) V)} (u : Term (ASym F) V)
      (h : LeftFlat t ts) : LeftFlat (.app .ap [t, u]) (ts ++ [u])

end Typing

/-! ## 2. Applicative rewriting and the recursive path order with application minimal -/

section Rewriting

variable {F RV : Type}

/-- Root steps of a list of rule schemas over rule variables `RV`, at terms over `ν`. -/
inductive ARoot {ν : Type} (R : List (Term (ASym F) RV × Term (ASym F) RV)) :
    Term (ASym F) ν → Term (ASym F) ν → Prop
  | inst {l r : Term (ASym F) RV} (hmem : (l, r) ∈ R) (θ : RV → Term (ASym F) ν) :
      ARoot R (tbind θ l) (tbind θ r)

/-- Applicative rewriting: root steps closed under the argument positions of function symbols
and under both positions of application. -/
inductive AStep {ν : Type} (R : List (Term (ASym F) RV × Term (ASym F) RV)) :
    Term (ASym F) ν → Term (ASym F) ν → Prop
  | root {t u : Term (ASym F) ν} (h : ARoot R t u) : AStep R t u
  | arg (f : ASym F) (pre post : List (Term (ASym F) ν)) {a b : Term (ASym F) ν}
      (h : AStep R a b) : AStep R (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

/-- Precedence on applicative symbols: function symbols compare by `pr`, and application lies
below every function symbol. `apPrec pr a b` means that `a` lies below `b`. -/
def apPrec (pr : F → F → Prop) : ASym F → ASym F → Prop
  | .fn g, .fn f => pr g f
  | .ap, .fn _ => True
  | _, .ap => False

theorem apPrec_wf {pr : F → F → Prop} (hwf : WellFounded pr) : WellFounded (apPrec pr) := by
  have hap : Acc (apPrec pr) ASym.ap := Acc.intro _ fun y hy => by
    cases y <;> exact (hy : False).elim
  have hfn : ∀ f, Acc (apPrec pr) (ASym.fn f) := fun f =>
    WellFounded.induction hwf f (C := fun f => Acc (apPrec pr) (ASym.fn f)) fun f ih =>
      Acc.intro _ fun y hy => by
        cases y with
        | fn g => exact ih g hy
        | ap => exact hap
  exact ⟨fun a => by
    cases a with
    | fn f => exact hfn f
    | ap => exact hap⟩

theorem apPrec_trans {pr : F → F → Prop} (htr : ∀ a b c, pr a b → pr b c → pr a c) :
    ∀ a b c : ASym F, apPrec pr a b → apPrec pr b c → apPrec pr a c := by
  intro a b c h₁ h₂
  rcases a with a | _ <;> rcases b with b | _ <;> rcases c with c | _
  · exact htr a b c h₁ h₂
  · exact (h₂ : False).elim
  · exact (h₁ : False).elim
  · exact (h₁ : False).elim
  · exact trivial
  · exact (h₂ : False).elim
  · exact (h₁ : False).elim
  · exact (h₁ : False).elim

/-- Rewrite steps of a rule list oriented by the recursive path order decrease in it: stability
under substitution (`RPO.bind`) and closure under argument contexts (`RPO.mono_arg`). -/
theorem AStep.rpo {pr : ASym F → ASym F → Prop} {st : ASym F → ArgStatus} {ν : Type}
    {R : List (Term (ASym F) RV × Term (ASym F) RV)} (hR : ∀ lr ∈ R, RPO pr st lr.1 lr.2)
    {t u : Term (ASym F) ν} (h : AStep R t u) : RPO pr st t u := by
  induction h with
  | root hr =>
      cases hr with
      | inst hmem θ => exact RPO.bind θ (hR _ hmem)
  | arg f pre post _ ih => exact RPO.mono_arg f pre post ih

/-- Termination of applicative rewriting for a rule list oriented by the recursive path order
over a well-founded precedence (`RPO.wf`, Dershowitz 1987). -/
theorem AStep.wf_of_rpo {pr : ASym F → ASym F → Prop} {st : ASym F → ArgStatus} {ν : Type}
    {R : List (Term (ASym F) RV × Term (ASym F) RV)} (hwf : WellFounded pr)
    (hR : ∀ lr ∈ R, RPO pr st lr.1 lr.2) :
    WellFounded (fun u t : Term (ASym F) ν => AStep R t u) :=
  Subrelation.wf (fun {_ _} h => AStep.rpo hR h) (RPO.wf hwf)

/-- A partial left-flattening whose members all lie below `f(s⃗)` lies below `f(s⃗)`, by the
precedence clause with application minimal. -/
theorem leftFlat_rpo {pr : ASym F → ASym F → Prop} {st : ASym F → ArgStatus} {f : F}
    {args : List (Term (ASym F) RV)} (hap : pr .ap (.fn f)) {t : Term (ASym F) RV}
    {ts : List (Term (ASym F) RV)} (hflat : LeftFlat t ts) :
    (∀ v ∈ ts, RPO pr st (.app (.fn f) args) v) → RPO pr st (.app (.fn f) args) t := by
  induction hflat with
  | two t u => exact fun h => RPO.prec hap h
  | more u _ ih =>
      intro h
      refine RPO.prec hap ?_
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact ih (fun w hw => h w (List.mem_append_left _ hw))
      · exact h _ (List.mem_append_right _ (List.mem_singleton_self _))

/-- A term never lies above an application that has it as an argument, for a well-founded
transitive precedence. -/
theorem rpo_not_superterm {pr : ASym F → ASym F → Prop} {st : ASym F → ArgStatus}
    (hwf : WellFounded pr) (htr : ∀ a b c, pr a b → pr b c → pr a c)
    {s : Term (ASym F) RV} {g : ASym F} {args : List (Term (ASym F) RV)} (hmem : s ∈ args) :
    ¬ RPO pr st s (.app g args) := fun h =>
  RPO.irrefl hwf s (RPO.trans htr h (RPO.subEq hmem))

end Rewriting

/-! ## 3. The System T signature, its rules, and the free-schema adapter -/

/-- Sorts: the natural numbers and one further sort. -/
inductive TSort : Type where
  | nat | o
  deriving DecidableEq

/-- Simple types over the System T sorts. -/
abbrev TTy : Type := HTy TSort

/-- The type of natural numbers. -/
abbrev natTy : TTy := .sort .nat

/-- Symbols: the constructors `0 : nat`, `S : nat → nat`, the iterator `iter_A` (the typed
rendering of the free recursor) and Gödel's recursor `rec_A`, at every result type `A`. -/
inductive TSym : Type where
  | zero | succ | iter (A : TTy) | grec (A : TTy)
  deriving DecidableEq

/-- Typing of the symbols: `iter_A : A × (A → A) × nat ⇒ A` and
`rec_A : A × (nat → A → A) × nat ⇒ A` (J. ACM 2007, Example 2.2, Gödel's system T). -/
def tSig : TSig TSort TSym where
  dom := fun
    | .zero => []
    | .succ => [natTy]
    | .iter A => [A, .arrow A A, natTy]
    | .grec A => [A, .arrow natTy (.arrow A A), natTy]
  cod := fun
    | .zero => natTy
    | .succ => natTy
    | .iter A => A
    | .grec A => A

/-- Rule variables. -/
inductive TVar : Type where
  | b | s | n
  deriving DecidableEq

/-- Applicative terms over the System T symbols. -/
abbrev TTerm (ν : Type) : Type := Term (ASym TSym) ν

/-- Variable typing of the iterator rules: `b : A`, `s : A → A`, `n : nat`. -/
def iterCtx (A : TTy) : TVar → TTy
  | .b => A
  | .s => .arrow A A
  | .n => natTy

/-- Variable typing of the recursor rules: `b : A`, `s : nat → A → A`, `n : nat`. -/
def recCtx (A : TTy) : TVar → TTy
  | .b => A
  | .s => .arrow natTy (.arrow A A)
  | .n => natTy

/-- `0`. -/
abbrev tZero {ν : Type} : TTerm ν := .app (.fn .zero) []
/-- `S t`. -/
abbrev tSucc {ν : Type} (t : TTerm ν) : TTerm ν := .app (.fn .succ) [t]
/-- `@(t, u)`. -/
abbrev tApp {ν : Type} (t u : TTerm ν) : TTerm ν := .app .ap [t, u]
/-- `iter_A(b, s, n)`. -/
abbrev tIter {ν : Type} (A : TTy) (b s n : TTerm ν) : TTerm ν := .app (.fn (.iter A)) [b, s, n]
/-- `rec_A(b, s, n)`. -/
abbrev tRec {ν : Type} (A : TTy) (b s n : TTerm ν) : TTerm ν := .app (.fn (.grec A)) [b, s, n]

/-- Left side `iter(b, s, 0)`. -/
abbrev iterZeroL (A : TTy) : TTerm TVar := tIter A (.var .b) (.var .s) tZero
/-- Left side `iter(b, s, S n)` of the duplicating iterator rule. -/
abbrev iterSuccL (A : TTy) : TTerm TVar := tIter A (.var .b) (.var .s) (tSucc (.var .n))
/-- Right side `@(s, iter(b, s, n))`. -/
abbrev iterSuccR (A : TTy) : TTerm TVar :=
  tApp (.var .s) (tIter A (.var .b) (.var .s) (.var .n))
/-- Left side `rec(b, s, 0)`. -/
abbrev recZeroL (A : TTy) : TTerm TVar := tRec A (.var .b) (.var .s) tZero
/-- Left side `rec(b, s, S n)` of the System T recursor rule. -/
abbrev recSuccL (A : TTy) : TTerm TVar := tRec A (.var .b) (.var .s) (tSucc (.var .n))
/-- The recursive call `rec(b, s, n)`. -/
abbrev recCall (A : TTy) : TTerm TVar := tRec A (.var .b) (.var .s) (.var .n)
/-- Right side `@(@(s, n), rec(b, s, n))` of the System T recursor rule. -/
abbrev recSuccR (A : TTy) : TTerm TVar := tApp (tApp (.var .s) (.var .n)) (recCall A)

/-- The typed rendering of the free two-rule system: the iterator rules. -/
def iterRules (A : TTy) : List (TTerm TVar × TTerm TVar) :=
  [(iterZeroL A, .var .b), (iterSuccL A, iterSuccR A)]

/-- Gödel's recursor rules. -/
def recRules (A : TTy) : List (TTerm TVar × TTerm TVar) :=
  [(recZeroL A, .var .b), (recSuccL A, recSuccR A)]

/-- Both sides of every System T rule are typable with the same type: they are typed rewrite
rules (J. ACM 2007, Definition 2.23). -/
theorem recRules_typed (A : TTy) :
    HasTy tSig (recCtx A) (recSuccL A) A ∧ HasTy tSig (recCtx A) (recSuccR A) A ∧
      HasTy tSig (recCtx A) (recZeroL A) A ∧ HasTy tSig (recCtx A) (.var .b) A := by
  have hn : HasTy tSig (recCtx A) (.var .n : TTerm TVar) natTy := HasTy.var TVar.n
  have hS : HasTy tSig (recCtx A) (tSucc (.var .n) : TTerm TVar) natTy := by
    refine HasTy.fn TSym.succ _ rfl ?_
    intro p hp
    simp only [tSig, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.mem_nil_iff,
      or_false] at hp
    subst hp
    exact hn
  have h0 : HasTy tSig (recCtx A) (tZero : TTerm TVar) natTy :=
    HasTy.fn TSym.zero _ rfl (fun p hp => by simp at hp)
  have hb : HasTy tSig (recCtx A) (.var .b : TTerm TVar) A := HasTy.var TVar.b
  have hs : HasTy tSig (recCtx A) (.var .s : TTerm TVar) (.arrow natTy (.arrow A A)) :=
    HasTy.var TVar.s
  have hrec : ∀ c : TTerm TVar, HasTy tSig (recCtx A) c natTy →
      HasTy tSig (recCtx A) (tRec A (.var .b) (.var .s) c) A := by
    intro c hc
    refine HasTy.fn (TSym.grec A) _ rfl ?_
    intro p hp
    simp only [tSig, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.mem_nil_iff,
      or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hb
    · exact hs
    · exact hc
  exact ⟨hrec _ hS, HasTy.ap (HasTy.ap hs hn) (hrec _ hn), hrec _ h0, hb⟩

/-- Adapter from the free schema: `wrap(s, y)` is read as the application `@(s, y)` and the free
recursor as the iterator at result type `A`. -/
def toA {ν : Type} (A : TTy) : FreeTerm ν → TTerm ν
  | .var x => .var x
  | .zero => tZero
  | .succ t => tSucc (toA A t)
  | .wrap s t => tApp (toA A s) (toA A t)
  | .recur b s n => tIter A (toA A b) (toA A s) (toA A n)

/-- Instantiation of the rule variables by adapted free terms. -/
def freeInst {ν : Type} (A : TTy) (b s n : FreeTerm ν) : TVar → TTerm ν
  | .b => toA A b
  | .s => toA A s
  | .n => toA A n

theorem toA_root {ν : Type} (A : TTy) :
    ∀ {t u : FreeTerm ν}, RootStep t u → ARoot (iterRules A) (toA A t) (toA A u)
  | _, _, .recurZero b s => by
      have h := ARoot.inst (R := iterRules A) (l := iterZeroL A) (r := .var .b)
        (List.mem_cons_self) (freeInst A b s .zero)
      have e1 : tbind (freeInst A b s .zero) (iterZeroL A) = toA A (.recur b s .zero) := by
        simp [tbind_app, freeInst, toA]
      have e2 : tbind (freeInst A b s .zero) (Term.var TVar.b) = toA A b := by
        simp [tbind_var, freeInst]
      rw [e1, e2] at h
      exact h
  | _, _, .recurSucc b s n => by
      have h := ARoot.inst (R := iterRules A) (l := iterSuccL A) (r := iterSuccR A)
        (List.mem_cons_of_mem _ (List.mem_cons_self)) (freeInst A b s n)
      have e1 : tbind (freeInst A b s n) (iterSuccL A) = toA A (.recur b s (.succ n)) := by
        simp [tbind_app, freeInst, toA]
      have e2 : tbind (freeInst A b s n) (iterSuccR A) = toA A (.wrap s (.recur b s n)) := by
        simp [tbind_app, freeInst, toA]
      rw [e1, e2] at h
      exact h

theorem toA_plug {ν : Type} (A : TTy) {t u : FreeTerm ν}
    (h : AStep (iterRules A) (toA A t) (toA A u)) :
    ∀ C : FreeContext ν, AStep (iterRules A) (toA A (C.plug t)) (toA A (C.plug u))
  | .hole => h
  | .succ C => AStep.arg (.fn TSym.succ) [] [] (toA_plug A h C)
  | .wrapLeft C r => AStep.arg .ap [] [toA A r] (toA_plug A h C)
  | .wrapRight l C => AStep.arg .ap [toA A l] [] (toA_plug A h C)
  | .recurBase C s n => AStep.arg (.fn (TSym.iter A)) [] [toA A s, toA A n] (toA_plug A h C)
  | .recurStep b C n => AStep.arg (.fn (TSym.iter A)) [toA A b] [toA A n] (toA_plug A h C)
  | .recurCounter b s C => AStep.arg (.fn (TSym.iter A)) [toA A b, toA A s] [] (toA_plug A h C)

/-- Every contextual step of the free schema is an applicative step of the iterator rules. -/
theorem toA_contextStep {ν : Type} (A : TTy) {t u : FreeTerm ν} (h : ContextStep t u) :
    AStep (iterRules A) (toA A t) (toA A u) := by
  cases h with
  | lift C hr => exact toA_plug A (AStep.root (toA_root A hr)) C

/-- Termination of the iterator rules transfers to the free schema along the adapter. -/
theorem free_wf_of_iter {ν : Type} (A : TTy)
    (h : WellFounded (fun u t : TTerm ν => AStep (iterRules A) t u)) :
    WellFounded (fun u t : FreeTerm ν => ContextStep t u) :=
  Subrelation.wf (fun {_ _} hs => toA_contextStep A hs) (InvImage.wf (toA A) h)

/-- The termination statement of the typed fragment: applicative rewriting with the iterator
rules terminates at every result type and over every variable type, and so does the contextual
relation of the free schema. -/
def TypedFreeTermination : Prop :=
  (∀ (A : TTy) (ν : Type), WellFounded (fun u t : TTerm ν => AStep (iterRules A) t u)) ∧
    ∀ ν : Type, WellFounded (fun u t : FreeTerm ν => ContextStep t u)

/-- Rank of the System T symbols. -/
def tRank : TSym → Nat
  | .zero => 0
  | .succ => 1
  | .iter _ => 2
  | .grec _ => 2

theorem tRank_wf : WellFounded (fun a b : TSym => tRank a < tRank b) :=
  InvImage.wf tRank Nat.lt_wfRel.wf

theorem ne_arrow_of_size {A B : TTy} (h : B.size < A.size) : A ≠ B := by
  rintro rfl
  exact lt_irrefl _ h

theorem ty_ne_step (A : TTy) : A ≠ .arrow natTy (.arrow A A) :=
  fun h => by
    have := congrArg HTy.size h
    simp only [HTy.size] at this
    omega

theorem ty_ne_endo (A : TTy) : A ≠ .arrow A A :=
  fun h => by
    have := congrArg HTy.size h
    simp only [HTy.size] at this
    omega

/-! ## 4. Row `horpoAdmittance`: the higher-order recursive path ordering

Jouannaud and Rubio, *The higher-order recursive path ordering*, LICS 1999, Definition 3.1,
cases 1 to 5 (the ordering compares terms of equivalent types), and *Polymorphic higher-order
recursive path orderings*, J. ACM 54(1), 2007, Definition 3.1, cases 1 to 4 and 7 (the same
clauses under a type ordering; type equality is the type ordering used here). -/

/-- Status of a function symbol: multiset, or lexicographic from left to right (J. ACM 2007,
Section 3.1). -/
inductive HStat : Type where
  | mul | lex
  deriving DecidableEq

/-- The status as an argument status of the recursive path order. -/
def HStat.toArg : HStat → ArgStatus
  | .mul => .mul
  | .lex => .lex (fun n => Equiv.refl (Fin n))

/-- Status of the applicative symbols: application has multiset status. -/
def apStat {F : Type} (st : F → HStat) : ASym F → ArgStatus
  | .fn f => (st f).toArg
  | .ap => .mul

/-- Comparison modes of the HORPO clauses: strict `≻`, weak `⪰` (equality or `≻`), and the
condition `A` of a term `f(s⃗)` over a term `v` (`f(s⃗) ≻ v`, or `u ⪰ v` for some `u ∈ s⃗`). -/
inductive HMode : Type where
  | gt | ge | dom
  deriving DecidableEq

section Horpo

variable {S F V : Type}

/-- The HORPO clauses needed by the recursor rule. The type condition is equality of the
computed types. -/
inductive Horpo (sig : TSig S F) (Γ : V → HTy S) (pr : F → F → Prop) (st : F → HStat) :
    HMode → Term (ASym F) V → Term (ASym F) V → Prop
  /-- `⪰` contains equality. -/
  | refl (t : Term (ASym F) V) : Horpo sig Γ pr st .ge t t
  /-- `⪰` contains `≻`. -/
  | strict {s t : Term (ASym F) V} (h : Horpo sig Γ pr st .gt s t) : Horpo sig Γ pr st .ge s t
  /-- Condition `A`, first alternative: `f(s⃗) ≻ v`. -/
  | domSelf {f : F} {args : List (Term (ASym F) V)} {v : Term (ASym F) V}
      (h : Horpo sig Γ pr st .gt (.app (.fn f) args) v) :
      Horpo sig Γ pr st .dom (.app (.fn f) args) v
  /-- Condition `A`, second alternative: `u ⪰ v` for an argument `u ∈ s⃗` (no type check). -/
  | domArg {f : F} {args : List (Term (ASym F) V)} {u v : Term (ASym F) V} (hu : u ∈ args)
      (h : Horpo sig Γ pr st .ge u v) : Horpo sig Γ pr st .dom (.app (.fn f) args) v
  /-- Case 1: `f(s⃗) ≻ t` if `u ⪰ t` for some `u ∈ s⃗`. -/
  | sub {f : F} {args : List (Term (ASym F) V)} {t u : Term (ASym F) V}
      (hty : TyEq sig Γ (.app (.fn f) args) t) (hu : u ∈ args) (h : Horpo sig Γ pr st .ge u t) :
      Horpo sig Γ pr st .gt (.app (.fn f) args) t
  /-- Case 2: `f(s⃗) ≻ g(t⃗)` if `f >F g` and condition `A` holds for every `v ∈ t⃗`. -/
  | prec {f g : F} {args targs : List (Term (ASym F) V)}
      (hty : TyEq sig Γ (.app (.fn f) args) (.app (.fn g) targs)) (hfg : pr g f)
      (hA : ∀ v ∈ targs, Horpo sig Γ pr st .dom (.app (.fn f) args) v) :
      Horpo sig Γ pr st .gt (.app (.fn f) args) (.app (.fn g) targs)
  /-- Case 3: multiset status, `s⃗ (≻)mul t⃗` in the Dershowitz–Manna form. -/
  | mul {f : F} {args targs : List (Term (ASym F) V)}
      (hty : TyEq sig Γ (.app (.fn f) args) (.app (.fn f) targs)) (hst : st f = .mul)
      (X Y Z : Multiset (Term (ASym F) V)) (φ : Term (ASym F) V → Term (ASym F) V) (hZ : Z ≠ 0)
      (hs : (args : Multiset (Term (ASym F) V)) = X + Z)
      (ht : (targs : Multiset (Term (ASym F) V)) = X + Y)
      (hφZ : ∀ y ∈ Y, φ y ∈ Z) (hφ : ∀ y ∈ Y, Horpo sig Γ pr st .gt (φ y) y) :
      Horpo sig Γ pr st .gt (.app (.fn f) args) (.app (.fn f) targs)
  /-- Case 4: lexicographic status, `s⃗ (≻)lex t⃗` and condition `A`. -/
  | lex {f : F} {args targs : List (Term (ASym F) V)}
      (hty : TyEq sig Γ (.app (.fn f) args) (.app (.fn f) targs)) (hst : st f = .lex)
      (n : Nat) (hn : args.length = n) (hn' : targs.length = n) (k : Fin n)
      (hpre : ∀ i : Fin n, i < k →
        args[i.1]'(lt_of_lt_of_eq i.2 hn.symm) = targs[i.1]'(lt_of_lt_of_eq i.2 hn'.symm))
      (hcut : Horpo sig Γ pr st .gt (args[k.1]'(lt_of_lt_of_eq k.2 hn.symm))
        (targs[k.1]'(lt_of_lt_of_eq k.2 hn'.symm)))
      (hA : ∀ v ∈ targs, Horpo sig Γ pr st .dom (.app (.fn f) args) v) :
      Horpo sig Γ pr st .gt (.app (.fn f) args) (.app (.fn f) targs)
  /-- Case 5 of LICS 1999 (case 7 of J. ACM 2007): `f(s⃗) ≻ t` if `t = @(t₁, …, tₙ)` is a
  partial left-flattening of `t` and condition `A` holds for every `tᵢ`. -/
  | apRight {f : F} {args : List (Term (ASym F) V)} {t : Term (ASym F) V}
      {ts : List (Term (ASym F) V)} (hty : TyEq sig Γ (.app (.fn f) args) t)
      (hflat : LeftFlat t ts) (hA : ∀ v ∈ ts, Horpo sig Γ pr st .dom (.app (.fn f) args) v) :
      Horpo sig Γ pr st .gt (.app (.fn f) args) t

/-- The reading of a comparison mode in the recursive path order. -/
def HMode.inRPO (pr : ASym F → ASym F → Prop) (st : ASym F → ArgStatus) :
    HMode → Term (ASym F) V → Term (ASym F) V → Prop
  | .gt, s, t => RPO pr st s t
  | .ge, s, t => s = t ∨ RPO pr st s t
  | .dom, s, t => RPO pr st s t

/-- **Embedding.** Every HORPO clause of the fragment is an instance of the recursive path order
over the applicative symbols, with application below every function symbol and multiset status
for application; the type condition is forgotten. -/
theorem Horpo.toRPO {sig : TSig S F} {Γ : V → HTy S} {pr : F → F → Prop} {st : F → HStat}
    {m : HMode} {s t : Term (ASym F) V} (h : Horpo sig Γ pr st m s t) :
    HMode.inRPO (apPrec pr) (apStat st) m s t := by
  induction h with
  | refl t => exact Or.inl rfl
  | strict _ ih => exact Or.inr ih
  | domSelf _ ih => exact ih
  | domArg hu _ ih =>
      rcases ih with heq | hlt
      · subst heq
        exact RPO.subEq hu
      · exact RPO.subGt _ hu hlt
  | sub _ hu _ ih =>
      rcases ih with heq | hlt
      · subst heq
        exact RPO.subEq hu
      · exact RPO.subGt _ hu hlt
  | prec _ hfg _ ih => exact RPO.prec hfg ih
  | mul _ hst X Y Z φ hZ hs ht hφZ _ ih =>
      exact RPO.mul (by simp only [apStat, hst, HStat.toArg]) X Y Z φ hZ hs ht hφZ ih
  | lex _ hst n hn hn' k hpre _ _ ihcut ihA =>
      exact RPO.lex (fun n => Equiv.refl (Fin n)) (by simp only [apStat, hst, HStat.toArg])
        n hn hn' k (fun i hi => hpre i hi) ihcut ihA
  | apRight _ hflat _ ih => exact leftFlat_rpo trivial hflat ih

/-- Every strict comparison carries the type condition. -/
theorem Horpo.gt_tyEq {sig : TSig S F} {Γ : V → HTy S} {pr : F → F → Prop} {st : F → HStat}
    {s t : Term (ASym F) V} (h : Horpo sig Γ pr st .gt s t) : TyEq sig Γ s t := by
  cases h <;> assumption

/-- **Fragment soundness of HORPO.** A rule list whose rules decrease in the HORPO clauses over a
well-founded precedence terminates under applicative rewriting, through the embedding
`Horpo.toRPO` and the well-foundedness, stability and monotonicity of the recursive path
order. -/
theorem horpo_rules_wf {sig : TSig S F} {Γ : V → HTy S} {pr : F → F → Prop} {st : F → HStat}
    {ν : Type} {R : List (Term (ASym F) V × Term (ASym F) V)} (hwf : WellFounded pr)
    (hR : ∀ lr ∈ R, Horpo sig Γ pr st .gt lr.1 lr.2) :
    WellFounded (fun u t : Term (ASym F) ν => AStep R t u) :=
  AStep.wf_of_rpo (st := apStat st) (apPrec_wf hwf) (fun lr hlr => (hR lr hlr).toRPO)

end Horpo

/-- `S n ≻ n` (case 1), at every variable typing with `n : nat`. -/
theorem horpo_succ_var {Γ : TVar → TTy} (hΓ : Γ .n = natTy) (pr : TSym → TSym → Prop)
    (st : TSym → HStat) : Horpo tSig Γ pr st .gt (tSucc (.var .n)) (.var .n) :=
  Horpo.sub ⟨natTy, rfl, by rw [tyOf_var, hΓ]⟩ (List.mem_singleton_self _) (.refl _)

/-- The recursive call `g(b, s, n)` lies below `g(b, s, S n)` by the status clause, for either
status of `g`. -/
theorem horpo_status_call {Γ : TVar → TTy} (hΓ : Γ .n = natTy) (pr : TSym → TSym → Prop)
    (st : TSym → HStat) (g : TSym) :
    Horpo tSig Γ pr st .gt (.app (.fn g) [.var .b, .var .s, tSucc (.var .n)])
      (.app (.fn g) [.var .b, .var .s, .var .n]) := by
  have hty : TyEq tSig Γ (.app (.fn g) [.var .b, .var .s, tSucc (.var .n)] : TTerm TVar)
      (.app (.fn g) [.var .b, .var .s, .var .n]) := ⟨tSig.cod g, rfl, rfl⟩
  have hsn := horpo_succ_var hΓ pr st
  cases hst : st g with
  | mul =>
      refine Horpo.mul hty hst (([.var .b, .var .s] : List (TTerm TVar)) : Multiset (TTerm TVar))
        (([.var .n] : List (TTerm TVar)) : Multiset (TTerm TVar))
        (([tSucc (.var .n)] : List (TTerm TVar)) : Multiset (TTerm TVar))
        (fun _ => tSucc (.var .n)) (by simp)
        (Multiset.coe_add ([.var .b, .var .s] : List (TTerm TVar)) [tSucc (.var .n)]).symm
        (Multiset.coe_add ([.var .b, .var .s] : List (TTerm TVar)) [.var .n]).symm (fun _ _ => by simp) ?_
      intro y hy
      have hy' : y = .var .n := by simpa using hy
      subst hy'
      exact hsn
  | lex =>
      refine Horpo.lex hty hst 3 rfl rfl ⟨2, by decide⟩ ?_ hsn ?_
      · intro i hi
        fin_cases i
        · rfl
        · rfl
        · exact absurd hi (by decide)
      · intro v hv
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl | rfl
        · exact .domArg List.mem_cons_self (.refl _)
        · exact .domArg (List.mem_cons_of_mem _ List.mem_cons_self) (.refl _)
        · exact .domArg (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            (.strict hsn)

/-- The zero rules: the base is an argument (case 1). -/
theorem horpo_zero_rule {Γ : TVar → TTy} (g : TSym) (hg : tSig.cod g = Γ .b)
    (pr : TSym → TSym → Prop) (st : TSym → HStat) :
    Horpo tSig Γ pr st .gt (.app (.fn g) [.var .b, .var .s, tZero]) (.var .b) :=
  Horpo.sub ⟨Γ .b, by rw [tyOf_fn, hg], rfl⟩ List.mem_cons_self (.refl _)

/-- **Admission of the duplicating iterator rule** (the free duplicating rule through the
adapter): case 5 of LICS 1999 with the flattening `[s, iter(b, s, n)]`; the step argument
satisfies condition `A` as an argument, the recursive call through the status clause. -/
theorem horpo_iter_succ (A : TTy) (pr : TSym → TSym → Prop) (st : TSym → HStat) :
    Horpo tSig (iterCtx A) pr st .gt (iterSuccL A) (iterSuccR A) := by
  refine Horpo.apRight ⟨A, rfl, rfl⟩ (LeftFlat.two _ _) ?_
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl
  · exact .domArg (List.mem_cons_of_mem _ List.mem_cons_self) (.refl _)
  · exact .domSelf (horpo_status_call rfl pr st (.iter A))

/-- **Admission of Gödel's recursor rule** by the HORPO clauses (LICS 1999, Example 1; J. ACM
2007, Example 3.2): case 5 with the full left-flattening `[s, n, rec(b, s, n)]`. -/
theorem horpo_rec_succ (A : TTy) (pr : TSym → TSym → Prop) (st : TSym → HStat) :
    Horpo tSig (recCtx A) pr st .gt (recSuccL A) (recSuccR A) := by
  refine Horpo.apRight ⟨A, rfl, rfl⟩ (LeftFlat.more _ (LeftFlat.two _ _)) ?_
  intro v hv
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with (rfl | rfl) | rfl
  · exact .domArg (List.mem_cons_of_mem _ List.mem_cons_self) (.refl _)
  · exact .domArg (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (.strict (horpo_succ_var rfl pr st))
  · exact .domSelf (horpo_status_call rfl pr st (.grec A))

/-- Every precedence and status admits both rules of the typed free system. -/
theorem horpo_accepts_iter (pr : TSym → TSym → Prop) (st : TSym → HStat) (A : TTy) :
    Horpo tSig (iterCtx A) pr st .gt (iterZeroL A) (.var .b) ∧
      Horpo tSig (iterCtx A) pr st .gt (iterSuccL A) (iterSuccR A) :=
  ⟨horpo_zero_rule (.iter A) rfl pr st, horpo_iter_succ A pr st⟩

/-- The type condition is live: the step argument `s` lies below the left side in the
recursive path order (it is an argument), but its type `nat → A → A` differs from `A`. -/
theorem horpo_rejects_step_arg (A : TTy) (pr : TSym → TSym → Prop) (st : TSym → HStat) :
    ¬ Horpo tSig (recCtx A) pr st .gt (recSuccL A) (.var .s) := by
  intro h
  obtain ⟨σ, h1, h2⟩ := h.gt_tyEq
  have e1 : A = σ := Option.some.inj h1
  have e2 : HTy.arrow natTy (HTy.arrow A A) = σ := Option.some.inj h2
  exact ty_ne_step A (e1.trans e2.symm)

/-- The flattening is load-bearing: with the binary flattening `[@(s, n), rec(b, s, n)]`
condition `A` fails at `@(s, n)`, whose type `A → A` differs from `A` and which no argument of
the left side dominates. -/
theorem horpo_binary_flattening_blocked (A : TTy) (pr : TSym → TSym → Prop)
    (st : TSym → HStat) :
    ¬ Horpo tSig (recCtx A) pr st .dom (recSuccL A) (tApp (.var .s) (.var .n)) := by
  intro h
  cases h with
  | domSelf hgt =>
      obtain ⟨σ, h1, h2⟩ := hgt.gt_tyEq
      have e1 : A = σ := Option.some.inj h1
      have e2 : HTy.arrow A A = σ := Option.some.inj h2
      exact ty_ne_endo A (e1.trans e2.symm)
  | domArg hu hge =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · cases hge with
        | strict hgt => cases hgt
      · cases hge with
        | strict hgt => cases hgt
      · cases hge with
        | strict hgt =>
            obtain ⟨σ, h1, h2⟩ := hgt.gt_tyEq
            have e : natTy = HTy.arrow A A := (Option.some.inj h1).trans (Option.some.inj h2).symm
            cases e

/-- A recursive call on the unchanged counter is rejected under the laws: the left side would
lie above a term containing it. -/
theorem horpo_rejects_same_counter (A : TTy) {pr : TSym → TSym → Prop} (st : TSym → HStat)
    (hwf : WellFounded pr) (htr : ∀ a b c, pr a b → pr b c → pr a c) :
    ¬ Horpo tSig (recCtx A) pr st .gt (recSuccL A) (tApp (tApp (.var .s) (.var .n)) (recSuccL A)) :=
  fun h => rpo_not_superterm (apPrec_wf hwf) (apPrec_trans htr)
    (List.mem_cons_of_mem _ List.mem_cons_self) h.toRPO

/-- Native data of `horpoAdmittance`: a precedence on the System T symbols and a status for every
symbol. -/
structure horpoAdmittanceData : Type where
  prec : TSym → TSym → Prop
  stat : TSym → HStat

/-- Jouannaud and Rubio, LICS 1999, Section 3 (the precedence is a well-founded ordering on the
function symbols; Definition 3.1), and J. ACM 54(1) 2007, Section 3.1 (a quasi-ordering whose
strict part is well founded): the precedence is a transitive, well-founded strict order; every
status is admissible. -/
def horpoAdmittanceLaws (M : horpoAdmittanceData) : Prop :=
  WellFounded M.prec ∧ ∀ a b c, M.prec a b → M.prec b c → M.prec a c

/-- HORPO's own acceptance of the free two-rule system through the adapter `toA`: the typed
iterator rules decrease in the HORPO clauses at every result type `A`. -/
def horpoAdmittanceAccepts (M : horpoAdmittanceData) : Prop :=
  ∀ A : TTy, Horpo tSig (iterCtx A) M.prec M.stat .gt (iterZeroL A) (.var .b) ∧
    Horpo tSig (iterCtx A) M.prec M.stat .gt (iterSuccL A) (iterSuccR A)

/-- The clauses accept the typed free system, and the fragment soundness theorem yields
termination of the typed iterator rules and of the free schema.
Verdict: fragment escape. -/
def horpoAdmittanceResult (M : horpoAdmittanceData) : Prop :=
  horpoAdmittanceAccepts M ∧ TypedFreeTermination

/-- **Soundness** of the fragment: acceptance and a well-founded precedence give termination
through the embedding into the recursive path order. -/
theorem horpoAdmittance_sound : ∀ M : horpoAdmittanceData, horpoAdmittanceLaws M →
    horpoAdmittanceAccepts M → TypedFreeTermination := by
  intro M hL hA
  have hwf : ∀ (A : TTy) (ν : Type),
      WellFounded (fun u t : TTerm ν => AStep (iterRules A) t u) := by
    intro A ν
    refine horpo_rules_wf (sig := tSig) (Γ := iterCtx A) (st := M.stat) hL.1 ?_
    intro lr hlr
    simp only [iterRules, List.mem_cons, List.mem_nil_iff, or_false] at hlr
    rcases hlr with rfl | rfl
    · exact (hA A).1
    · exact (hA A).2
  exact ⟨hwf, fun ν => free_wf_of_iter (.sort .o) (hwf _ ν)⟩

/-- Witness: the rank precedence and multiset status. -/
def horpoAdmittanceWitness : horpoAdmittanceData where
  prec := fun a b => tRank a < tRank b
  stat := fun _ => .mul

theorem horpoAdmittanceWitness_laws : horpoAdmittanceLaws horpoAdmittanceWitness :=
  ⟨tRank_wf, fun _ _ _ h₁ h₂ => lt_trans h₁ h₂⟩

theorem horpoAdmittanceWitness_result : horpoAdmittanceResult horpoAdmittanceWitness :=
  ⟨fun A => horpo_accepts_iter _ _ A,
    horpoAdmittance_sound _ horpoAdmittanceWitness_laws (fun A => horpo_accepts_iter _ _ A)⟩

/-- **Defining features.** The native recursive example (Gödel's recursor) is admitted with
multiset and with lexicographic status; application on the right uses the full left-flattening,
and the binary flattening is blocked by the type condition; the type condition rejects a
comparison that the untyped recursive path order accepts; a recursive call on the unchanged
counter is rejected. -/
theorem horpoAdmittanceWitness_feature :
    (∀ A : TTy, Horpo tSig (recCtx A) horpoAdmittanceWitness.prec horpoAdmittanceWitness.stat
        .gt (recSuccL A) (recSuccR A)) ∧
      (∀ A : TTy, Horpo tSig (recCtx A) horpoAdmittanceWitness.prec (fun _ => .lex)
        .gt (recSuccL A) (recSuccR A)) ∧
      (∀ A : TTy, ¬ Horpo tSig (recCtx A) horpoAdmittanceWitness.prec horpoAdmittanceWitness.stat
        .dom (recSuccL A) (tApp (.var .s) (.var .n))) ∧
      (∀ A : TTy, ¬ Horpo tSig (recCtx A) horpoAdmittanceWitness.prec
          horpoAdmittanceWitness.stat .gt (recSuccL A) (.var .s) ∧
        RPO (apPrec horpoAdmittanceWitness.prec) (apStat horpoAdmittanceWitness.stat)
          (recSuccL A) (.var .s)) ∧
      (∀ A : TTy, ¬ Horpo tSig (recCtx A) horpoAdmittanceWitness.prec horpoAdmittanceWitness.stat
        .gt (recSuccL A) (tApp (tApp (.var .s) (.var .n)) (recSuccL A))) :=
  ⟨fun A => horpo_rec_succ A _ _, fun A => horpo_rec_succ A _ _,
    fun A => horpo_binary_flattening_blocked A _ _,
    fun A => ⟨horpo_rejects_step_arg A _ _, RPO.subEq (List.mem_cons_of_mem _ List.mem_cons_self)⟩,
    fun A => horpo_rejects_same_counter A _ tRank_wf (fun _ _ _ h₁ h₂ => lt_trans h₁ h₂)⟩

/-- **Mutation.** The total relation as precedence, everything else fixed, is not well
founded. -/
theorem horpoAdmittance_mutation :
    ¬ horpoAdmittanceLaws { horpoAdmittanceWitness with prec := fun _ _ => True } :=
  fun h => h.1.isIrrefl.irrefl TSym.zero trivial

/-- **Scope.** The fragment omits λ-abstraction and every clause with an application or an
abstraction on the left or an abstraction on the right (LICS 1999 Definition 3.1 cases 6 and 7;
J. ACM 2007 Definition 3.1 cases 5, 6 and 8 to 12, including β and η), polymorphism, type
orderings other than equality, and the computability-based proof that the full ordering is
well founded (LICS 1999 Theorem 3.2, J. ACM 2007 Theorem 3.5; ESTABLISHED). Formally: every
comparison of the fragment has a symbol-headed left side and lies inside the first-order recursive
path order with application minimal, which supplies well-foundedness here. -/
theorem horpoAdmittance_scope :
    ∀ (pr : TSym → TSym → Prop) (st : TSym → HStat) (Γ : TVar → TTy) (s t : TTerm TVar),
      Horpo tSig Γ pr st .gt s t →
        (∃ f args, s = .app (.fn f) args) ∧ RPO (apPrec pr) (apStat st) s t := by
  intro pr st Γ s t h
  refine ⟨?_, h.toRPO⟩
  cases h <;> exact ⟨_, _, rfl⟩

/-- **System T (row B1).** The HORPO clauses accept Gödel's recursor rules
`rec b s (S n) → s n (rec b s n)` and `rec b s 0 → b`, for every precedence and status. -/
theorem horpoAdmittance_admits_systemT : ∀ (M : horpoAdmittanceData) (A : TTy),
    Horpo tSig (recCtx A) M.prec M.stat .gt (recSuccL A) (recSuccR A) ∧
      Horpo tSig (recCtx A) M.prec M.stat .gt (recZeroL A) (.var .b) :=
  fun M A => ⟨horpo_rec_succ A M.prec M.stat, horpo_zero_rule (.grec A) rfl M.prec M.stat⟩

/-- System T recursor rewriting terminates by the fragment soundness theorem of HORPO. -/
theorem horpoAdmittance_systemT_terminates : ∀ M : horpoAdmittanceData,
    horpoAdmittanceLaws M →
      ∀ (A : TTy) (ν : Type), WellFounded (fun u t : TTerm ν => AStep (recRules A) t u) := by
  intro M hL A ν
  refine horpo_rules_wf (sig := tSig) (Γ := recCtx A) (st := M.stat) hL.1 ?_
  intro lr hlr
  simp only [recRules, List.mem_cons, List.mem_nil_iff, or_false] at hlr
  rcases hlr with rfl | rfl
  · exact (horpoAdmittance_admits_systemT M A).2
  · exact (horpoAdmittance_admits_systemT M A).1

/-! ## 5. Row `cpoAdmittance`: the computability path ordering

Blanqui, Jouannaud and Rubio, *The computability path ordering*, Logical Methods in Computer
Science 11(4:3), 2015: Definition 2.2 (admissible type orderings), Definition 5.1 with Figure 1
(core CPO: rules (Fb⊳), (Fb=), (Fb>), (Fb@), (@⊳)), Definitions 7.2 and 7.3 (positions and
accessible arguments), Definition 7.5 (accessibility `⊳a`), Definition 7.8 (structurally smaller)
and Definition 7.10 with Figure 2 (CPO with accessible subterms: the new rules (Fb⊳) and (Fb=)).
The set `X` of Figure 1 stays empty because the fragment has no abstraction. -/

/-- Membership from a successful list lookup. -/
theorem mem_of_getElem?_eq {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    a ∈ l := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 h
  exact heq ▸ List.getElem_mem hlt

/-- The ingredients of CPO: a precedence, a status, an ordering on types and the accessible
argument positions of every function symbol. -/
structure CpoIngr (S F : Type) : Type where
  prec : F → F → Prop
  stat : F → HStat
  tyGt : HTy S → HTy S → Prop
  acc : F → Nat → Prop

/-- The left-argument relation on types: `T → U ⊳l T`. -/
def TyLeft {S : Type} (T U : HTy S) : Prop := ∃ W, T = .arrow U W

/-- The relation `⋗ = (> ∪ ⊳l)⁺` of Definition 2.2, oriented from the bigger type. -/
def TyDom {S : Type} (gt : HTy S → HTy S → Prop) : HTy S → HTy S → Prop :=
  Relation.TransGen (fun T U => gt T U ∨ TyLeft T U)

/-- Admissible type ordering (LMCS 2015, Definition 2.2): a strict ordering containing the
right-argument relation (typ-right-subterm), with `⋗` well founded (typ-sn), and such that
`T → U > V` implies `U ≥ V` or `V = T → U'` with `U > U'` (typ-arrow). -/
def AdmissibleTyOrder {S : Type} (gt : HTy S → HTy S → Prop) : Prop :=
  (∀ T U V, gt T U → gt U V → gt T V) ∧ (∀ T U, gt (.arrow T U) U) ∧
    WellFounded (fun U T => TyDom gt T U) ∧
    ∀ T U V, gt (.arrow T U) V → (gt U V ∨ U = V) ∨ ∃ U', V = .arrow T U' ∧ gt U U'

/-- `a` occurs only positively (`true`) or only negatively (`false`) in a type (LMCS 2015,
Definition 7.2). -/
def OnlyPolar {S : Type} (a : S) : Bool → HTy S → Prop
  | true, .sort _ => True
  | false, .sort b => b ≠ a
  | p, .arrow T U => OnlyPolar a (!p) T ∧ OnlyPolar a p U

/-- The sorts occurring in a type. -/
def HTy.sorts {S : Type} : HTy S → List S
  | .sort a => [a]
  | .arrow T U => T.sorts ++ U.sorts

/-- Accessible arguments (LMCS 2015, Definition 7.3): if `i ∈ Acc(f)` then `f` has a sort `A` as
output type, every sort of the argument type `Tᵢ` is at most `A` in `⋗` (`Sort_A(Tᵢ)`), and `A`
occurs only positively in `Tᵢ`. -/
def AccArgsOK {S F : Type} (sig : TSig S F) (gt : HTy S → HTy S → Prop)
    (acc : F → Nat → Prop) : Prop :=
  ∀ f i, acc f i → ∃ a T, sig.cod f = .sort a ∧ (sig.dom f)[i]? = some T ∧
    (∀ b ∈ T.sorts, b = a ∨ TyDom gt (.sort a) (.sort b)) ∧ OnlyPolar a true T

/-- Comparison modes of the CPO clauses: `≻`, `≻τ` (`≻` with `τ(s) ≥ τ(t)`), `⪰τ`, `⪰`, and the
status relation `≻τ ∪ ⊳@⪰τ` of the rule (Fb=) of Figure 2. -/
inductive CMode : Type where
  | gt | gtT | geT | ge | st
  deriving DecidableEq

section Cpo

variable {S F V : Type}

/-- Accessibility through accessible arguments (LMCS 2015, Definition 7.5, `⊳a`): `u` is an
accessible argument `tᵢ` of `f(t⃗)` with `i ∈ Acc(f)`, or accessible in one. -/
inductive AccSub (acc : F → Nat → Prop) : Term (ASym F) V → Term (ASym F) V → Prop
  | arg {f : F} {args : List (Term (ASym F) V)} {i : Nat} {u : Term (ASym F) V}
      (hi : acc f i) (hu : args[i]? = some u) : AccSub acc (.app (.fn f) args) u
  | deep {f : F} {args : List (Term (ASym F) V)} {i : Nat} {w u : Term (ASym F) V}
      (hi : acc f i) (hw : args[i]? = some w) (h : AccSub acc w u) :
      AccSub acc (.app (.fn f) args) u

/-- An accessible subterm is a proper subterm: the recursive path order places it, and
everything it dominates weakly, below the term. -/
theorem AccSub.rpo {acc : F → Nat → Prop} {pr : ASym F → ASym F → Prop}
    {st : ASym F → ArgStatus} {s w t : Term (ASym F) V} (h : AccSub acc s w) :
    (w = t ∨ RPO pr st w t) → RPO pr st s t := by
  induction h with
  | arg _ hu =>
      intro hwt
      rcases hwt with rfl | hlt
      · exact RPO.subEq (mem_of_getElem?_eq hu)
      · exact RPO.subGt _ (mem_of_getElem?_eq hu) hlt
  | deep _ hw _ ih => exact fun hwt => RPO.subGt _ (mem_of_getElem?_eq hw) (ih hwt)

/-- The type condition `τ(s) ≥ τ(t)`, both types defined. -/
def TyGe (sig : TSig S F) (Γ : V → HTy S) (gt : HTy S → HTy S → Prop)
    (s t : Term (ASym F) V) : Prop :=
  ∃ σ τ, tyOf sig Γ s = some σ ∧ tyOf sig Γ t = some τ ∧ (σ = τ ∨ gt σ τ)

/-- The CPO clauses used by the recursor rule, with accessible subterms. -/
inductive Cpo (sig : TSig S F) (Γ : V → HTy S) (P : CpoIngr S F) :
    CMode → Term (ASym F) V → Term (ASym F) V → Prop
  /-- `t ≻τ u` if `t ≻ u` and `τ(t) ≥ τ(u)` (Definition 5.1). -/
  | typed {s t : Term (ASym F) V} (h : Cpo sig Γ P .gt s t) (hty : TyGe sig Γ P.tyGt s t) :
      Cpo sig Γ P .gtT s t
  | geTRefl (t : Term (ASym F) V) : Cpo sig Γ P .geT t t
  | geTGt {s t : Term (ASym F) V} (h : Cpo sig Γ P .gtT s t) : Cpo sig Γ P .geT s t
  | geRefl (t : Term (ASym F) V) : Cpo sig Γ P .ge t t
  | geGt {s t : Term (ASym F) V} (h : Cpo sig Γ P .gt s t) : Cpo sig Γ P .ge s t
  /-- The status relation contains `≻τ`. -/
  | stGt {s t : Term (ASym F) V} (h : Cpo sig Γ P .gtT s t) : Cpo sig Γ P .st s t
  /-- The status relation contains `⊳@⪰τ`: `s ⊳a w` with `s` and `w` of the same sort
  (Definition 7.8 with `X = ∅`), and `w ⪰τ t`. -/
  | stAcc {s w t : Term (ASym F) V} (hacc : AccSub P.acc s w)
      (hsame : ∃ a, tyOf sig Γ s = some (.sort a) ∧ tyOf sig Γ w = some (.sort a))
      (h : Cpo sig Γ P .geT w t) : Cpo sig Γ P .st s t
  /-- (Fb⊳) of Figure 2: `f(t⃗) ≻ v` if `t⃗ ⊵a ⪰τ v`. -/
  | fbSub {f : F} {args : List (Term (ASym F) V)} {u w v : Term (ASym F) V} (hu : u ∈ args)
      (hw : w = u ∨ AccSub P.acc u w) (h : Cpo sig Γ P .geT w v) :
      Cpo sig Γ P .gt (.app (.fn f) args) v
  /-- (Fb=) of Figure 2 with multiset status: `f(t⃗) ≻ u⃗` and `t⃗ (≻τ ∪ ⊳@⪰τ)mul u⃗`. -/
  | fbEqMul {f : F} {args targs : List (Term (ASym F) V)} (hst : P.stat f = .mul)
      (hdom : ∀ v ∈ targs, Cpo sig Γ P .gt (.app (.fn f) args) v)
      (X Y Z : Multiset (Term (ASym F) V)) (φ : Term (ASym F) V → Term (ASym F) V) (hZ : Z ≠ 0)
      (hs : (args : Multiset (Term (ASym F) V)) = X + Z)
      (ht : (targs : Multiset (Term (ASym F) V)) = X + Y)
      (hφZ : ∀ y ∈ Y, φ y ∈ Z) (hφ : ∀ y ∈ Y, Cpo sig Γ P .st (φ y) y) :
      Cpo sig Γ P .gt (.app (.fn f) args) (.app (.fn f) targs)
  /-- (Fb=) of Figure 2 with lexicographic status. -/
  | fbEqLex {f : F} {args targs : List (Term (ASym F) V)} (hst : P.stat f = .lex)
      (hdom : ∀ v ∈ targs, Cpo sig Γ P .gt (.app (.fn f) args) v)
      (n : Nat) (hn : args.length = n) (hn' : targs.length = n) (k : Fin n)
      (hpre : ∀ i : Fin n, i < k →
        args[i.1]'(lt_of_lt_of_eq i.2 hn.symm) = targs[i.1]'(lt_of_lt_of_eq i.2 hn'.symm))
      (hcut : Cpo sig Γ P .st (args[k.1]'(lt_of_lt_of_eq k.2 hn.symm))
        (targs[k.1]'(lt_of_lt_of_eq k.2 hn'.symm))) :
      Cpo sig Γ P .gt (.app (.fn f) args) (.app (.fn f) targs)
  /-- (Fb>): `f(t⃗) ≻ g(u⃗)` if `f >F g` and `f(t⃗) ≻ u⃗`. -/
  | fbPrec {f g : F} {args targs : List (Term (ASym F) V)} (hfg : P.prec g f)
      (hdom : ∀ v ∈ targs, Cpo sig Γ P .gt (.app (.fn f) args) v) :
      Cpo sig Γ P .gt (.app (.fn f) args) (.app (.fn g) targs)
  /-- (Fb@): `f(t⃗) ≻ u v` if `f(t⃗) ≻ u` and `f(t⃗) ≻ v`; no type check. -/
  | fbAp {f : F} {args : List (Term (ASym F) V)} {t u : Term (ASym F) V}
      (ht : Cpo sig Γ P .gt (.app (.fn f) args) t) (hu : Cpo sig Γ P .gt (.app (.fn f) args) u) :
      Cpo sig Γ P .gt (.app (.fn f) args) (.app .ap [t, u])
  /-- (@⊳), left argument: `t u ≻ v` if `t ⪰ v`. -/
  | apSubL {t u v : Term (ASym F) V} (h : Cpo sig Γ P .ge t v) :
      Cpo sig Γ P .gt (.app .ap [t, u]) v
  /-- (@⊳), right argument: `t u ≻ v` if `u ⪰τ v`. -/
  | apSubR {t u v : Term (ASym F) V} (h : Cpo sig Γ P .geT u v) :
      Cpo sig Γ P .gt (.app .ap [t, u]) v

/-- The reading of a CPO mode in the recursive path order. -/
def CMode.inRPO (pr : ASym F → ASym F → Prop) (st : ASym F → ArgStatus) :
    CMode → Term (ASym F) V → Term (ASym F) V → Prop
  | .gt, s, t => RPO pr st s t
  | .gtT, s, t => RPO pr st s t
  | .geT, s, t => s = t ∨ RPO pr st s t
  | .ge, s, t => s = t ∨ RPO pr st s t
  | .st, s, t => RPO pr st s t

/-- **Embedding.** Every CPO clause of the fragment is an instance of the recursive path order
with application minimal; accessible subterms are proper subterms, and the type checks are
forgotten. -/
theorem Cpo.toRPO {sig : TSig S F} {Γ : V → HTy S} {P : CpoIngr S F} {m : CMode}
    {s t : Term (ASym F) V} (h : Cpo sig Γ P m s t) :
    CMode.inRPO (apPrec P.prec) (apStat P.stat) m s t := by
  induction h with
  | typed _ _ ih => exact ih
  | geTRefl t => exact Or.inl rfl
  | geTGt _ ih => exact Or.inr ih
  | geRefl t => exact Or.inl rfl
  | geGt _ ih => exact Or.inr ih
  | stGt _ ih => exact ih
  | stAcc hacc _ _ ih => exact hacc.rpo ih
  | fbSub hu hw _ ih =>
      rcases hw with rfl | hacc
      · rcases ih with heq | hlt
        · subst heq
          exact RPO.subEq hu
        · exact RPO.subGt _ hu hlt
      · exact RPO.subGt _ hu (hacc.rpo ih)
  | fbEqMul hst _ X Y Z φ hZ hs ht hφZ _ _ ih =>
      exact RPO.mul (by simp only [apStat, hst, HStat.toArg]) X Y Z φ hZ hs ht hφZ ih
  | fbEqLex hst _ n hn hn' k hpre _ ihdom ihcut =>
      exact RPO.lex (fun n => Equiv.refl (Fin n)) (by simp only [apStat, hst, HStat.toArg])
        n hn hn' k (fun i hi => hpre i hi) ihcut ihdom
  | fbPrec hfg _ ih => exact RPO.prec hfg ih
  | fbAp _ _ iht ihu =>
      refine RPO.prec trivial ?_
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact iht
      · exact ihu
  | apSubL _ ih =>
      rcases ih with heq | hlt
      · subst heq
        exact RPO.subEq List.mem_cons_self
      · exact RPO.subGt _ List.mem_cons_self hlt
  | apSubR _ ih =>
      rcases ih with heq | hlt
      · subst heq
        exact RPO.subEq (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact RPO.subGt _ (List.mem_cons_of_mem _ List.mem_cons_self) hlt

/-- **Fragment soundness of CPO.** A rule list whose rules satisfy `l ≻τ r` over a well-founded
precedence terminates under applicative rewriting, through `Cpo.toRPO`. -/
theorem cpo_rules_wf {sig : TSig S F} {Γ : V → HTy S} {P : CpoIngr S F} {ν : Type}
    {R : List (Term (ASym F) V × Term (ASym F) V)} (hwf : WellFounded P.prec)
    (hR : ∀ lr ∈ R, Cpo sig Γ P .gtT lr.1 lr.2) :
    WellFounded (fun u t : Term (ASym F) ν => AStep R t u) :=
  AStep.wf_of_rpo (st := apStat P.stat) (apPrec_wf hwf) (fun lr hlr => (hR lr hlr).toRPO)

/-- An argument is below the application of a symbol (rule (Fb⊳), reflexive case). -/
theorem cpo_arg {sig : TSig S F} {Γ : V → HTy S} {P : CpoIngr S F} {f : F}
    {args : List (Term (ASym F) V)} {u : Term (ASym F) V} (hu : u ∈ args) :
    Cpo sig Γ P .gt (.app (.fn f) args) u :=
  Cpo.fbSub hu (Or.inl rfl) (.geTRefl u)

end Cpo

/-- The right spine: `U` is a proper right-argument descendant of `T`. -/
inductive RSpine {S : Type} : HTy S → HTy S → Prop
  | cod (T U : HTy S) : RSpine (.arrow T U) U
  | step (T : HTy S) {U V : HTy S} (h : RSpine U V) : RSpine (.arrow T U) V

theorem RSpine.size_lt {S : Type} {T U : HTy S} (h : RSpine T U) : U.size < T.size := by
  induction h with
  | cod T U => simp only [HTy.size]; omega
  | step T _ ih => simp only [HTy.size]; omega

theorem RSpine.trans {S : Type} {T U V : HTy S} (h₁ : RSpine T U) (h₂ : RSpine U V) :
    RSpine T V := by
  induction h₁ with
  | cod T U => exact .step T h₂
  | step T _ ih => exact .step T (ih h₂)

theorem tyDom_size_lt {S : Type} {T U : HTy S} (h : TyDom (RSpine (S := S)) T U) :
    U.size < T.size := by
  induction h with
  | single h =>
      rcases h with h | ⟨W, rfl⟩
      · exact h.size_lt
      · simp only [HTy.size]; omega
  | tail _ h ih =>
      rcases h with h | ⟨W, rfl⟩
      · exact lt_trans h.size_lt ih
      · simp only [HTy.size] at ih ⊢; omega

/-- The right spine is an admissible type ordering. -/
theorem rspine_admissible {S : Type} : AdmissibleTyOrder (RSpine (S := S)) := by
  refine ⟨fun T U V h₁ h₂ => h₁.trans h₂, fun T U => .cod T U, ?_, ?_⟩
  · exact Subrelation.wf (fun {_ _} h => tyDom_size_lt h) (InvImage.wf HTy.size Nat.lt_wfRel.wf)
  · intro T U V h
    cases h with
    | cod => exact Or.inl (Or.inr rfl)
    | step _ h => exact Or.inl (Or.inl h)

/-- `S n ≻τ n`, at every variable typing with `n : nat`. -/
theorem cpo_succ_var {Γ : TVar → TTy} (hΓ : Γ .n = natTy) (P : CpoIngr TSort TSym) :
    Cpo tSig Γ P .gtT (tSucc (.var .n)) (.var .n) :=
  Cpo.typed (cpo_arg (List.mem_singleton_self _))
    ⟨natTy, natTy, rfl, by rw [tyOf_var, hΓ], Or.inl rfl⟩

/-- The counter `n` lies below `g(b, s, S n)` by (Fb⊳) through `S n ≻τ n`. -/
theorem cpo_counter {Γ : TVar → TTy} (hΓ : Γ .n = natTy) (P : CpoIngr TSort TSym) (g : TSym) :
    Cpo tSig Γ P .gt (.app (.fn g) [.var .b, .var .s, tSucc (.var .n)]) (.var .n) :=
  Cpo.fbSub (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (Or.inl rfl)
    (.geTGt (cpo_succ_var hΓ P))

/-- The recursive call lies below the left side by (Fb=), for either status. -/
theorem cpo_status_call {Γ : TVar → TTy} (hΓ : Γ .n = natTy) (P : CpoIngr TSort TSym)
    (g : TSym) :
    Cpo tSig Γ P .gt (.app (.fn g) [.var .b, .var .s, tSucc (.var .n)])
      (.app (.fn g) [.var .b, .var .s, .var .n]) := by
  have hdom : ∀ v ∈ ([.var .b, .var .s, .var .n] : List (TTerm TVar)),
      Cpo tSig Γ P .gt (.app (.fn g) [.var .b, .var .s, tSucc (.var .n)]) v := by
    intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact cpo_arg List.mem_cons_self
    · exact cpo_arg (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact cpo_counter hΓ P g
  cases hst : P.stat g with
  | mul =>
      refine Cpo.fbEqMul hst hdom
        (([.var .b, .var .s] : List (TTerm TVar)) : Multiset (TTerm TVar))
        (([.var .n] : List (TTerm TVar)) : Multiset (TTerm TVar))
        (([tSucc (.var .n)] : List (TTerm TVar)) : Multiset (TTerm TVar))
        (fun _ => tSucc (.var .n)) (by simp)
        (Multiset.coe_add ([.var .b, .var .s] : List (TTerm TVar)) [tSucc (.var .n)]).symm
        (Multiset.coe_add ([.var .b, .var .s] : List (TTerm TVar)) [.var .n]).symm
        (fun _ _ => by simp) ?_
      intro y hy
      have hy' : y = .var .n := by simpa using hy
      subst hy'
      exact .stGt (cpo_succ_var hΓ P)
  | lex =>
      refine Cpo.fbEqLex hst hdom 3 rfl rfl ⟨2, by decide⟩ ?_ (.stGt (cpo_succ_var hΓ P))
      intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact absurd hi (by decide)

/-- **Admission of the duplicating iterator rule** by the CPO clauses: (Fb@) with the step
argument by (Fb⊳) and the recursive call by (Fb=); the rule satisfies `l ≻τ r`. -/
theorem cpo_iter_succ (A : TTy) (P : CpoIngr TSort TSym) :
    Cpo tSig (iterCtx A) P .gtT (iterSuccL A) (iterSuccR A) :=
  Cpo.typed (Cpo.fbAp (cpo_arg (List.mem_cons_of_mem _ List.mem_cons_self))
    (cpo_status_call rfl P (.iter A))) ⟨A, A, rfl, rfl, Or.inl rfl⟩

/-- **Admission of Gödel's recursor rule** by the CPO clauses: (Fb@) twice, with no partial
flattening; the inner application `@(s, n)` has type `A → A` and is compared without type
check. -/
theorem cpo_rec_succ (A : TTy) (P : CpoIngr TSort TSym) :
    Cpo tSig (recCtx A) P .gtT (recSuccL A) (recSuccR A) :=
  Cpo.typed (Cpo.fbAp (Cpo.fbAp (cpo_arg (List.mem_cons_of_mem _ List.mem_cons_self))
    (cpo_counter rfl P (.grec A))) (cpo_status_call rfl P (.grec A)))
    ⟨A, A, rfl, rfl, Or.inl rfl⟩

/-- The zero rules: the base is an argument. -/
theorem cpo_zero_rule {Γ : TVar → TTy} (g : TSym) (hg : tSig.cod g = Γ .b)
    (P : CpoIngr TSort TSym) :
    Cpo tSig Γ P .gtT (.app (.fn g) [.var .b, .var .s, tZero]) (.var .b) :=
  Cpo.typed (cpo_arg List.mem_cons_self) ⟨Γ .b, Γ .b, by rw [tyOf_fn, hg], rfl, Or.inl rfl⟩

/-- Immediate subterm. -/
def ImmSub {F V : Type} (u t : Term (ASym F) V) : Prop :=
  ∃ (g : ASym F) (args : List (Term (ASym F) V)), t = .app g args ∧ u ∈ args

/-- The subterm-only closure: `u` is a proper subterm of `t`, the relation generated by the
subterm case alone. -/
def SubtermOnly {F V : Type} (t u : Term (ASym F) V) : Prop := Relation.TransGen ImmSub u t

theorem SubtermOnly.size_lt {F V : Type} {t u : Term (ASym F) V} (h : SubtermOnly t u) :
    u.size < t.size := by
  induction h with
  | single h =>
      obtain ⟨g, args, rfl, hu⟩ := h
      exact Term.size_lt_of_mem hu
  | tail _ h ih =>
      obtain ⟨g, args, rfl, hu⟩ := h
      exact lt_trans ih (Term.size_lt_of_mem hu)

/-- Native data of `cpoAdmittance`: precedence, status, type ordering and accessible arguments
on the System T signature. -/
abbrev cpoAdmittanceData : Type := CpoIngr TSort TSym

/-- Blanqui, Jouannaud and Rubio, LMCS 11(4:3) 2015, Section 5.1 (a precedence whose strict part
is well founded; a status for every symbol), Definition 2.2 (admissible type ordering) and
Definition 7.3 (accessible arguments). -/
def cpoAdmittanceLaws (M : cpoAdmittanceData) : Prop :=
  (WellFounded M.prec ∧ ∀ a b c, M.prec a b → M.prec b c → M.prec a c) ∧
    AdmissibleTyOrder M.tyGt ∧ AccArgsOK tSig M.tyGt M.acc

/-- CPO's own acceptance of the free two-rule system through the adapter `toA`: both typed
iterator rules satisfy `l ≻τ r` at every result type. -/
def cpoAdmittanceAccepts (M : cpoAdmittanceData) : Prop :=
  ∀ A : TTy, Cpo tSig (iterCtx A) M .gtT (iterZeroL A) (.var .b) ∧
    Cpo tSig (iterCtx A) M .gtT (iterSuccL A) (iterSuccR A)

/-- The clauses accept the typed free system, and the fragment soundness theorem yields
termination of the typed iterator rules and of the free schema.
Verdict: fragment escape. -/
def cpoAdmittanceResult (M : cpoAdmittanceData) : Prop :=
  cpoAdmittanceAccepts M ∧ TypedFreeTermination

/-- **Soundness** of the fragment: acceptance and a well-founded precedence give termination
through the embedding of CPO into the recursive path order. The type-ordering and accessibility
laws are consumed by the computability proof of the source (Theorem 7.26), which the fragment
replaces by the embedding. -/
theorem cpoAdmittance_sound : ∀ M : cpoAdmittanceData, cpoAdmittanceLaws M →
    cpoAdmittanceAccepts M → TypedFreeTermination := by
  intro M hL hA
  have hwf : ∀ (A : TTy) (ν : Type),
      WellFounded (fun u t : TTerm ν => AStep (iterRules A) t u) := by
    intro A ν
    refine cpo_rules_wf (sig := tSig) (Γ := iterCtx A) (P := M) hL.1.1 ?_
    intro lr hlr
    simp only [iterRules, List.mem_cons, List.mem_nil_iff, or_false] at hlr
    rcases hlr with rfl | rfl
    · exact (hA A).1
    · exact (hA A).2
  exact ⟨hwf, fun ν => free_wf_of_iter (.sort .o) (hwf _ ν)⟩

/-- Witness: rank precedence, multiset status, the right-spine type ordering, and the argument
of the successor as the only accessible argument. -/
def cpoAdmittanceWitness : cpoAdmittanceData where
  prec := fun a b => tRank a < tRank b
  stat := fun _ => .mul
  tyGt := RSpine
  acc := fun f i => f = .succ ∧ i = 0

theorem cpoAdmittanceWitness_laws : cpoAdmittanceLaws cpoAdmittanceWitness := by
  refine ⟨⟨tRank_wf, fun _ _ _ h₁ h₂ => lt_trans h₁ h₂⟩, rspine_admissible, ?_⟩
  rintro f i ⟨rfl, rfl⟩
  refine ⟨.nat, natTy, rfl, rfl, ?_, trivial⟩
  intro b hb
  simp only [HTy.sorts, List.mem_singleton] at hb
  exact Or.inl hb

theorem cpoAdmittanceWitness_accepts : cpoAdmittanceAccepts cpoAdmittanceWitness :=
  fun A => ⟨cpo_zero_rule (.iter A) rfl _, cpo_iter_succ A _⟩

theorem cpoAdmittanceWitness_result : cpoAdmittanceResult cpoAdmittanceWitness :=
  ⟨cpoAdmittanceWitness_accepts,
    cpoAdmittance_sound _ cpoAdmittanceWitness_laws cpoAdmittanceWitness_accepts⟩

/-- **Defining features.** CPO orients Gödel's recursor rule, which the subterm-only closure does
not orient; (Fb@) compares the application `@(s, n)` of type `A → A` without type check, where
HORPO's condition `A` fails (`horpo_binary_flattening_blocked`); the counter is reached through
the accessible argument of `S` (Definition 7.5), and the status relation uses the structurally
smaller counter (Definition 7.8); the checked relation `≻τ` rejects the step argument, whose type
`nat → A → A` is not below `A` in the type ordering, while `≻` accepts it; a recursive call on the
unchanged counter is rejected. -/
theorem cpoAdmittanceWitness_feature :
    (∀ A : TTy, Cpo tSig (recCtx A) cpoAdmittanceWitness .gtT (recSuccL A) (recSuccR A) ∧
        ¬ SubtermOnly (recSuccL A) (recSuccR A)) ∧
      (∀ A : TTy, Cpo tSig (recCtx A) cpoAdmittanceWitness .gt (recSuccL A)
        (tApp (.var .s) (.var .n))) ∧
      (∀ A : TTy, Cpo tSig (recCtx A) cpoAdmittanceWitness .gt (recSuccL A) (.var .n) ∧
        Cpo tSig (recCtx A) cpoAdmittanceWitness .st (tSucc (.var .n)) (.var .n)) ∧
      (∀ A : TTy, Cpo tSig (recCtx A) cpoAdmittanceWitness .gt (recSuccL A) (.var .s) ∧
        ¬ Cpo tSig (recCtx A) cpoAdmittanceWitness .gtT (recSuccL A) (.var .s)) ∧
      (∀ A : TTy, ¬ Cpo tSig (recCtx A) cpoAdmittanceWitness .gtT (recSuccL A)
        (tApp (tApp (.var .s) (.var .n)) (recSuccL A))) := by
  refine ⟨fun A => ⟨cpo_rec_succ A _, ?_⟩, fun A => ?_, fun A => ⟨?_, ?_⟩,
    fun A => ⟨cpo_arg (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩, fun A => ?_⟩
  · intro h
    have := h.size_lt
    simp only [Term.size_app, Term.size_var, Term.sizeList_cons, Term.sizeList_nil] at this
    omega
  · exact Cpo.fbAp (cpo_arg (List.mem_cons_of_mem _ List.mem_cons_self))
      (cpo_counter rfl _ (.grec A))
  · exact Cpo.fbSub (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (Or.inr (AccSub.arg ⟨rfl, rfl⟩ rfl)) (.geTRefl _)
  · exact Cpo.stAcc (AccSub.arg ⟨rfl, rfl⟩ rfl) ⟨.nat, rfl, rfl⟩ (.geTRefl _)
  · intro h
    cases h with
    | typed _ hty =>
        obtain ⟨σ, τ, h1, h2, h3⟩ := hty
        have e1 : A = σ := Option.some.inj h1
        have e2 : HTy.arrow natTy (HTy.arrow A A) = τ := Option.some.inj h2
        subst e1
        subst e2
        rcases h3 with h3 | h3
        · exact ty_ne_step A h3
        · have := RSpine.size_lt h3
          simp only [HTy.size] at this
          omega
  · intro h
    exact rpo_not_superterm (apPrec_wf tRank_wf) (apPrec_trans (fun _ _ _ h₁ h₂ => lt_trans h₁ h₂))
      (List.mem_cons_of_mem _ List.mem_cons_self) h.toRPO

/-- **Mutation.** The empty relation as type ordering, everything else fixed, violates
(typ-right-subterm) of Definition 2.2. -/
theorem cpoAdmittance_mutation :
    ¬ cpoAdmittanceLaws { cpoAdmittanceWitness with tyGt := fun _ _ => False } :=
  fun h => h.2.1.2.1 natTy natTy

/-- **Scope.** The fragment omits λ-abstraction and the rules that involve it or a variable of
`X` ((Fbλ), (FbX), (@λ), (@X), (@β), (λ⊳), (λ=), (λ≠), (λX), (λη) of Figure 1), the rule (@=),
subterms of basic sort (`⊳bs` of Definition 7.5) beyond the reflexive case, structurally smaller
terms applied to variables of `X` (Definition 7.8 with `X ≠ ∅`), small symbols (Section 8), and
the computability proofs of well-foundedness (Theorems 6.27 and 7.26; ESTABLISHED). Formally:
every comparison of the fragment has a symbol-headed or application-headed left side and lies
inside the first-order recursive path order with application minimal. -/
theorem cpoAdmittance_scope :
    ∀ (P : CpoIngr TSort TSym) (Γ : TVar → TTy) (s t : TTerm TVar),
      Cpo tSig Γ P .gt s t →
        ((∃ f args, s = .app (.fn f) args) ∨ ∃ t₁ t₂, s = .app .ap [t₁, t₂]) ∧
          RPO (apPrec P.prec) (apStat P.stat) s t := by
  intro P Γ s t h
  refine ⟨?_, h.toRPO⟩
  cases h with
  | fbSub => exact Or.inl ⟨_, _, rfl⟩
  | fbEqMul => exact Or.inl ⟨_, _, rfl⟩
  | fbEqLex => exact Or.inl ⟨_, _, rfl⟩
  | fbPrec => exact Or.inl ⟨_, _, rfl⟩
  | fbAp => exact Or.inl ⟨_, _, rfl⟩
  | apSubL => exact Or.inr ⟨_, _, rfl⟩
  | apSubR => exact Or.inr ⟨_, _, rfl⟩

/-- **System T (row B1).** The CPO clauses accept Gödel's recursor rules `rec b s (S n) → s n
(rec b s n)` and `rec b s 0 → b` for all ingredients, both with `l ≻τ r`. -/
theorem cpoAdmittance_admits_systemT : ∀ (M : cpoAdmittanceData) (A : TTy),
    Cpo tSig (recCtx A) M .gtT (recSuccL A) (recSuccR A) ∧
      Cpo tSig (recCtx A) M .gtT (recZeroL A) (.var .b) :=
  fun M A => ⟨cpo_rec_succ A M, cpo_zero_rule (.grec A) rfl M⟩

/-- System T recursor rewriting terminates by the fragment soundness theorem of CPO. -/
theorem cpoAdmittance_systemT_terminates : ∀ M : cpoAdmittanceData, cpoAdmittanceLaws M →
    ∀ (A : TTy) (ν : Type), WellFounded (fun u t : TTerm ν => AStep (recRules A) t u) := by
  intro M hL A ν
  refine cpo_rules_wf (sig := tSig) (Γ := recCtx A) (P := M) hL.1.1 ?_
  intro lr hlr
  simp only [recRules, List.mem_cons, List.mem_nil_iff, or_false] at hlr
  rcases hlr with rfl | rfl
  · exact (cpoAdmittance_admits_systemT M A).2
  · exact (cpoAdmittance_admits_systemT M A).1

/-! ## 6. Row `generalSchemaAdmittance`: the general schema

Blanqui, Jouannaud and Okada, *Inductive-data-type systems*, Theoretical Computer Science
272(1–2), 2002, 41–68 (arXiv cs/0610066): Definitions 2 and 3 (constructors, basic inductive
types), Definition 4 (precedence), Definition 7 (status), Definition 9 (accessible subterms),
Definition 10 (ordering on arguments), Definition 11 (computable closure), Definition 12 (General
Schema) and Theorem 20 (strong normalization). -/

/-- Inductive-type declarations: the constructors and the basic inductive sorts (IDTS 2002,
Definitions 2 and 3). -/
structure InductiveDecl (S F : Type) : Type where
  isCon : F → Prop
  basic : S → Prop

/-- The constructors `0` and `S` of `nat`; both sorts are basic. -/
def tInd : InductiveDecl TSort TSym where
  isCon := fun f => f = .zero ∨ f = .succ
  basic := fun _ => True

/-- DM is monotone in the base relation. -/
theorem dm_mono {α : Type} {R R' : α → α → Prop} (h : ∀ a b, R a b → R' a b)
    {M N : Multiset α} (hd : DM R M N) : DM R' M N := by
  obtain ⟨X, Y, Z, hZ, hM, hN, hY⟩ := hd
  exact ⟨X, Y, Z, hZ, hM, hN, fun y hy => (hY y hy).imp fun z hz => ⟨hz.1, h _ _ hz.2⟩⟩

section GeneralSchema

variable {S F V : Type}

/-- Accessible subterms (IDTS 2002, Definition 9, cases 1, 3 and 5): `GAcc v u` means
`u ∈ Acc(v)`. -/
inductive GAcc (D : InductiveDecl S F) (sig : TSig S F) (Γ : V → HTy S) :
    Term (ASym F) V → Term (ASym F) V → Prop
  /-- Case 1: `v ∈ Acc(v)`. -/
  | self (v : Term (ASym F) V) : GAcc D sig Γ v v
  /-- Case 3: if `C(u⃗) ∈ Acc(v)` for a constructor `C`, then every `uᵢ ∈ Acc(v)`. -/
  | con {v : Term (ASym F) V} {c : F} {args : List (Term (ASym F) V)} {u : Term (ASym F) V}
      (hc : D.isCon c) (h : GAcc D sig Γ v (.app (.fn c) args)) (hu : u ∈ args) :
      GAcc D sig Γ v u
  /-- Case 5: a subterm of `v` of basic type. -/
  | basicSub {v u : Term (ASym F) V} (hsub : Relation.ReflTransGen ImmSub u v)
      (hb : ∃ a, tyOf sig Γ u = some (.sort a) ∧ D.basic a) : GAcc D sig Γ v u

/-- Accessible subterms are subterms. -/
theorem GAcc.sub {D : InductiveDecl S F} {sig : TSig S F} {Γ : V → HTy S}
    {v u : Term (ASym F) V} (h : GAcc D sig Γ v u) : Relation.ReflTransGen ImmSub u v := by
  induction h with
  | self => exact .refl
  | con _ _ hu ih => exact Relation.ReflTransGen.head ⟨_, _, rfl, hu⟩ ih
  | basicSub hsub _ => exact hsub

/-- A weak subterm is equal to the term or below it in the recursive path order. -/
theorem rtSub_rpo {pr : ASym F → ASym F → Prop} {st : ASym F → ArgStatus}
    {u t : Term (ASym F) V} (h : Relation.ReflTransGen ImmSub u t) :
    t = u ∨ RPO pr st t u := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
      obtain ⟨g, args, rfl, hmem⟩ := hstep
      rcases ih with heq | hlt
      · subst heq
        exact Or.inr (RPO.subEq hmem)
      · exact Or.inr (RPO.subGt _ hmem hlt)

/-- A weak subterm of an argument lies below the application. -/
theorem rpo_of_mem_rtSub {pr : ASym F → ASym F → Prop} {st : ASym F → ArgStatus}
    {g : ASym F} {l : List (Term (ASym F) V)} {li u : Term (ASym F) V} (hli : li ∈ l)
    (h : Relation.ReflTransGen ImmSub u li) : RPO pr st (.app g l) u := by
  rcases rtSub_rpo (pr := pr) (st := st) h with heq | hlt
  · subst heq
    exact RPO.subEq hli
  · exact RPO.subGt _ hli hlt

theorem rtSub_size_le {u t : Term (ASym F) V} (h : Relation.ReflTransGen ImmSub u t) :
    u.size ≤ t.size := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      obtain ⟨g, args, rfl, hmem⟩ := hstep
      exact le_of_lt (lt_of_le_of_lt ih (Term.size_lt_of_mem hmem))

/-- The ordering on arguments (IDTS 2002, Definition 10, strictly positive case with an empty
argument vector): `v = u|p` for a position `p ≠ ε` with every position strictly above `p`
constructor-headed. -/
inductive ArgGt (D : InductiveDecl S F) : Term (ASym F) V → Term (ASym F) V → Prop
  | arg {c : F} {args : List (Term (ASym F) V)} {v : Term (ASym F) V} (hc : D.isCon c)
      (hv : v ∈ args) : ArgGt D (.app (.fn c) args) v
  | deep {c : F} {args : List (Term (ASym F) V)} {w v : Term (ASym F) V} (hc : D.isCon c)
      (hw : w ∈ args) (h : ArgGt D w v) : ArgGt D (.app (.fn c) args) v

/-- Definition 10 compares two terms of the same inductive type. -/
def ArgGtT (D : InductiveDecl S F) (sig : TSig S F) (Γ : V → HTy S)
    (u v : Term (ASym F) V) : Prop :=
  ArgGt D u v ∧ ∃ a, tyOf sig Γ u = some (.sort a) ∧ tyOf sig Γ v = some (.sort a)

theorem ArgGt.rpo {D : InductiveDecl S F} {pr : ASym F → ASym F → Prop}
    {st : ASym F → ArgStatus} {u v : Term (ASym F) V} (h : ArgGt D u v) : RPO pr st u v := by
  induction h with
  | arg _ hv => exact RPO.subEq hv
  | deep _ hw _ ih => exact RPO.subGt _ hw ih

/-- The status extension of the ordering on arguments (Definition 7, with a pure multiset or a
pure lexicographic status). -/
def StatGt (D : InductiveDecl S F) (sig : TSig S F) (Γ : V → HTy S) (st : HStat)
    (l us : List (Term (ASym F) V)) : Prop :=
  match st with
  | .mul => DM (ArgGtT D sig Γ) (l : Multiset (Term (ASym F) V)) (us : Multiset (Term (ASym F) V))
  | .lex => ∃ (n : Nat) (hn : l.length = n) (hn' : us.length = n) (k : Fin n),
      (∀ i : Fin n, i < k →
        l[i.1]'(lt_of_lt_of_eq i.2 hn.symm) = us[i.1]'(lt_of_lt_of_eq i.2 hn'.symm)) ∧
      ArgGtT D sig Γ (l[k.1]'(lt_of_lt_of_eq k.2 hn.symm)) (us[k.1]'(lt_of_lt_of_eq k.2 hn'.symm))

/-- The computable closure `CC_f(l)` (IDTS 2002, Definition 11, cases 1, 2, 3, 5 and 6). -/
inductive GSClosure (D : InductiveDecl S F) (sig : TSig S F) (Γ : V → HTy S)
    (pr : F → F → Prop) (st : F → HStat) (f : F) (l : List (Term (ASym F) V)) :
    Term (ASym F) V → Prop
  /-- Case 1: variables. -/
  | var (x : V) : GSClosure D sig Γ pr st f l (.var x)
  /-- Case 2: accessible subterms of the arguments of the left-hand side. -/
  | acc {u : Term (ASym F) V} (hu : ∃ li ∈ l, GAcc D sig Γ li u) : GSClosure D sig Γ pr st f l u
  /-- Case 3: application of closure terms of types `t₁ → t₂` and `t₁`. -/
  | ap {u v : Term (ASym F) V} {A B : HTy S} (hu : GSClosure D sig Γ pr st f l u)
      (hv : GSClosure D sig Γ pr st f l v) (htu : tyOf sig Γ u = some (.arrow A B))
      (htv : tyOf sig Γ v = some A) : GSClosure D sig Γ pr st f l (.app .ap [u, v])
  /-- Case 5: a symbol `g <F f` applied to closure terms of the argument types of `g`. -/
  | lower {g : F} {us : List (Term (ASym F) V)} (hg : pr g f)
      (hus : ∀ u ∈ us, GSClosure D sig Γ pr st f l u)
      (hty : us.map (tyOf sig Γ) = (sig.dom g).map some) :
      GSClosure D sig Γ pr st f l (.app (.fn g) us)
  /-- Case 6: a recursive call on closure terms that are smaller in the status extension of
  the ordering on arguments. -/
  | recCall {us : List (Term (ASym F) V)} (hus : ∀ u ∈ us, GSClosure D sig Γ pr st f l u)
      (hty : us.map (tyOf sig Γ) = (sig.dom f).map some) (hdec : StatGt D sig Γ (st f) l us) :
      GSClosure D sig Γ pr st f l (.app (.fn f) us)

/-- The General Schema (IDTS 2002, Definition 12): `f(l) → r` follows the schema if
`r ∈ CC_f(l)` and every variable of `r` is accessible in `l`. -/
def FollowsGS (D : InductiveDecl S F) (sig : TSig S F) (Γ : V → HTy S) (pr : F → F → Prop)
    (st : F → HStat) (lhs rhs : Term (ASym F) V) : Prop :=
  ∃ (f : F) (l : List (Term (ASym F) V)), lhs = .app (.fn f) l ∧
    GSClosure D sig Γ pr st f l rhs ∧ ∀ x : V, Occurs x rhs → ∃ li ∈ l, GAcc D sig Γ li (.var x)

/-- **Embedding.** A right-hand side in the computable closure of `f(l)` whose variables are
accessible in `l` lies below `f(l)` in the recursive path order with application minimal:
accessible subterms are subterms, applications and smaller symbols use the precedence clause, and
recursive calls use the status clause through the ordering on arguments. -/
theorem GSClosure.toRPO {D : InductiveDecl S F} {sig : TSig S F} {Γ : V → HTy S}
    {pr : F → F → Prop} {st : F → HStat} {f : F} {l : List (Term (ASym F) V)}
    {r : Term (ASym F) V} (h : GSClosure D sig Γ pr st f l r) :
    (∀ x : V, Occurs x r → ∃ li ∈ l, GAcc D sig Γ li (.var x)) →
      RPO (apPrec pr) (apStat st) (.app (.fn f) l) r := by
  induction h with
  | var x =>
      intro hfv
      obtain ⟨li, hli, hacc⟩ := hfv x .here
      exact rpo_of_mem_rtSub hli hacc.sub
  | acc hu =>
      intro _
      obtain ⟨li, hli, hacc⟩ := hu
      exact rpo_of_mem_rtSub hli hacc.sub
  | ap _ _ _ _ ihu ihv =>
      intro hfv
      refine RPO.prec trivial ?_
      intro w hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl
      · exact ihu (fun x hx => hfv x (.arg List.mem_cons_self hx))
      · exact ihv (fun x hx => hfv x (.arg (List.mem_cons_of_mem _ List.mem_cons_self) hx))
  | lower hg _ _ ih =>
      intro hfv
      exact RPO.prec hg (fun u hu => ih u hu (fun x hx => hfv x (.arg hu hx)))
  | @recCall us _ _ hdec ih =>
      intro hfv
      have hdom : ∀ u ∈ us, RPO (apPrec pr) (apStat st) (.app (.fn f) l) u :=
        fun u hu => ih u hu (fun x hx => hfv x (.arg hu hx))
      cases hst : st f with
      | mul =>
          rw [hst] at hdec
          exact RPO.of_DM (by simp only [apStat, hst, HStat.toArg])
            (dm_mono (fun a b hab => hab.1.rpo) hdec)
      | lex =>
          rw [hst] at hdec
          obtain ⟨n, hn, hn', k, hpre, hcut⟩ := hdec
          exact RPO.lex (fun n => Equiv.refl (Fin n)) (by simp only [apStat, hst, HStat.toArg])
            n hn hn' k (fun i hi => hpre i hi) hcut.1.rpo hdom

theorem FollowsGS.toRPO {D : InductiveDecl S F} {sig : TSig S F} {Γ : V → HTy S}
    {pr : F → F → Prop} {st : F → HStat} {lhs rhs : Term (ASym F) V}
    (h : FollowsGS D sig Γ pr st lhs rhs) : RPO (apPrec pr) (apStat st) lhs rhs := by
  obtain ⟨f, l, rfl, hcc, hfv⟩ := h
  exact hcc.toRPO hfv

/-- **Fragment soundness of the General Schema.** A rule list whose rules follow the schema over
a well-founded precedence terminates under applicative rewriting, through
`GSClosure.toRPO`. -/
theorem gs_rules_wf {D : InductiveDecl S F} {sig : TSig S F} {Γ : V → HTy S}
    {pr : F → F → Prop} {st : F → HStat} {ν : Type}
    {R : List (Term (ASym F) V × Term (ASym F) V)} (hwf : WellFounded pr)
    (hR : ∀ lr ∈ R, FollowsGS D sig Γ pr st lr.1 lr.2) :
    WellFounded (fun u t : Term (ASym F) ν => AStep R t u) :=
  AStep.wf_of_rpo (st := apStat st) (apPrec_wf hwf) (fun lr hlr => (hR lr hlr).toRPO)

end GeneralSchema

/-- `n` is accessible in `S n` (Definition 9, cases 1 and 3). -/
theorem gs_acc_counter {Γ : TVar → TTy} :
    GAcc tInd tSig Γ (tSucc (.var .n) : TTerm TVar) (.var .n) :=
  GAcc.con (Or.inr rfl) (.self _) List.mem_cons_self

/-- `S n > n` in the ordering on arguments (Definition 10). -/
theorem gs_argGt_counter {Γ : TVar → TTy} (hΓ : Γ .n = natTy) :
    ArgGtT tInd tSig Γ (tSucc (.var .n) : TTerm TVar) (.var .n) :=
  ⟨ArgGt.arg (Or.inr rfl) List.mem_cons_self, .nat, rfl, by rw [tyOf_var, hΓ]⟩

/-- The arguments of the recursive call are smaller in either status. -/
theorem gs_statGt_counter {Γ : TVar → TTy} (hΓ : Γ .n = natTy) (x : HStat) :
    StatGt tInd tSig Γ x [.var .b, .var .s, tSucc (.var .n)] [.var .b, .var .s, .var .n] := by
  cases x with
  | mul =>
      show DM (ArgGtT tInd tSig Γ) _ _
      refine ⟨(([.var .b, .var .s] : List (TTerm TVar)) : Multiset (TTerm TVar)),
        (([.var .n] : List (TTerm TVar)) : Multiset (TTerm TVar)),
        (([tSucc (.var .n)] : List (TTerm TVar)) : Multiset (TTerm TVar)), by simp,
        (Multiset.coe_add ([.var .b, .var .s] : List (TTerm TVar)) [tSucc (.var .n)]).symm,
        (Multiset.coe_add ([.var .b, .var .s] : List (TTerm TVar)) [.var .n]).symm, ?_⟩
      intro y hy
      have hy' : y = .var .n := by simpa using hy
      subst hy'
      exact ⟨tSucc (.var .n), by simp, gs_argGt_counter hΓ⟩
  | lex =>
      refine ⟨3, rfl, rfl, ⟨2, by decide⟩, ?_, gs_argGt_counter hΓ⟩
      intro i hi
      fin_cases i
      · rfl
      · rfl
      · exact absurd hi (by decide)

/-- The three pattern variables of `g(b, s, S n)` are accessible. -/
theorem gs_vars_accessible {Γ : TVar → TTy} (x : TVar) :
    ∃ li ∈ ([.var .b, .var .s, tSucc (.var .n)] : List (TTerm TVar)),
      GAcc tInd tSig Γ li (.var x) := by
  cases x with
  | b => exact ⟨.var .b, List.mem_cons_self, .self _⟩
  | s => exact ⟨.var .s, List.mem_cons_of_mem _ List.mem_cons_self, .self _⟩
  | n => exact ⟨tSucc (.var .n), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      gs_acc_counter⟩

/-- Every pattern variable belongs to the computable closure of `g(b, s, S n)` (case 2). -/
theorem gs_var_closure {Γ : TVar → TTy} (pr : TSym → TSym → Prop) (st : TSym → HStat)
    (g : TSym) (x : TVar) :
    GSClosure tInd tSig Γ pr st g [.var .b, .var .s, tSucc (.var .n)] (.var x) :=
  GSClosure.acc (gs_vars_accessible x)

/-- The recursive call `g(b, s, n)` belongs to the computable closure (case 6). -/
theorem gs_call_closure {Γ : TVar → TTy} (hΓ : Γ .n = natTy) (pr : TSym → TSym → Prop)
    (st : TSym → HStat) (g : TSym)
    (hty : ([.var .b, .var .s, .var .n] : List (TTerm TVar)).map (tyOf tSig Γ) =
      (tSig.dom g).map some) :
    GSClosure tInd tSig Γ pr st g [.var .b, .var .s, tSucc (.var .n)]
      (.app (.fn g) [.var .b, .var .s, .var .n]) := by
  refine GSClosure.recCall ?_ hty (gs_statGt_counter hΓ _)
  intro u hu
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl | rfl <;> exact gs_var_closure pr st g _

/-- **Admission of Gödel's recursor rule** by the General Schema (IDTS 2002, Section 4: the
recursor rules follow the schema): `@(@(s, n), rec(b, s, n))` belongs to the computable closure
by cases 2, 3 and 6, since `n` is accessible in `S n` and `S n > n`. -/
theorem gs_rec_succ (A : TTy) (pr : TSym → TSym → Prop) (st : TSym → HStat) :
    FollowsGS tInd tSig (recCtx A) pr st (recSuccL A) (recSuccR A) :=
  ⟨.grec A, _, rfl,
    GSClosure.ap (GSClosure.ap (gs_var_closure pr st _ .s) (gs_var_closure pr st _ .n) rfl rfl)
      (gs_call_closure rfl pr st (.grec A) rfl) rfl rfl,
    fun x _ => gs_vars_accessible x⟩

/-- **Admission of the duplicating iterator rule** (the free duplicating rule through the
adapter). -/
theorem gs_iter_succ (A : TTy) (pr : TSym → TSym → Prop) (st : TSym → HStat) :
    FollowsGS tInd tSig (iterCtx A) pr st (iterSuccL A) (iterSuccR A) :=
  ⟨.iter A, _, rfl,
    GSClosure.ap (gs_var_closure pr st _ .s) (gs_call_closure rfl pr st (.iter A) rfl) rfl rfl,
    fun x _ => gs_vars_accessible x⟩

/-- The zero rules follow the schema: the base is accessible. -/
theorem gs_zero_rule {Γ : TVar → TTy} (g : TSym) (pr : TSym → TSym → Prop) (st : TSym → HStat) :
    FollowsGS tInd tSig Γ pr st (.app (.fn g) [.var .b, .var .s, tZero]) (.var .b) :=
  ⟨g, _, rfl, GSClosure.acc ⟨.var .b, List.mem_cons_self, .self _⟩, fun x hx => by
    cases hx
    exact ⟨.var .b, List.mem_cons_self, .self _⟩⟩

/-- The recursive call on the larger counter `S (S n)` lies above `rec(b, s, S n)` in the
recursive path order, for either status. -/
theorem rpo_larger_call (pr : TSym → TSym → Prop) (st : TSym → HStat) (A : TTy) :
    RPO (apPrec pr) (apStat st) (tRec A (.var .b) (.var .s) (tSucc (tSucc (.var .n))))
      (recSuccL A) := by
  have hSS : RPO (apPrec pr) (apStat st) (tSucc (tSucc (.var .n)) : TTerm TVar)
      (tSucc (.var .n)) := RPO.subEq List.mem_cons_self
  cases hst : st (.grec A) with
  | mul =>
      refine RPO.of_DM (by simp only [apStat, hst, HStat.toArg])
        ⟨(([.var .b, .var .s] : List (TTerm TVar)) : Multiset (TTerm TVar)),
          (([tSucc (.var .n)] : List (TTerm TVar)) : Multiset (TTerm TVar)),
          (([tSucc (tSucc (.var .n))] : List (TTerm TVar)) : Multiset (TTerm TVar)), by simp,
          (Multiset.coe_add ([.var .b, .var .s] : List (TTerm TVar))
            [tSucc (tSucc (.var .n))]).symm,
          (Multiset.coe_add ([.var .b, .var .s] : List (TTerm TVar)) [tSucc (.var .n)]).symm, ?_⟩
      intro y hy
      have hy' : y = tSucc (.var .n) := by simpa using hy
      subst hy'
      exact ⟨tSucc (tSucc (.var .n)), by simp, hSS⟩
  | lex =>
      refine RPO.lex (fun n => Equiv.refl (Fin n)) (by simp only [apStat, hst, HStat.toArg])
        3 rfl rfl ⟨2, by decide⟩ ?_ hSS ?_
      · intro i hi
        fin_cases i
        · rfl
        · rfl
        · exact absurd hi (by decide)
      · intro u hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl
        · exact RPO.subEq List.mem_cons_self
        · exact RPO.subEq (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact RPO.subGt _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            hSS

/-- A recursive call on a larger counter is rejected under the laws. -/
theorem gs_rejects_larger_counter (A : TTy) {pr : TSym → TSym → Prop} (st : TSym → HStat)
    (hwf : WellFounded pr) (htr : ∀ a b c, pr a b → pr b c → pr a c) :
    ¬ FollowsGS tInd tSig (recCtx A) pr st (recSuccL A)
      (tApp (tApp (.var .s) (.var .n)) (tRec A (.var .b) (.var .s) (tSucc (tSucc (.var .n))))) := by
  intro h
  have htr' := apPrec_trans htr
  have h2 : RPO (apPrec pr) (apStat st)
      (tApp (tApp (.var .s) (.var .n)) (tRec A (.var .b) (.var .s) (tSucc (tSucc (.var .n))))
        : TTerm TVar)
      (tRec A (.var .b) (.var .s) (tSucc (tSucc (.var .n))) : TTerm TVar) :=
    RPO.subEq (List.mem_cons_of_mem _ List.mem_cons_self)
  exact RPO.irrefl (apPrec_wf hwf) _
    (RPO.trans htr' (RPO.trans htr' h.toRPO h2) (rpo_larger_call pr st A))

/-- The call `iter(b, @(s, n), n)` of another defined symbol inside a rule defining `rec`. -/
abbrev iterCallRhs (A : TTy) : TTerm TVar := tIter A (.var .b) (tApp (.var .s) (.var .n)) (.var .n)

/-- A precedence that places the iterator below the recursor. -/
def gsRankIterLow : TSym → Nat
  | .zero => 0
  | .succ => 1
  | .iter _ => 2
  | .grec _ => 3

/-- The call dependency is governed by the precedence: with `iter` and `rec` of equal rank the
call `iter(b, @(s, n), n)` is forbidden (neither case 5 nor case 6 applies, and the call is not
a subterm), while with `iter <F rec` it belongs to the closure by case 5. -/
theorem gs_call_dependency (A : TTy) :
    ¬ FollowsGS tInd tSig (recCtx A) (fun a b : TSym => tRank a < tRank b) (fun _ => .mul)
        (recSuccL A) (iterCallRhs A) ∧
      FollowsGS tInd tSig (recCtx A) (fun a b : TSym => gsRankIterLow a < gsRankIterLow b)
        (fun _ => .mul) (recSuccL A) (iterCallRhs A) := by
  constructor
  · rintro ⟨f, l, hl, hcc, _⟩
    cases hl
    cases hcc with
    | acc hu =>
        obtain ⟨li, hli, hacc⟩ := hu
        have hle := rtSub_size_le hacc.sub
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hli
        rcases hli with rfl | rfl | rfl <;>
          simp only [Term.size_app, Term.size_var, Term.sizeList_cons, Term.sizeList_nil] at hle <;>
          omega
    | lower hg _ _ => exact absurd hg (lt_irrefl 2)
  · refine ⟨.grec A, _, rfl, ?_, fun x _ => gs_vars_accessible x⟩
    refine GSClosure.lower (show (2 : Nat) < 3 by decide) ?_ rfl
    intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact gs_var_closure _ _ _ .b
    · exact GSClosure.ap (gs_var_closure _ _ _ .s) (gs_var_closure _ _ _ .n) rfl rfl
    · exact gs_var_closure _ _ _ .n

/-- Native data of `generalSchemaAdmittance`: a precedence and a status on the System T
symbols (IDTS 2002, Definitions 4 and 8). -/
structure generalSchemaAdmittanceData : Type where
  prec : TSym → TSym → Prop
  stat : TSym → HStat

/-- Blanqui, Jouannaud and Okada, TCS 272 (2002), Definition 4 and Assumption 2: the strict
precedence is well founded (and transitive); statuses agree on equivalent symbols, which here are
equal symbols. -/
def generalSchemaAdmittanceLaws (M : generalSchemaAdmittanceData) : Prop :=
  WellFounded M.prec ∧ ∀ a b c, M.prec a b → M.prec b c → M.prec a c

/-- The General Schema's own acceptance of the free two-rule system through the adapter `toA`:
both typed iterator rules follow the schema at every result type. -/
def generalSchemaAdmittanceAccepts (M : generalSchemaAdmittanceData) : Prop :=
  ∀ A : TTy, FollowsGS tInd tSig (iterCtx A) M.prec M.stat (iterZeroL A) (.var .b) ∧
    FollowsGS tInd tSig (iterCtx A) M.prec M.stat (iterSuccL A) (iterSuccR A)

/-- The schema accepts the typed free system, and the fragment soundness theorem yields
termination of the typed iterator rules and of the free schema.
Verdict: fragment escape. -/
def generalSchemaAdmittanceResult (M : generalSchemaAdmittanceData) : Prop :=
  generalSchemaAdmittanceAccepts M ∧ TypedFreeTermination

/-- **Soundness** of the fragment: rules following the schema over a well-founded precedence
terminate, through the embedding of the computable closure into the recursive path order. -/
theorem generalSchemaAdmittance_sound : ∀ M : generalSchemaAdmittanceData,
    generalSchemaAdmittanceLaws M → generalSchemaAdmittanceAccepts M → TypedFreeTermination := by
  intro M hL hA
  have hwf : ∀ (A : TTy) (ν : Type),
      WellFounded (fun u t : TTerm ν => AStep (iterRules A) t u) := by
    intro A ν
    refine gs_rules_wf (D := tInd) (sig := tSig) (Γ := iterCtx A) (st := M.stat) hL.1 ?_
    intro lr hlr
    simp only [iterRules, List.mem_cons, List.mem_nil_iff, or_false] at hlr
    rcases hlr with rfl | rfl
    · exact (hA A).1
    · exact (hA A).2
  exact ⟨hwf, fun ν => free_wf_of_iter (.sort .o) (hwf _ ν)⟩

/-- Witness: rank precedence and multiset status. -/
def generalSchemaAdmittanceWitness : generalSchemaAdmittanceData where
  prec := fun a b => tRank a < tRank b
  stat := fun _ => .mul

theorem generalSchemaAdmittanceWitness_laws :
    generalSchemaAdmittanceLaws generalSchemaAdmittanceWitness :=
  ⟨tRank_wf, fun _ _ _ h₁ h₂ => lt_trans h₁ h₂⟩

theorem generalSchemaAdmittanceWitness_accepts :
    generalSchemaAdmittanceAccepts generalSchemaAdmittanceWitness :=
  fun A => ⟨gs_zero_rule (.iter A) _ _, gs_iter_succ A _ _⟩

theorem generalSchemaAdmittanceWitness_result :
    generalSchemaAdmittanceResult generalSchemaAdmittanceWitness :=
  ⟨generalSchemaAdmittanceWitness_accepts,
    generalSchemaAdmittance_sound _ generalSchemaAdmittanceWitness_laws
      generalSchemaAdmittanceWitness_accepts⟩

/-- **Defining features.** The right side of Gödel's recursor rule belongs to the computable
closure; admission rests on the accessibility of `n` in `S n` and on `S n > n`; a recursive call
on the larger counter `S (S n)` is rejected; a call of `iter` from a rule defining `rec` is
forbidden at equal rank and allowed once `iter <F rec`. -/
theorem generalSchemaAdmittanceWitness_feature :
    (∀ A : TTy, FollowsGS tInd tSig (recCtx A) generalSchemaAdmittanceWitness.prec
        generalSchemaAdmittanceWitness.stat (recSuccL A) (recSuccR A)) ∧
      (∀ A : TTy, GAcc tInd tSig (recCtx A) (tSucc (.var .n)) (.var .n) ∧
        ArgGtT tInd tSig (recCtx A) (tSucc (.var .n)) (.var .n)) ∧
      (∀ A : TTy, ¬ FollowsGS tInd tSig (recCtx A) generalSchemaAdmittanceWitness.prec
        generalSchemaAdmittanceWitness.stat (recSuccL A)
        (tApp (tApp (.var .s) (.var .n)) (tRec A (.var .b) (.var .s) (tSucc (tSucc (.var .n)))))) ∧
      (∀ A : TTy, ¬ FollowsGS tInd tSig (recCtx A) generalSchemaAdmittanceWitness.prec
          generalSchemaAdmittanceWitness.stat (recSuccL A) (iterCallRhs A) ∧
        FollowsGS tInd tSig (recCtx A) (fun a b : TSym => gsRankIterLow a < gsRankIterLow b)
          (fun _ => .mul) (recSuccL A) (iterCallRhs A)) :=
  ⟨fun A => gs_rec_succ A _ _, fun _ => ⟨gs_acc_counter, gs_argGt_counter rfl⟩,
    fun A => gs_rejects_larger_counter A _ tRank_wf (fun _ _ _ h₁ h₂ => lt_trans h₁ h₂),
    fun A => gs_call_dependency A⟩

/-- **Mutation.** The total relation as precedence, everything else fixed, is not well
founded. -/
theorem generalSchemaAdmittance_mutation :
    ¬ generalSchemaAdmittanceLaws { generalSchemaAdmittanceWitness with prec := fun _ _ => True } :=
  fun h => h.1.isIrrefl.irrefl TSym.zero trivial

/-- **Scope.** The fragment omits λ-abstraction and the cases that involve it (Definition 9
cases 2 and 4, Definition 11 case 4), the ordering on arguments for a nonempty argument vector
and for non-inductive types (Definition 10; strictly positive types with functional constructor
arguments such as Brouwer's ordinals), statuses that combine lexicographic and multiset groups
(Definition 7), β- and η-reduction, and the computability proof of strong normalization
(Theorem 20; ESTABLISHED). Formally: every rule of the fragment has a symbol-headed left side and
lies inside the first-order recursive path order with application minimal. -/
theorem generalSchemaAdmittance_scope :
    ∀ (pr : TSym → TSym → Prop) (st : TSym → HStat) (Γ : TVar → TTy) (lhs rhs : TTerm TVar),
      FollowsGS tInd tSig Γ pr st lhs rhs →
        (∃ f l, lhs = .app (.fn f) l) ∧ RPO (apPrec pr) (apStat st) lhs rhs := by
  intro pr st Γ lhs rhs h
  refine ⟨?_, h.toRPO⟩
  obtain ⟨f, l, hl, _, _⟩ := h
  exact ⟨f, l, hl⟩

/-- **System T (row B1).** Gödel's recursor rules `rec b s (S n) → s n (rec b s n)` and
`rec b s 0 → b` follow the General Schema for every precedence and status. -/
theorem generalSchemaAdmittance_admits_systemT : ∀ (M : generalSchemaAdmittanceData) (A : TTy),
    FollowsGS tInd tSig (recCtx A) M.prec M.stat (recSuccL A) (recSuccR A) ∧
      FollowsGS tInd tSig (recCtx A) M.prec M.stat (recZeroL A) (.var .b) :=
  fun M A => ⟨gs_rec_succ A M.prec M.stat, gs_zero_rule (.grec A) M.prec M.stat⟩

/-- System T recursor rewriting terminates by the fragment soundness theorem of the General
Schema. -/
theorem generalSchemaAdmittance_systemT_terminates : ∀ M : generalSchemaAdmittanceData,
    generalSchemaAdmittanceLaws M →
      ∀ (A : TTy) (ν : Type), WellFounded (fun u t : TTerm ν => AStep (recRules A) t u) := by
  intro M hL A ν
  refine gs_rules_wf (D := tInd) (sig := tSig) (Γ := recCtx A) (st := M.stat) hL.1 ?_
  intro lr hlr
  simp only [recRules, List.mem_cons, List.mem_nil_iff, or_false] at hlr
  rcases hlr with rfl | rfl
  · exact (generalSchemaAdmittance_admits_systemT M A).2
  · exact (generalSchemaAdmittance_admits_systemT M A).1

/-! ## 7. Row `sizedTypesAdmittance`: size-annotated types

Barthe, Frade, Giménez, Pinto and Uustalu, *Type-based termination of recursive definitions*,
Mathematical Structures in Computer Science 14(1), 2004, 97–141 (sized types after Hughes,
Pareto and Sabry, POPL 1996): Definition 2.6 (stages and types), Definition 2.11 with Figures 1
and 2 (stage comparison and subtyping), Definition 2.17 with Figure 3 (typing, with the rules
(var), (cons), (app), (sub) and (rec)), Proposition 3.32 (soundness of stage comparison) and
Proposition 3.36 (strong normalisation). The fragment reads the rule (rec) on the defining rules
of the recursor: the matched counter `S n` has the successor stage `ı̂` of the pattern variable
`n : Nat^ı` (rule (case)), and on the right side the defined symbol is available only at the
hypothesis type `… → Nat^ı → θ` of (rec). -/

/-- Stage expressions (Definition 2.6): stage variables, the successor `ŝ` and the limit `∞`. -/
inductive Stage : Type where
  | var (i : Nat)
  | hat (s : Stage)
  | inf
  deriving DecidableEq

/-- Stage comparison (Definition 2.11, Figure 1). -/
inductive SLe : Stage → Stage → Prop
  | refl (s : Stage) : SLe s s
  | trans {s r p : Stage} (h₁ : SLe s r) (h₂ : SLe r p) : SLe s p
  | hat (s : Stage) : SLe s (.hat s)
  | infty (s : Stage) : SLe s .inf

/-- Sized types over the System T sorts (Definition 2.6, with the datatype `Nat`). -/
inductive SzTy : Type where
  | snat (s : Stage)
  | so
  | arrow (A B : SzTy)
  deriving DecidableEq

/-- Subtyping (Definition 2.11, Figure 2). -/
inductive SzSub : SzTy → SzTy → Prop
  | refl (σ : SzTy) : SzSub σ σ
  | data {s r : Stage} (h : SLe s r) : SzSub (.snat s) (.snat r)
  | func {τ τ' σ σ' : SzTy} (h₁ : SzSub τ' τ) (h₂ : SzSub σ σ') :
      SzSub (.arrow τ σ) (.arrow τ' σ')

/-- Unsized types as sized types at the limit stage (Notation 2.7: `d` abbreviates `d^∞`). -/
def liftTy : TTy → SzTy
  | .sort .nat => .snat .inf
  | .sort .o => .so
  | .arrow A B => .arrow (liftTy A) (liftTy B)

/-- The stage variable `i` occurs in a stage. -/
def Stage.hasVar (i : Nat) : Stage → Prop
  | .var j => j = i
  | .hat s => s.hasVar i
  | .inf => False

/-- The stage variable `i` occurs in a sized type. -/
def SzTy.hasVar (i : Nat) : SzTy → Prop
  | .snat s => s.hasVar i
  | .so => False
  | .arrow A B => A.hasVar i ∨ B.hasVar i

/-- Declared argument type of a symbol at a position. -/
def argTy (g : TSym) (k : Nat) : TTy := (tSig.dom g).getD k natTy

/-- The sized typing judgment of a defining rule of `g` at the stage variable `i`, with the
size-annotated types `Δ` of the pattern variables (Figure 3 read on rewrite rules). -/
inductive SzHas (g : TSym) (i : Nat) (Δ : TVar → SzTy) : TTerm TVar → SzTy → Prop
  /-- (var). -/
  | var (x : TVar) : SzHas g i Δ (.var x) (Δ x)
  /-- (cons) for `o : Nat^ŝ`. -/
  | zero (s : Stage) : SzHas g i Δ tZero (.snat (.hat s))
  /-- (cons) with (app) for `s : Nat^s → Nat^ŝ`. -/
  | succ (s : Stage) {t : TTerm TVar} (h : SzHas g i Δ t (.snat s)) :
      SzHas g i Δ (tSucc t) (.snat (.hat s))
  /-- The hypothesis of (rec): the defined symbol takes its size argument at `Nat^ı`. -/
  | call {u₁ u₂ u₃ : TTerm TVar} (h₁ : SzHas g i Δ u₁ (liftTy (argTy g 0)))
      (h₂ : SzHas g i Δ u₂ (liftTy (argTy g 1))) (h₃ : SzHas g i Δ u₃ (.snat (.var i))) :
      SzHas g i Δ (.app (.fn g) [u₁, u₂, u₃]) (liftTy (tSig.cod g))
  /-- (app). -/
  | ap {t u : TTerm TVar} {τ σ : SzTy} (ht : SzHas g i Δ t (.arrow τ σ))
      (hu : SzHas g i Δ u τ) : SzHas g i Δ (tApp t u) σ
  /-- (sub). -/
  | sub {t : TTerm TVar} {σ σ' : SzTy} (h : SzHas g i Δ t σ) (hs : SzSub σ σ') :
      SzHas g i Δ t σ'

/-- Interpretation of stages in `ℕ∞` under a valuation of the stage variables (Section 3.2). -/
def Stage.val (ρ : Nat → ENat) : Stage → ENat
  | .var j => ρ j
  | .hat s => s.val ρ + 1
  | .inf => ⊤

/-- Soundness of stage comparison (Proposition 3.32, with values in `ℕ∞`). -/
theorem SLe.val_le {s r : Stage} (h : SLe s r) (ρ : Nat → ENat) : s.val ρ ≤ r.val ρ := by
  induction h with
  | refl s => exact le_rfl
  | trans _ _ ih₁ ih₂ => exact le_trans ih₁ ih₂
  | hat s => exact le_self_add
  | infty s => exact le_top

/-- The stage value of the positive result of a sized type. -/
def SzTy.posVal (ρ : Nat → ENat) : SzTy → ENat
  | .snat s => s.val ρ
  | .so => ⊤
  | .arrow _ B => B.posVal ρ

theorem SzSub.posVal_le {σ σ' : SzTy} (h : SzSub σ σ') (ρ : Nat → ENat) :
    σ.posVal ρ ≤ σ'.posVal ρ := by
  induction h with
  | refl σ => exact le_rfl
  | data h => exact h.val_le ρ
  | func _ _ _ ih₂ => exact ih₂

theorem SzSub.snat_inv {r : Stage} {σ : SzTy} (h : SzSub (.snat r) σ) : ∃ r', σ = .snat r' := by
  cases h with
  | refl => exact ⟨r, rfl⟩
  | data _ => exact ⟨_, rfl⟩

/-- The valuation that sends the stage variable `i` to `0` and every other variable to `1`. -/
def stageVal0 (i : Nat) : Nat → ENat := fun j => if j = i then 0 else 1

theorem Stage.one_le_val {i : Nat} : ∀ {s : Stage}, ¬ s.hasVar i → 1 ≤ s.val (stageVal0 i)
  | .var j, h => by
      have hj : ¬ j = i := h
      simp only [Stage.val, stageVal0, if_neg hj, le_refl]
  | .hat _, _ => le_add_self
  | .inf, _ => le_top

theorem SzTy.one_le_posVal {i : Nat} :
    ∀ {σ : SzTy}, ¬ σ.hasVar i → 1 ≤ σ.posVal (stageVal0 i)
  | .snat _, h => Stage.one_le_val h
  | .so, _ => le_top
  | .arrow _ B, h => SzTy.one_le_posVal (σ := B) (fun hB => h (Or.inr hB))

theorem liftTy_noVar (i : Nat) : ∀ A : TTy, ¬ (liftTy A).hasVar i
  | .sort .nat => fun h => h
  | .sort .o => fun h => h
  | .arrow A B => fun h => h.elim (liftTy_noVar i A) (liftTy_noVar i B)

/-- **The counter lemma of the size-decrease check.** If the labels of `b` and `s` do not mention
the stage variable `ı` and `n : Nat^ı`, every typed term is `n` itself or has a type whose
positive result stage is at least `1` when `ı` is read as `0`. -/
theorem SzHas.counter_or_pos {g : TSym} {i : Nat} {Δ : TVar → SzTy}
    (hb : ¬ (Δ .b).hasVar i) (hs : ¬ (Δ .s).hasVar i) (hn : Δ .n = .snat (.var i))
    {t : TTerm TVar} {σ : SzTy} (h : SzHas g i Δ t σ) :
    (t = .var .n ∧ ∃ r, σ = .snat r) ∨ 1 ≤ σ.posVal (stageVal0 i) := by
  induction h with
  | var x =>
      cases x with
      | b => exact Or.inr (SzTy.one_le_posVal hb)
      | s => exact Or.inr (SzTy.one_le_posVal hs)
      | n => exact Or.inl ⟨rfl, .var i, hn⟩
  | zero s => exact Or.inr (show (1 : ENat) ≤ s.val (stageVal0 i) + 1 from le_add_self)
  | succ s _ _ => exact Or.inr (show (1 : ENat) ≤ s.val (stageVal0 i) + 1 from le_add_self)
  | call _ _ _ _ _ _ => exact Or.inr (SzTy.one_le_posVal (liftTy_noVar i _))
  | ap _ _ iht _ =>
      rcases iht with ⟨_, r, hr⟩ | hpos
      · cases hr
      · exact Or.inr hpos
  | sub _ hsub ih =>
      rcases ih with ⟨rfl, r, rfl⟩ | hpos
      · exact Or.inl ⟨rfl, hsub.snat_inv⟩
      · exact Or.inr (le_trans hpos (hsub.posVal_le _))

/-- The only term typable at `Nat^ı` is the pattern variable `n`: the size argument of every
recursive call is the predecessor of the matched counter. -/
theorem SzHas.counter_eq {g : TSym} {i : Nat} {Δ : TVar → SzTy}
    (hb : ¬ (Δ .b).hasVar i) (hs : ¬ (Δ .s).hasVar i) (hn : Δ .n = .snat (.var i))
    {u : TTerm TVar} (h : SzHas g i Δ u (.snat (.var i))) : u = .var .n := by
  rcases h.counter_or_pos hb hs hn with ⟨rfl, _⟩ | hpos
  · rfl
  · exact absurd hpos (by simp [SzTy.posVal, Stage.val, stageVal0])

/-- Status of the recursive path order used by the embedding: the three-argument symbols compare
their arguments lexicographically with the size argument first. -/
def szStat : ASym TSym → ArgStatus
  | .fn _ => .lex (fun _ => Fin.revPerm)
  | .ap => .mul

/-- Precedence of the embedding: the rank of the System T symbols, application minimal. -/
abbrev szPrec : ASym TSym → ASym TSym → Prop := apPrec (fun a b : TSym => tRank a < tRank b)

/-- **Embedding, successor branch.** A right side typed in the sized judgment of `g` lies below
`g(b, s, S n)` in the recursive path order: pattern variables are subterms, constructors and
application use the precedence, and recursive calls use the counter-first lexicographic status,
since their size argument is `n` by `SzHas.counter_eq`. -/
theorem SzHas.toRPO_succ {g : TSym} (hg : tRank g = 2) {i : Nat} {Δ : TVar → SzTy}
    (hb : ¬ (Δ .b).hasVar i) (hs : ¬ (Δ .s).hasVar i) (hn : Δ .n = .snat (.var i))
    {t : TTerm TVar} {σ : SzTy} (h : SzHas g i Δ t σ) :
    RPO szPrec szStat (.app (.fn g) [.var .b, .var .s, tSucc (.var .n)]) t := by
  induction h with
  | var x =>
      have h3 : (tSucc (.var .n) : TTerm TVar) ∈ [.var .b, .var .s, tSucc (.var .n)] :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      cases x with
      | b => exact RPO.subEq List.mem_cons_self
      | s => exact RPO.subEq (List.mem_cons_of_mem _ List.mem_cons_self)
      | n => exact RPO.subGt _ h3 (RPO.subEq List.mem_cons_self)
  | zero s =>
      exact RPO.prec (show tRank TSym.zero < tRank g by rw [hg]; decide)
        (fun u hu => by simp at hu)
  | succ s _ ih =>
      refine RPO.prec (show tRank TSym.succ < tRank g by rw [hg]; decide) ?_
      intro u hu
      rw [List.mem_singleton] at hu
      subst hu
      exact ih
  | @call u₁ u₂ u₃ _ _ h₃ ih₁ ih₂ _ =>
      obtain rfl := h₃.counter_eq hb hs hn
      refine RPO.lex (fun _ => Fin.revPerm) rfl 3 rfl rfl 0 ?_ ?_ ?_
      · intro j hj
        exact absurd hj (Fin.not_lt_zero j)
      · exact RPO.subEq List.mem_cons_self
      · intro u hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl
        · exact ih₁
        · exact ih₂
        · exact RPO.subGt _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            (RPO.subEq List.mem_cons_self)
  | ap _ _ iht ihu =>
      refine RPO.prec trivial ?_
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact iht
      · exact ihu
  | sub _ _ ih => exact ih

/-- **Embedding, zero branch.** A right side without the variable `n` typed in the sized judgment
of `g` lies below `g(b, s, 0)`: it contains no recursive call, since a call needs a size argument
of type `Nat^ı`, which only `n` has. -/
theorem SzHas.toRPO_zero {g : TSym} (hg : tRank g = 2) {i : Nat} {Δ : TVar → SzTy}
    (hb : ¬ (Δ .b).hasVar i) (hs : ¬ (Δ .s).hasVar i) (hn : Δ .n = .snat (.var i))
    {t : TTerm TVar} {σ : SzTy} (h : SzHas g i Δ t σ) :
    ¬ Occurs TVar.n t → RPO szPrec szStat (.app (.fn g) [.var .b, .var .s, tZero]) t := by
  induction h with
  | var x =>
      intro hno
      cases x with
      | b => exact RPO.subEq List.mem_cons_self
      | s => exact RPO.subEq (List.mem_cons_of_mem _ List.mem_cons_self)
      | n => exact absurd .here hno
  | zero s =>
      intro _
      exact RPO.prec (show tRank TSym.zero < tRank g by rw [hg]; decide)
        (fun u hu => by simp at hu)
  | succ s _ ih =>
      intro hno
      refine RPO.prec (show tRank TSym.succ < tRank g by rw [hg]; decide) ?_
      intro u hu
      rw [List.mem_singleton] at hu
      subst hu
      exact ih (fun ho => hno (.arg List.mem_cons_self ho))
  | @call u₁ u₂ u₃ _ _ h₃ _ _ _ =>
      intro hno
      obtain rfl := h₃.counter_eq hb hs hn
      exact absurd (Occurs.arg (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        .here) hno
  | ap _ _ iht ihu =>
      intro hno
      refine RPO.prec trivial ?_
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact iht (fun ho => hno (.arg List.mem_cons_self ho))
      · exact ihu (fun ho => hno (.arg (List.mem_cons_of_mem _ List.mem_cons_self) ho))
  | sub _ _ ih => exact ih

/-- Labels of the iterator rules at stage variable `i`: `b : A`, `s : A → A`, `n : Nat^ı`. -/
def sizedIterLabels (i : Nat) (A : TTy) : TVar → SzTy
  | .b => liftTy A
  | .s => liftTy (.arrow A A)
  | .n => .snat (.var i)

/-- Labels of the recursor rules at stage variable `i`: `b : A`, `s : nat → A → A`,
`n : Nat^ı`. -/
def sizedRecLabels (i : Nat) (A : TTy) : TVar → SzTy
  | .b => liftTy A
  | .s => liftTy (.arrow natTy (.arrow A A))
  | .n => .snat (.var i)

/-- Native data of `sizedTypesAdmittance`: the stage variable `ı` of the rule (rec) and the
size-annotated types of the pattern variables at every result type. -/
structure sizedTypesAdmittanceData : Type where
  stageVar : Nat
  labels : TTy → TVar → SzTy

/-- Barthe, Frade, Giménez, Pinto and Uustalu, MSCS 14 (2004), Figure 3: in the rule (rec) the
stage variable `ı` does not occur in the context (the labels of `b` and `s`), and the rule (case)
types the predecessor `n` of a counter of type `Nat^ı̂` at `Nat^ı`. -/
def sizedTypesAdmittanceLaws (M : sizedTypesAdmittanceData) : Prop :=
  ∀ A : TTy, ¬ (M.labels A .b).hasVar M.stageVar ∧ ¬ (M.labels A .s).hasVar M.stageVar ∧
    M.labels A .n = .snat (.var M.stageVar)

/-- The size-decrease check on the free two-rule system through the adapter `toA`: both right
sides of the typed iterator rules are typable in the sized judgment, where the iterator is
available only at the hypothesis type of (rec). -/
def sizedTypesAdmittanceAccepts (M : sizedTypesAdmittanceData) : Prop :=
  ∀ A : TTy, SzHas (.iter A) M.stageVar (M.labels A) (.var .b) (liftTy A) ∧
    SzHas (.iter A) M.stageVar (M.labels A) (iterSuccR A) (liftTy A)

/-- The check accepts the typed free system, and recursion soundness of the fragment yields
termination of the typed iterator rules and of the free schema.
Verdict: fragment escape. -/
def sizedTypesAdmittanceResult (M : sizedTypesAdmittanceData) : Prop :=
  sizedTypesAdmittanceAccepts M ∧ TypedFreeTermination

/-- **Recursion soundness** of the fragment: under the laws, size-checked rules decrease in the
recursive path order with counter-first lexicographic status, whose well-foundedness gives
termination. -/
theorem sizedTypesAdmittance_sound : ∀ M : sizedTypesAdmittanceData,
    sizedTypesAdmittanceLaws M → sizedTypesAdmittanceAccepts M → TypedFreeTermination := by
  intro M hL hA
  have hwf : ∀ (A : TTy) (ν : Type),
      WellFounded (fun u t : TTerm ν => AStep (iterRules A) t u) := by
    intro A ν
    obtain ⟨hb, hs, hn⟩ := hL A
    refine AStep.wf_of_rpo (st := szStat) (apPrec_wf tRank_wf) ?_
    intro lr hlr
    simp only [iterRules, List.mem_cons, List.mem_nil_iff, or_false] at hlr
    rcases hlr with rfl | rfl
    · exact (hA A).1.toRPO_zero rfl hb hs hn (fun h => by cases h)
    · exact (hA A).2.toRPO_succ rfl hb hs hn
  exact ⟨hwf, fun ν => free_wf_of_iter (.sort .o) (hwf _ ν)⟩

/-- Witness: stage variable `0` and the iterator labels. -/
def sizedTypesAdmittanceWitness : sizedTypesAdmittanceData where
  stageVar := 0
  labels := sizedIterLabels 0

theorem sizedTypesAdmittanceWitness_laws :
    sizedTypesAdmittanceLaws sizedTypesAdmittanceWitness :=
  fun A => ⟨liftTy_noVar 0 A, liftTy_noVar 0 _, rfl⟩

/-- The iterator rules pass the size-decrease check. -/
theorem sized_iter_accepts (i : Nat) (A : TTy) :
    SzHas (.iter A) i (sizedIterLabels i A) (.var .b) (liftTy A) ∧
      SzHas (.iter A) i (sizedIterLabels i A) (iterSuccR A) (liftTy A) :=
  ⟨SzHas.var .b, SzHas.ap (SzHas.var .s) (SzHas.call (SzHas.var .b) (SzHas.var .s) (SzHas.var .n))⟩

theorem sizedTypesAdmittanceWitness_result :
    sizedTypesAdmittanceResult sizedTypesAdmittanceWitness :=
  ⟨fun A => sized_iter_accepts 0 A,
    sizedTypesAdmittance_sound _ sizedTypesAdmittanceWitness_laws (fun A => sized_iter_accepts 0 A)⟩

/-- **System T (row B1).** The size-decrease check admits Gödel's recursor rules
`rec b s (S n) → s n (rec b s n)` and `rec b s 0 → b`: the right sides are typable with
`n : Nat^ı` and the recursor at the hypothesis type of (rec). -/
theorem sizedTypesAdmittance_admits_systemT : ∀ (i : Nat) (A : TTy),
    SzHas (.grec A) i (sizedRecLabels i A) (recSuccR A) (liftTy A) ∧
      SzHas (.grec A) i (sizedRecLabels i A) (.var .b) (liftTy A) :=
  fun _ _ =>
    ⟨SzHas.ap (SzHas.ap (SzHas.var .s) (SzHas.sub (SzHas.var .n) (SzSub.data (SLe.infty _))))
        (SzHas.call (SzHas.var .b) (SzHas.var .s) (SzHas.var .n)), SzHas.var .b⟩

/-- System T recursor rewriting terminates by recursion soundness of the fragment. -/
theorem sizedTypesAdmittance_systemT_terminates :
    ∀ (A : TTy) (ν : Type), WellFounded (fun u t : TTerm ν => AStep (recRules A) t u) := by
  intro A ν
  have hb : ¬ (sizedRecLabels 0 A .b).hasVar 0 := liftTy_noVar 0 A
  have hs : ¬ (sizedRecLabels 0 A .s).hasVar 0 := liftTy_noVar 0 _
  have hn : sizedRecLabels 0 A .n = .snat (.var 0) := rfl
  refine AStep.wf_of_rpo (st := szStat) (apPrec_wf tRank_wf) ?_
  intro lr hlr
  simp only [recRules, List.mem_cons, List.mem_nil_iff, or_false] at hlr
  rcases hlr with rfl | rfl
  · exact (sizedTypesAdmittance_admits_systemT 0 A).2.toRPO_zero rfl hb hs hn (fun h => by cases h)
  · exact (sizedTypesAdmittance_admits_systemT 0 A).1.toRPO_succ rfl hb hs hn

/-- Arbitrary labels: `b` labelled at the stage `ı` of the hypothesis, against the freshness
condition of (rec). -/
def badLabels : TVar → SzTy
  | .b => .snat (.var 0)
  | .s => liftTy (.arrow natTy (.arrow natTy natTy))
  | .n => .snat (.var 0)

/-- The looping rule `rec(b, s, S n) → rec(b, s, b)`. -/
def loopRules : List (TTerm TVar × TTerm TVar) :=
  [(recSuccL natTy, tRec natTy (.var .b) (.var .s) (.var .b))]

theorem loopRules_not_wf :
    ¬ WellFounded (fun u t : TTerm TVar => AStep loopRules t u) := by
  intro hwf
  let θ : TVar → TTerm TVar := fun
    | .b => tSucc tZero
    | .s => .var .s
    | .n => tZero
  have h := ARoot.inst (R := loopRules) (l := recSuccL natTy)
    (r := tRec natTy (.var .b) (.var .s) (.var .b)) List.mem_cons_self θ
  have e1 : tbind θ (recSuccL natTy) = tRec natTy (tSucc tZero) (.var .s) (tSucc tZero) := by
    simp [tbind_app, θ]
  have e2 : tbind θ (tRec natTy (.var .b) (.var .s) (.var .b)) =
      tRec natTy (tSucc tZero) (.var .s) (tSucc tZero) := by
    simp [tbind_app, θ]
  rw [e1, e2] at h
  exact hwf.isIrrefl.irrefl _ (AStep.root h)

/-- **Defining features.** The recursor definition is typed with size variables; the
size-decrease check types `n` at `Nat^ı` and rejects `S n` there; a recursive call on the
matched counter `S n` (an equal-size call) is rejected; arbitrary size labels are unsound: with
`b` labelled at `Nat^ı`, against the freshness law, the check accepts the looping rule
`rec(b, s, S n) → rec(b, s, b)`. -/
theorem sizedTypesAdmittanceWitness_feature :
    (∀ A : TTy, SzHas (.grec A) 0 (sizedRecLabels 0 A) (recSuccR A) (liftTy A)) ∧
      (∀ A : TTy, SzHas (.grec A) 0 (sizedRecLabels 0 A) (.var .n) (.snat (.var 0)) ∧
        ¬ SzHas (.grec A) 0 (sizedRecLabels 0 A) (tSucc (.var .n)) (.snat (.var 0))) ∧
      (∀ A : TTy, ¬ SzHas (.grec A) 0 (sizedRecLabels 0 A)
        (tApp (tApp (.var .s) (.var .n)) (recSuccL A)) (liftTy A)) ∧
      (SzHas (.grec natTy) 0 badLabels (tRec natTy (.var .b) (.var .s) (.var .b)) (liftTy natTy) ∧
        (badLabels .b).hasVar 0 ∧
        ¬ WellFounded (fun u t : TTerm TVar => AStep loopRules t u)) := by
  refine ⟨fun A => (sizedTypesAdmittance_admits_systemT 0 A).1, fun A => ⟨SzHas.var .n, ?_⟩,
    fun A => ?_, ⟨?_, rfl, loopRules_not_wf⟩⟩
  · intro h
    have := h.counter_eq (liftTy_noVar 0 A) (liftTy_noVar 0 _) rfl
    cases this
  · intro h
    exact rpo_not_superterm (apPrec_wf tRank_wf) (apPrec_trans (fun _ _ _ h₁ h₂ => lt_trans h₁ h₂))
      (List.mem_cons_of_mem _ List.mem_cons_self)
      (h.toRPO_succ rfl (liftTy_noVar 0 A) (liftTy_noVar 0 _) rfl)
  · exact SzHas.call (SzHas.sub (SzHas.var .b) (SzSub.data (SLe.infty _))) (SzHas.var .s)
      (SzHas.var .b)

/-- **Mutation.** Moving the stage variable of (rec) to `1`, everything else fixed, breaks the
law that types the pattern variable `n` at `Nat^ı`. -/
theorem sizedTypesAdmittance_mutation :
    ¬ sizedTypesAdmittanceLaws { sizedTypesAdmittanceWitness with stageVar := 1 } :=
  fun h => absurd (h natTy).2.2 (by decide)

/-- **Scope.** The fragment omits the term syntax of λ̂ (abstraction, `case` and `letrec`; the
rules (abs), (case) and (rec) are read on the defining rules of the recursor), datatypes other
than `Nat` and datatype parameters, coinductive types (Section 5), stage variables occurring
positively in the result type (`ı pos θ` of (rec), which types size-preserving functions such as
subtraction), calls of other defined symbols, and the saturated-set semantics with the strong
normalisation theorem (Proposition 3.36; ESTABLISHED). Formally: under the laws, every right side
typed in the sized judgment of the iterator lies below the left side `iter(b, s, S n)` in the
recursive path order with counter-first lexicographic status. -/
theorem sizedTypesAdmittance_scope :
    ∀ (A : TTy) (i : Nat) (Δ : TVar → SzTy), ¬ (Δ .b).hasVar i → ¬ (Δ .s).hasVar i →
      Δ .n = .snat (.var i) → ∀ (t : TTerm TVar) (σ : SzTy),
        SzHas (.iter A) i Δ t σ → RPO szPrec szStat (iterSuccL A) t :=
  fun _ _ _ hb hs hn _ _ h => h.toRPO_succ rfl hb hs hn

end OperatorKO7.Methods.OrientationClosure.MethodRowsTypedCalculi
