import Mathlib.Tactic

/-!
# Gödel's System T in de Bruijn form: the shared carrier of the higher-order boundary lanes

Relation: `Step` (full contextual one-step reduction: beta, the two recursor rules, congruences).
Closure: one step; `StepStar` is the reflexive-transitive closure.
Strategy: `stepLO` is the deterministic leftmost-outermost strategy (recursor argument first);
`Step` is the full relation and `stepLO` picks one of its steps.
Trust: definitions and `decide`-checked fixtures only; no axioms beyond the Lean baseline.
Scope: open and closed terms; simple types `SysTTy`; typing judgment `HasType`; inference `infer`;
the Church numeral family `church`, `churchApp`.

Every higher-order boundary lane imports this module: the type-cost boundary (L1), the indexed
license (L2), the light-types transport (L3), reducibility (L4), the meta-halt checker (L6).
Nothing here is a theorem about the boundary; the lanes prove those in their own modules.

Conventions. `shift d c t` raises every free variable of `t` at or above the cutoff `c` by `d`.
`subst j u t` replaces the variable `j` by `u` and lowers the free variables above `j` by one, so
`subst 0 u b` is the contractum of the redex `app (lam A b) u`.  Under a binder the substituted
term is shifted by one.  These are the textbook single-substitution equations (Pierce, TAPL 6.2)
and the ones the external Lean 4 Metatheory library (Ramos et al., arXiv 2512.09280) proves the
substitution lemmas for; the lanes prove the lemmas they need here.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingSystemT

/-- Simple types of System T: the base type `nat` and arrows. -/
inductive SysTTy : Type where
  | nat : SysTTy
  | arrow : SysTTy → SysTTy → SysTTy
  deriving DecidableEq, Repr

/-- Terms of System T with de Bruijn indices: variables, typed abstraction, application,
zero, successor, and the recursor `natrec z s n` with rules `natrec z s zero → z` and
`natrec z s (succ n) → app (app s n) (natrec z s n)`. -/
inductive SysTTerm : Type where
  | var : Nat → SysTTerm
  | lam : SysTTy → SysTTerm → SysTTerm
  | app : SysTTerm → SysTTerm → SysTTerm
  | zero : SysTTerm
  | succ : SysTTerm → SysTTerm
  | natrec : SysTTerm → SysTTerm → SysTTerm → SysTTerm
  deriving DecidableEq, Repr

/-- Raise every free variable at or above the cutoff `c` by `d`. -/
def shift (d c : Nat) : SysTTerm → SysTTerm
  | .var n => if n < c then .var n else .var (n + d)
  | .lam A b => .lam A (shift d (c + 1) b)
  | .app f a => .app (shift d c f) (shift d c a)
  | .zero => .zero
  | .succ t => .succ (shift d c t)
  | .natrec z s n => .natrec (shift d c z) (shift d c s) (shift d c n)

/-- Replace the variable `j` by `u`; free variables above `j` drop by one; under a binder the
substituted term is shifted by one. -/
def subst (j : Nat) (u : SysTTerm) : SysTTerm → SysTTerm
  | .var n => if n < j then .var n else if n = j then u else .var (n - 1)
  | .lam A b => .lam A (subst (j + 1) (shift 1 0 u) b)
  | .app f a => .app (subst j u f) (subst j u a)
  | .zero => .zero
  | .succ t => .succ (subst j u t)
  | .natrec z s n => .natrec (subst j u z) (subst j u s) (subst j u n)

/-- Full one-step reduction of System T.
Relation: `Step`. Closure: one step, closed under every constructor context.
Strategy: full (any redex). -/
inductive Step : SysTTerm → SysTTerm → Prop where
  | beta (A : SysTTy) (b u : SysTTerm) : Step (.app (.lam A b) u) (subst 0 u b)
  | recZero (z s : SysTTerm) : Step (.natrec z s .zero) z
  | recSucc (z s n : SysTTerm) :
      Step (.natrec z s (.succ n)) (.app (.app s n) (.natrec z s n))
  | appL {f f' : SysTTerm} (a : SysTTerm) : Step f f' → Step (.app f a) (.app f' a)
  | appR (f : SysTTerm) {a a' : SysTTerm} : Step a a' → Step (.app f a) (.app f a')
  | lam (A : SysTTy) {b b' : SysTTerm} : Step b b' → Step (.lam A b) (.lam A b')
  | succ {t t' : SysTTerm} : Step t t' → Step (.succ t) (.succ t')
  | recZ {z z' : SysTTerm} (s n : SysTTerm) : Step z z' → Step (.natrec z s n) (.natrec z' s n)
  | recS (z : SysTTerm) {s s' : SysTTerm} (n : SysTTerm) :
      Step s s' → Step (.natrec z s n) (.natrec z s' n)
  | recN (z s : SysTTerm) {n n' : SysTTerm} : Step n n' → Step (.natrec z s n) (.natrec z s n')

/-- Reflexive-transitive closure of `Step`. -/
abbrev StepStar : SysTTerm → SysTTerm → Prop := Relation.ReflTransGen Step

/-- A term with no `Step` successor. -/
def IsNormal (t : SysTTerm) : Prop := ∀ u, ¬ Step t u

/-- Leftmost-outermost one-step strategy: the root redex first; in an application the function
first; in a recursor the counter argument first, then the base, then the step.
Relation: a function whose graph lies inside `Step` (the lanes prove `stepLO_sound`).
Strategy: leftmost-outermost. -/
def stepLO : SysTTerm → Option SysTTerm
  | .app (.lam _ b) u => some (subst 0 u b)
  | .natrec z _ .zero => some z
  | .natrec z s (.succ n) => some (.app (.app s n) (.natrec z s n))
  | .app f a =>
      match stepLO f with
      | some f' => some (.app f' a)
      | none =>
        match stepLO a with
        | some a' => some (.app f a')
        | none => none
  | .lam A b => (stepLO b).map (.lam A)
  | .succ t => (stepLO t).map .succ
  | .natrec z s n =>
      match stepLO n with
      | some n' => some (.natrec z s n')
      | none =>
        match stepLO z with
        | some z' => some (.natrec z' s n)
        | none =>
          match stepLO s with
          | some s' => some (.natrec z s' n)
          | none => none
  | .var _ => none
  | .zero => none

/-- Fuelled leftmost-outermost normalizer: the normal form and the number of `stepLO` steps
taken, or `none` when the fuel runs out before a normal form is reached. -/
def normalizeFuel : Nat → SysTTerm → Option (SysTTerm × Nat)
  | 0, t =>
      match stepLO t with
      | none => some (t, 0)
      | some _ => none
  | fuel + 1, t =>
      match stepLO t with
      | none => some (t, 0)
      | some t' => (normalizeFuel fuel t').map (fun p => (p.1, p.2 + 1))

/-- The leftmost-outermost step count to normal form within `fuel` steps. -/
def betaCost (fuel : Nat) (t : SysTTerm) : Option Nat :=
  (normalizeFuel fuel t).map Prod.snd

/-- Simple typing of System T in a de Bruijn context (`Γ[n]?` is the type of variable `n`). -/
inductive HasType : List SysTTy → SysTTerm → SysTTy → Prop where
  | var {Γ : List SysTTy} {n : Nat} {A : SysTTy} : Γ[n]? = some A → HasType Γ (.var n) A
  | lam {Γ : List SysTTy} {A B : SysTTy} {b : SysTTerm} :
      HasType (A :: Γ) b B → HasType Γ (.lam A b) (.arrow A B)
  | app {Γ : List SysTTy} {A B : SysTTy} {f a : SysTTerm} :
      HasType Γ f (.arrow A B) → HasType Γ a A → HasType Γ (.app f a) B
  | zero {Γ : List SysTTy} : HasType Γ .zero .nat
  | succ {Γ : List SysTTy} {t : SysTTerm} : HasType Γ t .nat → HasType Γ (.succ t) .nat
  | natrec {Γ : List SysTTy} {A : SysTTy} {z s n : SysTTerm} :
      HasType Γ z A → HasType Γ s (.arrow .nat (.arrow A A)) → HasType Γ n .nat →
        HasType Γ (.natrec z s n) A

/-- Type inference: the cheap observer of the type-cost lane. The lanes prove `infer_sound`
(`infer Γ t = some A → HasType Γ t A`). -/
def infer (Γ : List SysTTy) : SysTTerm → Option SysTTy
  | .var n => Γ[n]?
  | .lam A b => (infer (A :: Γ) b).map (SysTTy.arrow A)
  | .app f a =>
      match infer Γ f, infer Γ a with
      | some (.arrow A B), some A' => if A = A' then some B else none
      | _, _ => none
  | .zero => some .nat
  | .succ t =>
      match infer Γ t with
      | some .nat => some .nat
      | _ => none
  | .natrec z s n =>
      match infer Γ z, infer Γ s, infer Γ n with
      | some A, some (.arrow .nat (.arrow A' A'')), some .nat =>
          if A = A' then (if A = A'' then some A else none) else none
      | _, _, _ => none

/-! ## The Church numeral family -/

/-- The body `f (f (... (f x)))` with `n` applications: `var 1` is `f`, `var 0` is `x`. -/
def churchBody : Nat → SysTTerm
  | 0 => .var 0
  | n + 1 => .app (.var 1) (churchBody n)

/-- The Church numeral `n` at type `(nat → nat) → nat → nat`. -/
def church (n : Nat) : SysTTerm :=
  .lam (.arrow .nat .nat) (.lam .nat (churchBody n))

/-- The successor function `λx. succ x`. -/
def succFn : SysTTerm := .lam .nat (.succ (.var 0))

/-- The numeral `n` as `succ^n zero`. -/
def natLit : Nat → SysTTerm
  | 0 => .zero
  | n + 1 => .succ (natLit n)

/-- The Church numeral `n` applied to the successor function and zero. Its normal form is
`natLit n`, its type is `nat` for every `n`, and its leftmost-outermost cost is `n + 2`. -/
def churchApp (n : Nat) : SysTTerm :=
  .app (.app (church n) succFn) .zero

/-! ## Fixtures (kernel-checked by `decide`) -/

theorem infer_churchApp_two : infer [] (churchApp 2) = some .nat := by decide

theorem infer_churchApp_five : infer [] (churchApp 5) = some .nat := by decide

theorem normalizeFuel_churchApp_two : normalizeFuel 100 (churchApp 2) = some (natLit 2, 4) := by
  decide

theorem normalizeFuel_churchApp_five : normalizeFuel 100 (churchApp 5) = some (natLit 5, 7) := by
  decide

theorem betaCost_churchApp_two_ne_five : betaCost 100 (churchApp 2) ≠ betaCost 100 (churchApp 5) := by
  decide

end OperatorKO7.HigherOrderRewritingSystemT
