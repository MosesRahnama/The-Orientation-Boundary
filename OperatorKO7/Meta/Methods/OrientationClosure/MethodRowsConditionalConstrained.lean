import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness
import OperatorKO7.Meta.Methods.OrientationClosure.ProcessorSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import Mathlib.Tactic

/-!
# Conditional and constrained method rows

Four rows of the method universe whose native language is conditional or constrained rewriting.

* `twoDDPForCTRS`: 2D dependency pairs (Lucas and Meseguer, WRLA 2014) on the conditional
  recursor, with the removal-triple processor of an argument filtering and an `ℕ`-algebra.
* `operationalTerminationCTRS`: operational termination (Lucas, Marché and Meseguer, IPL 2005)
  through the unraveling `U(R)` (Ohlebusch 2002, Definition 7.2.48), whose termination is proved
  by a dependency-pair reduction pair.
* `integerTermRewriting`: integer term rewriting (Fuhs, Giesl, Plücker, Schneider-Kamp and Falke,
  RTA 2009) on the integer recursor, with the conditional reduction pair processor.
* `lctrs`: logically constrained rewriting (Kop and Nishida, FroCoS 2013) with the value criterion
  of the constrained dependency-pair framework (Kop, WST 2013).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics

universe u v

/-! ## Argument lists under an arbitrary step relation -/

section ArgLists

variable {α : Type u}

/-- Two argument lists related by one `S` step at one position. -/
def ArgStepOf (S : α → α → Prop) (xs ys : List α) : Prop :=
  ∃ pre post : List α, ∃ a b : α, xs = pre ++ a :: post ∧ ys = pre ++ b :: post ∧ S a b

theorem not_argStepOf_nil {S : α → α → Prop} (ys : List α) : ¬ ArgStepOf S [] ys := by
  rintro ⟨pre, post, a, b, h, -, -⟩
  cases pre <;> simp at h

theorem argStepOf_cons_iff {S : α → α → Prop} (a : α) (rest ys : List α) :
    ArgStepOf S (a :: rest) ys ↔
      (∃ b, S a b ∧ ys = b :: rest) ∨ (∃ rest', ArgStepOf S rest rest' ∧ ys = a :: rest') := by
  constructor
  · rintro ⟨pre, post, x, y, hxs, hys, hst⟩
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs hys
      obtain ⟨rfl, rfl⟩ := hxs
      exact Or.inl ⟨y, hst, hys⟩
    | cons p pre' =>
      simp only [List.cons_append, List.cons.injEq] at hxs hys
      obtain ⟨rfl, rfl⟩ := hxs
      exact Or.inr ⟨pre' ++ y :: post, ⟨pre', post, x, y, rfl, rfl, hst⟩, hys⟩
  · rintro (⟨b, hab, rfl⟩ | ⟨rest', ⟨pre, post, x, y, rfl, rfl, hst⟩, rfl⟩)
    · exact ⟨[], rest, a, b, rfl, rfl, hab⟩
    · exact ⟨a :: pre, post, x, y, rfl, rfl, hst⟩

theorem accOf_cons {S : α → α → Prop} :
    ∀ a : α, Acc (fun b a => S a b) a → ∀ rest : List α,
      Acc (fun ys xs => ArgStepOf S xs ys) rest →
        Acc (fun ys xs => ArgStepOf S xs ys) (a :: rest) := by
  intro a ha
  induction ha with
  | intro a _ iha =>
    intro rest hr
    induction hr with
    | intro rest hr' ihr =>
      refine Acc.intro _ fun ys hys => ?_
      rcases (argStepOf_cons_iff a rest ys).1 hys with ⟨b, hab, rfl⟩ | ⟨rest', hrr, rfl⟩
      · exact iha b hab rest (Acc.intro rest hr')
      · exact ihr rest' hrr

/-- Accessible elements make argument rewriting accessible. -/
theorem accArgsOf {S : α → α → Prop} :
    ∀ args : List α, (∀ a ∈ args, Acc (fun b a => S a b) a) →
      Acc (fun ys xs => ArgStepOf S xs ys) args
  | [], _ => Acc.intro _ fun ys h => absurd h (not_argStepOf_nil ys)
  | a :: rest, h =>
    accOf_cons a (h a List.mem_cons_self) rest
      (accArgsOf rest fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem argStepOf_preserve {S : α → α → Prop} {P : α → Prop} (hP : ∀ a b, P a → S a b → P b)
    {xs ys : List α} (hxs : ∀ a ∈ xs, P a) (h : ArgStepOf S xs ys) : ∀ b ∈ ys, P b := by
  obtain ⟨pre, post, a, b, rfl, rfl, hab⟩ := h
  intro c hc
  simp only [List.mem_append, List.mem_cons] at hc
  rcases hc with hc | rfl | hc
  · exact hxs c (by simp [hc])
  · exact hP a c (hxs a (by simp)) hab
  · exact hxs c (by simp [hc])

theorem argStepsOf_preserve {S : α → α → Prop} {P : α → Prop} (hP : ∀ a b, P a → S a b → P b)
    {xs ys : List α} (h : Relation.ReflTransGen (ArgStepOf S) xs ys) (hxs : ∀ a ∈ xs, P a) :
    ∀ b ∈ ys, P b := by
  induction h with
  | refl => exact hxs
  | tail _ hst ih => exact argStepOf_preserve hP ih hst

/-- Pointwise comparison of two lists that differ at one position. -/
theorem forall₂_of_mid {r : α → α → Prop} (hr : ∀ x, r x x) {a b : α} (hab : r a b) :
    ∀ pre post : List α, List.Forall₂ r (pre ++ a :: post) (pre ++ b :: post)
  | [], post => by
    refine List.Forall₂.cons hab ?_
    induction post with
    | nil => exact List.Forall₂.nil
    | cons c cs ih => exact List.Forall₂.cons (hr c) ih
  | c :: pre, post => List.Forall₂.cons (hr c) (forall₂_of_mid hr hab pre post)

theorem forall₂_refl {r : α → α → Prop} (hr : ∀ x, r x x) : ∀ xs : List α, List.Forall₂ r xs xs
  | [] => List.Forall₂.nil
  | x :: xs => List.Forall₂.cons (hr x) (forall₂_refl hr xs)

theorem forall₂_trans {r : α → α → Prop} (hr : ∀ x y z, r x y → r y z → r x z) :
    ∀ {xs ys zs : List α}, List.Forall₂ r xs ys → List.Forall₂ r ys zs → List.Forall₂ r xs zs
  | [], [], [], _, _ => List.Forall₂.nil
  | _ :: _, _ :: _, _ :: _, List.Forall₂.cons h₁ t₁, List.Forall₂.cons h₂ t₂ =>
    List.Forall₂.cons (hr _ _ _ h₁ h₂) (forall₂_trans hr t₁ t₂)

theorem forall₂_getElem? {r : α → α → Prop} :
    ∀ {xs ys : List α}, List.Forall₂ r xs ys → ∀ i : Nat,
      (xs[i]? = none ∧ ys[i]? = none) ∨ ∃ x y, xs[i]? = some x ∧ ys[i]? = some y ∧ r x y
  | [], [], List.Forall₂.nil, _ => Or.inl ⟨rfl, rfl⟩
  | x :: _, y :: _, List.Forall₂.cons h _, 0 => Or.inr ⟨x, y, rfl, rfl, h⟩
  | _ :: _, _ :: _, List.Forall₂.cons _ t, i + 1 => by
    simpa using forall₂_getElem? t i

/-- The values at the kept positions, in the order of `keep`. -/
def filterVals (keep : List Nat) (vs : List α) : List α := keep.filterMap fun i => vs[i]?

theorem forall₂_filterVals {r : α → α → Prop} {vs ws : List α} (h : List.Forall₂ r vs ws) :
    ∀ keep : List Nat, List.Forall₂ r (filterVals keep vs) (filterVals keep ws)
  | [] => List.Forall₂.nil
  | i :: keep => by
    have ih := forall₂_filterVals h keep
    unfold filterVals at ih ⊢
    rcases forall₂_getElem? h i with ⟨h1, h2⟩ | ⟨x, y, h1, h2, hxy⟩
    · simp only [List.filterMap_cons, h1, h2]
      exact ih
    · simp only [List.filterMap_cons, h1, h2]
      exact List.Forall₂.cons hxy ih

end ArgLists

/-! ## Term evaluation in an algebra over `ℕ` -/

section Algebra

variable {sigma : Type u} {nu : Type v}

mutual
/-- Evaluation of a term in the algebra `A` under the variable valuation `α`. -/
def evalT (A : sigma → List Nat → Nat) (α : nu → Nat) : Term sigma nu → Nat
  | .var x => α x
  | .app f args => A f (evalL A α args)
/-- Evaluation of an argument list. -/
def evalL (A : sigma → List Nat → Nat) (α : nu → Nat) : List (Term sigma nu) → List Nat
  | [] => []
  | a :: as => evalT A α a :: evalL A α as
end

theorem evalL_eq_map (A : sigma → List Nat → Nat) (α : nu → Nat) :
    ∀ args : List (Term sigma nu), evalL A α args = args.map (evalT A α)
  | [] => rfl
  | a :: as => by simp [evalL, evalL_eq_map A α as]

@[simp] theorem evalT_var (A : sigma → List Nat → Nat) (α : nu → Nat) (x : nu) :
    evalT A α (.var x : Term sigma nu) = α x := rfl

theorem evalT_app (A : sigma → List Nat → Nat) (α : nu → Nat) (f : sigma)
    (args : List (Term sigma nu)) : evalT A α (.app f args) = A f (args.map (evalT A α)) := by
  simp [evalT, evalL_eq_map]

/-- Evaluation of a substitution instance. -/
theorem evalT_subst (A : sigma → List Nat → Nat) (α : nu → Nat) (σ : Subst sigma nu) :
    ∀ t : Term sigma nu, evalT A α (Subst.apply σ t) = evalT A (fun x => evalT A α (σ x)) t := by
  intro t
  induction t using Term.rec' with
  | hvar x => simp
  | happ f args ih =>
    rw [Subst.apply_app, evalT_app, evalT_app, Subst.applyList_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left fun a ha => ih a ha

theorem evalL_subst (A : sigma → List Nat → Nat) (α : nu → Nat) (σ : Subst sigma nu)
    (args : List (Term sigma nu)) :
    (Subst.applyList σ args).map (evalT A α) = args.map (evalT A (fun x => evalT A α (σ x))) := by
  rw [Subst.applyList_eq_map, List.map_map]
  exact List.map_congr_left fun a _ => evalT_subst A α σ a

/-- Weak monotonicity of every interpretation function. -/
def AlgMono (A : sigma → List Nat → Nat) : Prop :=
  ∀ f xs ys, List.Forall₂ (· ≤ ·) xs ys → A f xs ≤ A f ys

theorem forall₂_map_le {A : sigma → List Nat → Nat} {α : nu → Nat} {a b : Term sigma nu}
    (h : evalT A α b ≤ evalT A α a) (pre post : List (Term sigma nu)) :
    List.Forall₂ (· ≤ ·) ((pre ++ b :: post).map (evalT A α)) ((pre ++ a :: post).map (evalT A α)) := by
  simpa using forall₂_of_mid (r := (· ≤ ·)) (fun x => le_refl x) h (pre.map (evalT A α))
    (post.map (evalT A α))

end Algebra

/-! ## Context closures of root relations and their dependency pairs -/

section CtxClosure

variable {sigma : Type u} {nu : Type v}

/-- The context closure of a root relation: a root contraction or a step inside one argument. -/
inductive CtxStep (Root : Term sigma nu → Term sigma nu → Prop) :
    Term sigma nu → Term sigma nu → Prop
  | root {s t : Term sigma nu} : Root s t → CtxStep Root s t
  | arg (f : sigma) (pre post : List (Term sigma nu)) {a b : Term sigma nu} :
      CtxStep Root a b → CtxStep Root (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

/-- Strong normalization for the context closure of `Root`. -/
def RSN (Root : Term sigma nu → Term sigma nu → Prop) (t : Term sigma nu) : Prop :=
  Acc (fun u t => CtxStep Root t u) t

theorem ctxStep_app_iff (Root : Term sigma nu → Term sigma nu → Prop) (f : sigma)
    (args : List (Term sigma nu)) (u : Term sigma nu) :
    CtxStep Root (.app f args) u ↔
      Root (.app f args) u ∨ ∃ args', ArgStepOf (CtxStep Root) args args' ∧ u = .app f args' := by
  constructor
  · intro h
    cases h with
    | root h => exact Or.inl h
    | arg g pre post hab => exact Or.inr ⟨_, ⟨pre, post, _, _, rfl, rfl, hab⟩, rfl⟩
  · rintro (h | ⟨args', ⟨pre, post, a, b, rfl, rfl, hab⟩, rfl⟩)
    · exact CtxStep.root h
    · exact CtxStep.arg f pre post hab

theorem ctxStep_var_iff (Root : Term sigma nu → Term sigma nu → Prop) (x : nu)
    (u : Term sigma nu) : CtxStep Root (.var x) u ↔ Root (.var x) u := by
  constructor
  · intro h
    cases h with
    | root h => exact h
  · exact CtxStep.root

/-- Arguments of a strongly normalizing application are strongly normalizing. -/
theorem rsn_arg {Root : Term sigma nu → Term sigma nu → Prop} {f : sigma}
    {args : List (Term sigma nu)} (h : RSN Root (.app f args)) {a : Term sigma nu}
    (ha : a ∈ args) : RSN Root a := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
  have key : ∀ t, RSN Root t → ∀ (pre post : List (Term sigma nu)) (a : Term sigma nu),
      t = .app f (pre ++ a :: post) → RSN Root a := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro pre post a heq
      refine Acc.intro _ fun b hab => ?_
      exact ih _ (by rw [heq]; exact CtxStep.arg f pre post hab) pre post b rfl
  exact key _ h pre post a rfl

theorem rsn_of_isSubterm {Root : Term sigma nu → Term sigma nu → Prop} {w t : Term sigma nu}
    (h : IsSubterm w t) (ht : RSN Root t) : RSN Root w := by
  induction h with
  | refl => exact ht
  | arg f args hmem _ ih => exact ih (rsn_arg ht hmem)

/-- An application whose root contractions lead to strongly normalizing terms is strongly
normalizing when its arguments are. -/
theorem rsn_app_of_root {Root : Term sigma nu → Term sigma nu → Prop} {f : sigma}
    (hroot : ∀ xs u, (∀ a ∈ xs, RSN Root a) → Root (.app f xs) u → RSN Root u) :
    ∀ args : List (Term sigma nu), (∀ a ∈ args, RSN Root a) → RSN Root (.app f args) := by
  intro args hargs
  have hacc := accArgsOf (S := CtxStep Root) args hargs
  induction hacc with
  | intro xs _ ih =>
    refine Acc.intro _ fun u hu => ?_
    rcases (ctxStep_app_iff Root f xs u).1 hu with hr | ⟨ys, hys, rfl⟩
    · exact hroot xs u hargs hr
    · exact ih ys hys (argStepOf_preserve (fun a b ha hab => Acc.inv ha hab) hargs hys)

/-- The minimal chain relation of `Root` for a pair relation on calls: argument rewriting from
the call `c`, then one pair edge to `d`; both ends have strongly normalizing arguments. -/
def MinChainOf (Root : Term sigma nu → Term sigma nu → Prop)
    (Pair : Call sigma nu → Call sigma nu → Prop) (c d : Call sigma nu) : Prop :=
  (∀ a ∈ c.2, RSN Root a) ∧ (∀ a ∈ d.2, RSN Root a) ∧
    ∃ xs, Relation.ReflTransGen (ArgStepOf (CtxStep Root)) c.2 xs ∧ Pair (c.1, xs) d

theorem rsn_of_minChainOf_acc (Root : Term sigma nu → Term sigma nu → Prop)
    (Pair : Call sigma nu → Call sigma nu → Prop)
    (hroot : ∀ (f : sigma) (xs : List (Term sigma nu)) (u : Term sigma nu), Root (.app f xs) u →
      (∀ a ∈ xs, RSN Root a) →
      (∀ d : Call sigma nu, Pair (f, xs) d → (∀ a ∈ d.2, RSN Root a) → RSN Root (.app d.1 d.2)) →
      RSN Root u) :
    ∀ c : Call sigma nu, Acc (fun d c => MinChainOf Root Pair c d) c →
      (∀ a ∈ c.2, RSN Root a) → ∀ xs, Relation.ReflTransGen (ArgStepOf (CtxStep Root)) c.2 xs →
        (∀ a ∈ xs, RSN Root a) → RSN Root (.app c.1 xs) := by
  intro c hc
  induction hc with
  | intro c _ ihc =>
    intro hcSN xs hreach hxs
    have hacc := accArgsOf (S := CtxStep Root) xs hxs
    induction hacc with
    | intro xs _ ihx =>
      refine Acc.intro _ fun u hu => ?_
      rcases (ctxStep_app_iff Root c.1 xs u).1 hu with hr | ⟨ys, hys, rfl⟩
      · exact hroot c.1 xs u hr hxs fun d hd hdSN =>
          ihc d ⟨hcSN, hdSN, xs, hreach, hd⟩ hdSN d.2 .refl hdSN
      · exact ihx ys hys (hreach.tail hys)
          (argStepOf_preserve (fun a b ha hab => Acc.inv ha hab) hxs hys)

/-- Dependency-pair soundness for the context closure of a root relation: if the root analysis
reduces strong normalization of every contractum to strong normalization of its calls, a
well-founded minimal chain relation gives termination. -/
theorem rsn_of_minChainOf_wf (Root : Term sigma nu → Term sigma nu → Prop)
    (Pair : Call sigma nu → Call sigma nu → Prop)
    (hvar : ∀ (x : nu) (u : Term sigma nu), ¬ Root (.var x) u)
    (hroot : ∀ (f : sigma) (xs : List (Term sigma nu)) (u : Term sigma nu), Root (.app f xs) u →
      (∀ a ∈ xs, RSN Root a) →
      (∀ d : Call sigma nu, Pair (f, xs) d → (∀ a ∈ d.2, RSN Root a) → RSN Root (.app d.1 d.2)) →
      RSN Root u)
    (hwf : WellFounded (fun d c => MinChainOf Root Pair c d)) : ∀ t, RSN Root t := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
    exact Acc.intro _ fun u hu => absurd ((ctxStep_var_iff Root x u).1 hu) (hvar x u)
  | happ f args ih =>
    exact rsn_of_minChainOf_acc Root Pair hroot (f, args) (hwf.apply _) ih args .refl ih

end CtxClosure

/-! ## Conditional rewriting as an inference system -/

section Conditional

variable {sigma : Type u} {nu : Type v}

/-- A conditional rewrite rule `ℓ → r ⇐ s₁ → t₁, …, sₙ → tₙ` with oriented reachability
conditions (Lucas and Meseguer 2014, Section 2). -/
structure CRule (sigma : Type u) (nu : Type v) where
  lhs : Term sigma nu
  rhs : Term sigma nu
  conds : List (Term sigma nu × Term sigma nu)
  lhs_isApp : lhs.isApp = true

/-- A conditional term rewriting system. -/
abbrev CTRS (sigma : Type u) (nu : Type v) := List (CRule sigma nu)

theorem crule_lhs_eq_app (ρ : CRule sigma nu) : ∃ g largs, ρ.lhs = .app g largs := by
  have h := ρ.lhs_isApp
  cases hl : ρ.lhs with
  | var x =>
    rw [hl] at h
    simp at h
  | app g largs => exact ⟨g, largs, rfl⟩

/-- The two judgments of conditional rewriting: one step `s → t` and many steps `s →* t`. -/
inductive Judg (sigma : Type u) (nu : Type v) where
  | step (s t : Term sigma nu)
  | steps (s t : Term sigma nu)

/-- The instantiated conditions of a rule, as `→*` goals in order. -/
def condGoals (σ : Subst sigma nu) (cs : List (Term sigma nu × Term sigma nu)) :
    List (Judg sigma nu) :=
  cs.map fun c => .steps (Subst.apply σ c.1) (Subst.apply σ c.2)

/-- The inference rules of conditional rewriting (Lucas and Meseguer 2014, Figure 1):
`Refl`, `Tran`, `Cong` and `Repl`. `Infer R j ps` says that `j` follows from the premises `ps`. -/
inductive Infer (R : CTRS sigma nu) : Judg sigma nu → List (Judg sigma nu) → Prop
  | refl (t : Term sigma nu) : Infer R (.steps t t) []
  | tran (s t w : Term sigma nu) : Infer R (.steps s w) [.step s t, .steps t w]
  | cong (f : sigma) (pre post : List (Term sigma nu)) (a b : Term sigma nu) :
      Infer R (.step (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))) [.step a b]
  | repl {ρ : CRule sigma nu} (hρ : ρ ∈ R) (σ : Subst sigma nu) :
      Infer R (.step (Subst.apply σ ρ.lhs) (Subst.apply σ ρ.rhs)) (condGoals σ ρ.conds)

/-- A judgment with a closed proof tree. -/
inductive Derivable (R : CTRS sigma nu) : Judg sigma nu → Prop
  | intro {j : Judg sigma nu} {ps : List (Judg sigma nu)} :
      Infer R j ps → (∀ p ∈ ps, Derivable R p) → Derivable R j

/-- The conditional rewrite relation: `s →_R t` has a closed proof tree. -/
def CStep (R : CTRS sigma nu) (s t : Term sigma nu) : Prop := Derivable R (.step s t)

/-- The reachability relation `s →*_R t` of conditional rewriting. -/
def CSteps (R : CTRS sigma nu) (s t : Term sigma nu) : Prop := Derivable R (.steps s t)

/-- The instantiated conditions hold. -/
def CondsHold (R : CTRS sigma nu) (σ : Subst sigma nu)
    (cs : List (Term sigma nu × Term sigma nu)) : Prop :=
  ∀ c ∈ cs, CSteps R (Subst.apply σ c.1) (Subst.apply σ c.2)

theorem derivable_inv {R : CTRS sigma nu} {j : Judg sigma nu} (h : Derivable R j) :
    ∃ ps, Infer R j ps ∧ ∀ p ∈ ps, Derivable R p := by
  cases h with
  | intro hi hps => exact ⟨_, hi, hps⟩

theorem infer_step_inv {R : CTRS sigma nu} {s w : Term sigma nu} {ps : List (Judg sigma nu)}
    (h : Infer R (.step s w) ps) :
    (∃ f pre post a b, s = .app f (pre ++ a :: post) ∧ w = .app f (pre ++ b :: post) ∧
        ps = [.step a b]) ∨
      (∃ ρ ∈ R, ∃ σ : Subst sigma nu, s = Subst.apply σ ρ.lhs ∧ w = Subst.apply σ ρ.rhs ∧
        ps = condGoals σ ρ.conds) := by
  cases h with
  | cong f pre post a b => exact Or.inl ⟨f, pre, post, a, b, rfl, rfl, rfl⟩
  | repl hρ σ => exact Or.inr ⟨_, hρ, σ, rfl, rfl, rfl⟩

theorem infer_steps_inv {R : CTRS sigma nu} {s w : Term sigma nu} {ps : List (Judg sigma nu)}
    (h : Infer R (.steps s w) ps) :
    (s = w ∧ ps = []) ∨ ∃ t, ps = [.step s t, .steps t w] := by
  cases h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | tran _ t _ => exact Or.inr ⟨t, rfl⟩

theorem cstep_inv {R : CTRS sigma nu} {s t : Term sigma nu} (h : CStep R s t) :
    (∃ f pre post a b, s = .app f (pre ++ a :: post) ∧ t = .app f (pre ++ b :: post) ∧
        CStep R a b) ∨
      (∃ ρ ∈ R, ∃ σ : Subst sigma nu, s = Subst.apply σ ρ.lhs ∧ t = Subst.apply σ ρ.rhs ∧
        CondsHold R σ ρ.conds) := by
  obtain ⟨ps, hi, hps⟩ := derivable_inv h
  rcases infer_step_inv hi with ⟨f, pre, post, a, b, rfl, rfl, rfl⟩ | ⟨ρ, hρ, σ, rfl, rfl, rfl⟩
  · exact Or.inl ⟨f, pre, post, a, b, rfl, rfl, hps _ (by simp)⟩
  · exact Or.inr ⟨ρ, hρ, σ, rfl, rfl, fun c hc => hps _ (List.mem_map_of_mem hc)⟩

theorem cstep_cong {R : CTRS sigma nu} (f : sigma) (pre post : List (Term sigma nu))
    {a b : Term sigma nu} (h : CStep R a b) :
    CStep R (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)) :=
  Derivable.intro (Infer.cong f pre post a b) (by simpa using h)

theorem cstep_repl {R : CTRS sigma nu} {ρ : CRule sigma nu} (hρ : ρ ∈ R) (σ : Subst sigma nu)
    (h : CondsHold R σ ρ.conds) :
    CStep R (Subst.apply σ ρ.lhs) (Subst.apply σ ρ.rhs) :=
  Derivable.intro (Infer.repl hρ σ) (by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
    exact h c hc)

theorem csteps_refl (R : CTRS sigma nu) (t : Term sigma nu) : CSteps R t t :=
  Derivable.intro (Infer.refl t) (by simp)

theorem csteps_head {R : CTRS sigma nu} {s t w : Term sigma nu} (h₁ : CStep R s t)
    (h₂ : CSteps R t w) : CSteps R s w :=
  Derivable.intro (Infer.tran s t w) (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    exacts [h₁, h₂])

theorem csteps_of_rtg {R : CTRS sigma nu} {s t : Term sigma nu}
    (h : Relation.ReflTransGen (CStep R) s t) : CSteps R s t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact csteps_refl R _
  | head hst _ ih => exact csteps_head hst ih

theorem derivable_steps_rtg {R : CTRS sigma nu} :
    ∀ {j : Judg sigma nu}, Derivable R j →
      match j with
      | .steps s t => Relation.ReflTransGen (CStep R) s t
      | .step _ _ => True := by
  intro j h
  induction h with
  | intro hi hps ih =>
    cases hi with
    | refl => exact .refl
    | tran s t w =>
      have h1 : CStep R s t := hps (.step s t) (by simp)
      have h2 : Relation.ReflTransGen (CStep R) t w := ih (.steps t w) (by simp)
      exact Relation.ReflTransGen.head h1 h2
    | cong => trivial
    | repl => trivial

theorem csteps_iff_rtg {R : CTRS sigma nu} {s t : Term sigma nu} :
    CSteps R s t ↔ Relation.ReflTransGen (CStep R) s t :=
  ⟨fun h => derivable_steps_rtg h, csteps_of_rtg⟩

theorem csteps_trans {R : CTRS sigma nu} {s t w : Term sigma nu} (h₁ : CSteps R s t)
    (h₂ : CSteps R t w) : CSteps R s w :=
  csteps_of_rtg ((csteps_iff_rtg.1 h₁).trans (csteps_iff_rtg.1 h₂))

theorem csteps_of_cstep {R : CTRS sigma nu} {s t : Term sigma nu} (h : CStep R s t) :
    CSteps R s t :=
  csteps_head h (csteps_refl R t)

theorem csteps_cong {R : CTRS sigma nu} (f : sigma) (pre post : List (Term sigma nu))
    {a b : Term sigma nu} (h : CSteps R a b) :
    CSteps R (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)) :=
  csteps_of_rtg (Relation.ReflTransGen.lift (fun x => Term.app f (pre ++ x :: post))
    (fun _ _ hxy => cstep_cong f pre post hxy) (csteps_iff_rtg.1 h))

/-! ### Proof search: goal stacks and partial proof trees -/

/-- Expanding the active (leftmost) open goal by an inference-rule instance replaces it by the
premises of that instance. A goal stack is the list of open goals of a well-formed partial proof
tree, from left to right. -/
inductive Expand (R : CTRS sigma nu) : List (Judg sigma nu) → List (Judg sigma nu) → Prop
  | mk {j : Judg sigma nu} {ps : List (Judg sigma nu)} (rest : List (Judg sigma nu)) :
      Infer R j ps → Expand R (j :: rest) (ps ++ rest)

/-- Every expansion sequence from the goal stack is finite. -/
def Good (R : CTRS sigma nu) (gs : List (Judg sigma nu)) : Prop :=
  Acc (fun b a => Expand R a b) gs

/-- Every proof attempt for the goal is finite. -/
def LFin (R : CTRS sigma nu) (j : Judg sigma nu) : Prop := Good R [j]

theorem good_nil (R : CTRS sigma nu) : Good R [] :=
  Acc.intro _ fun _ h => by cases h

theorem expand_append {R : CTRS sigma nu} {X Y : List (Judg sigma nu)} (h : Expand R X Y)
    (rest : List (Judg sigma nu)) : Expand R (X ++ rest) (Y ++ rest) := by
  cases h with
  | mk rest' hi => simpa [List.append_assoc] using Expand.mk (rest' ++ rest) hi

theorem good_of_append {R : CTRS sigma nu} {rest : List (Judg sigma nu)} :
    ∀ Z, Good R Z → ∀ X, Z = X ++ rest → Good R X := by
  intro Z hZ
  induction hZ with
  | intro Z _ ih =>
    intro X hX
    subst hX
    exact Acc.intro _ fun Y hY => ih (Y ++ rest) (expand_append hY rest) Y rfl

theorem lfin_of_good_cons {R : CTRS sigma nu} {j : Judg sigma nu} {rest : List (Judg sigma nu)}
    (h : Good R (j :: rest)) : LFin R j :=
  good_of_append (j :: rest) h [j] rfl

theorem good_of_rtg {R : CTRS sigma nu} {X Y : List (Judg sigma nu)}
    (h : Relation.ReflTransGen (Expand R) X Y) (hX : Good R X) : Good R Y := by
  induction h with
  | refl => exact hX
  | tail _ hst ih => exact Acc.inv ih hst

theorem reach_append {R : CTRS sigma nu} :
    ∀ ps : List (Judg sigma nu),
      (∀ p ∈ ps, ∀ rest, Relation.ReflTransGen (Expand R) (p :: rest) rest) →
        ∀ rest, Relation.ReflTransGen (Expand R) (ps ++ rest) rest
  | [], _, _ => .refl
  | p :: ps, h, rest =>
    (h p List.mem_cons_self (ps ++ rest)).trans
      (reach_append ps (fun q hq => h q (List.mem_cons_of_mem _ hq)) rest)

/-- A closed proof tree closes its goal on every stack. -/
theorem derivable_reach {R : CTRS sigma nu} :
    ∀ {j : Judg sigma nu}, Derivable R j →
      ∀ rest, Relation.ReflTransGen (Expand R) (j :: rest) rest := by
  intro j h
  induction h with
  | intro hi _ ih =>
    intro rest
    exact Relation.ReflTransGen.head (Expand.mk rest hi) (reach_append _ ih rest)

/-- A goal stack that is emptied consists of derivable goals. -/
theorem derivable_of_reach_nil {R : CTRS sigma nu} {X : List (Judg sigma nu)}
    (h : Relation.ReflTransGen (Expand R) X []) : ∀ j ∈ X, Derivable R j := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro j hj; simp at hj
  | head hstep _ ih =>
    cases hstep with
    | mk rest hi =>
      intro j' hj'
      simp only [List.mem_cons] at hj'
      rcases hj' with rfl | hj'
      · exact Derivable.intro hi fun p hp => ih p (List.mem_append_left _ hp)
      · exact ih j' (List.mem_append_right _ hj')

theorem good_append_of {R : CTRS sigma nu} :
    ∀ X, Good R X → ∀ rest, (Relation.ReflTransGen (Expand R) X [] → Good R rest) →
      Good R (X ++ rest) := by
  intro X hX
  induction hX with
  | intro X _ ih =>
    intro rest hrest
    cases X with
    | nil => exact hrest .refl
    | cons j X' =>
      refine Acc.intro _ fun Y hY => ?_
      rw [List.cons_append] at hY
      cases hY with
      | mk _ hi =>
        have hstep : Expand R (j :: X') (_ ++ X') := Expand.mk X' hi
        have := ih _ hstep rest fun h => hrest (.head hstep h)
        simpa [List.append_assoc] using this

theorem good_cons_of_lfin {R : CTRS sigma nu} {j : Judg sigma nu} {rest : List (Judg sigma nu)}
    (hj : LFin R j) (hrest : Derivable R j → Good R rest) : Good R (j :: rest) :=
  good_append_of [j] hj rest fun h => hrest (derivable_of_reach_nil h j (by simp))

/-- Goals attempted from left to right: each goal is finite, and the rest is finite once it is
proved. -/
def GoodSeq (R : CTRS sigma nu) : List (Judg sigma nu) → Prop
  | [] => True
  | p :: ps => LFin R p ∧ (Derivable R p → GoodSeq R ps)

theorem good_of_goodSeq {R : CTRS sigma nu} : ∀ ps : List (Judg sigma nu), GoodSeq R ps → Good R ps
  | [], _ => good_nil R
  | _ :: ps, ⟨hp, hps⟩ => good_cons_of_lfin hp fun hd => good_of_goodSeq ps (hps hd)

theorem lfin_iff {R : CTRS sigma nu} {j : Judg sigma nu} :
    LFin R j ↔ ∀ ps, Infer R j ps → Good R ps := by
  constructor
  · intro h ps hi
    have := Acc.inv h (Expand.mk [] hi)
    simpa using this
  · intro h
    refine Acc.intro _ fun Y hY => ?_
    cases hY with
    | mk rest hi => simpa using h _ hi

theorem goodSeq_condGoals {R : CTRS sigma nu} (σ : Subst sigma nu) :
    ∀ cs : List (Term sigma nu × Term sigma nu),
      (∀ pre s t post, cs = pre ++ (s, t) :: post → CondsHold R σ pre →
        LFin R (.steps (Subst.apply σ s) (Subst.apply σ t))) →
      GoodSeq R (condGoals σ cs)
  | [], _ => trivial
  | (s, t) :: cs, h => by
    simp only [condGoals, List.map_cons, GoodSeq]
    refine ⟨h [] s t cs rfl (by simp [CondsHold]), fun hd => ?_⟩
    refine goodSeq_condGoals σ cs fun pre s' t' post hcs hpre => ?_
    refine h ((s, t) :: pre) s' t' post (by simp [hcs]) ?_
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    exacts [hd, hpre c hc]

/-- A partial proof tree: an open goal, or a judgment with the subtrees of its premises. -/
inductive PTree (sigma : Type u) (nu : Type v) where
  | goal (j : Judg sigma nu)
  | node (j : Judg sigma nu) (ts : List (PTree sigma nu))

mutual
/-- The open goals of a partial proof tree, from left to right. -/
def PTree.frontier : PTree sigma nu → List (Judg sigma nu)
  | .goal j => [j]
  | .node _ ts => PTree.frontierList ts
/-- The open goals of a list of trees. -/
def PTree.frontierList : List (PTree sigma nu) → List (Judg sigma nu)
  | [] => []
  | t :: ts => PTree.frontier t ++ PTree.frontierList ts
end

/-- Induction on partial proof trees with a hypothesis for every subtree. -/
@[elab_as_elim]
def PTree.rec' {motive : PTree sigma nu → Prop}
    (hgoal : ∀ j, motive (.goal j))
    (hnode : ∀ j ts, (∀ t ∈ ts, motive t) → motive (.node j ts)) : ∀ t, motive t
  | .goal j => hgoal j
  | .node j ts => hnode j ts (fun t ht =>
      have _hmem : t ∈ ts := ht
      PTree.rec' hgoal hnode t)
  termination_by t => sizeOf t
  decreasing_by
    · exact List.sizeOf_lt_of_mem ht |>.trans_le (by
        simp only [PTree.node.sizeOf_spec]; omega)

/-- Expansion of the leftmost open goal of a partial proof tree: the goal becomes a node whose
subtrees are the open premises of an inference-rule instance. The subtrees to the left of the
expanded one are closed (they have no open goal); this is the expansion that keeps a tree well
formed in the sense of Lucas and Meseguer (2014, Section 2). -/
inductive TExpand (R : CTRS sigma nu) : PTree sigma nu → PTree sigma nu → Prop
  | leaf {j : Judg sigma nu} {ps : List (Judg sigma nu)} : Infer R j ps →
      TExpand R (.goal j) (.node j (ps.map PTree.goal))
  | inner (j : Judg sigma nu) (pre post : List (PTree sigma nu)) {t t' : PTree sigma nu} :
      (∀ c ∈ pre, PTree.frontier c = []) → TExpand R t t' →
        TExpand R (.node j (pre ++ t :: post)) (.node j (pre ++ t' :: post))

theorem frontierList_append :
    ∀ xs ys : List (PTree sigma nu),
      PTree.frontierList (xs ++ ys) = PTree.frontierList xs ++ PTree.frontierList ys
  | [], _ => rfl
  | x :: xs, ys => by
    simp only [List.cons_append, PTree.frontierList, frontierList_append xs ys, List.append_assoc]

theorem frontierList_map_goal :
    ∀ ps : List (Judg sigma nu), PTree.frontierList (ps.map PTree.goal) = ps
  | [] => rfl
  | p :: ps => by
    simp only [List.map_cons, PTree.frontierList, PTree.frontier, frontierList_map_goal ps,
      List.singleton_append]

theorem frontierList_eq_nil :
    ∀ pre : List (PTree sigma nu), (∀ c ∈ pre, PTree.frontier c = []) →
      PTree.frontierList pre = []
  | [], _ => rfl
  | c :: cs, h => by
    simp only [PTree.frontierList, h c List.mem_cons_self, List.nil_append]
    exact frontierList_eq_nil cs fun d hd => h d (List.mem_cons_of_mem _ hd)

theorem tExpand_frontier {R : CTRS sigma nu} {T T' : PTree sigma nu} (h : TExpand R T T') :
    ∃ j ps rest, PTree.frontier T = j :: rest ∧ PTree.frontier T' = ps ++ rest ∧ Infer R j ps := by
  induction h with
  | leaf hi =>
    exact ⟨_, _, [], by simp [PTree.frontier], by simp [PTree.frontier, frontierList_map_goal], hi⟩
  | inner j pre post hpre _ ih =>
    obtain ⟨j', ps, rest, h1, h2, hi⟩ := ih
    refine ⟨j', ps, rest ++ PTree.frontierList post, ?_, ?_, hi⟩
    · simp only [PTree.frontier, frontierList_append, frontierList_eq_nil pre hpre,
        PTree.frontierList, h1, List.nil_append, List.cons_append]
    · simp only [PTree.frontier, frontierList_append, frontierList_eq_nil pre hpre,
        PTree.frontierList, h2, List.nil_append, List.append_assoc]

theorem expand_of_tExpand {R : CTRS sigma nu} {T T' : PTree sigma nu} (h : TExpand R T T') :
    Expand R (PTree.frontier T) (PTree.frontier T') := by
  obtain ⟨j, ps, rest, h1, h2, hi⟩ := tExpand_frontier h
  rw [h1, h2]
  exact Expand.mk rest hi

theorem split_frontierList :
    ∀ (ts : List (PTree sigma nu)) (j : Judg sigma nu) (rest : List (Judg sigma nu)),
      PTree.frontierList ts = j :: rest →
        ∃ pre c post rc, ts = pre ++ c :: post ∧ (∀ x ∈ pre, PTree.frontier x = []) ∧
          PTree.frontier c = j :: rc ∧ rest = rc ++ PTree.frontierList post
  | [], _, _, h => by simp [PTree.frontierList] at h
  | t :: ts, j, rest, h => by
    simp only [PTree.frontierList] at h
    cases hft : PTree.frontier t with
    | nil =>
      rw [hft, List.nil_append] at h
      obtain ⟨pre, c, post, rc, rfl, hpre, hc, hrest⟩ := split_frontierList ts j rest h
      refine ⟨t :: pre, c, post, rc, rfl, ?_, hc, hrest⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      exacts [hft, hpre x hx]
    | cons j' rc =>
      rw [hft, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], t, ts, rc, rfl, by simp, hft, rfl⟩

theorem tExpand_of_frontier {R : CTRS sigma nu} :
    ∀ (T : PTree sigma nu) (j : Judg sigma nu) (rest ps : List (Judg sigma nu)),
      PTree.frontier T = j :: rest → Infer R j ps →
        ∃ T', TExpand R T T' ∧ PTree.frontier T' = ps ++ rest := by
  intro T
  induction T using PTree.rec' with
  | hgoal j0 =>
    intro j rest ps h hi
    simp only [PTree.frontier, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, TExpand.leaf hi, by simp [PTree.frontier, frontierList_map_goal]⟩
  | hnode j0 ts ih =>
    intro j rest ps h hi
    simp only [PTree.frontier] at h
    obtain ⟨pre, c, post, rc, rfl, hpre, hc, rfl⟩ := split_frontierList ts j rest h
    obtain ⟨c', hcc', hc'⟩ := ih c (by simp) j rc ps hc hi
    refine ⟨_, TExpand.inner j0 pre post hpre hcc', ?_⟩
    simp only [PTree.frontier, frontierList_append, frontierList_eq_nil pre hpre,
      PTree.frontierList, hc', List.nil_append, List.append_assoc]

theorem acc_tree_of_good {R : CTRS sigma nu} {T : PTree sigma nu}
    (h : Good R (PTree.frontier T)) : Acc (fun T' T => TExpand R T T') T := by
  have := InvImage.accessible (r := fun b a => Expand R a b) PTree.frontier h
  exact Subrelation.accessible (fun {_ _} hab => expand_of_tExpand hab) this

theorem good_of_acc_tree {R : CTRS sigma nu} {T : PTree sigma nu}
    (h : Acc (fun T' T => TExpand R T T') T) : Good R (PTree.frontier T) := by
  induction h with
  | intro T _ ih =>
    refine Acc.intro _ fun Y hY => ?_
    generalize hF : PTree.frontier T = F at hY
    cases hY with
    | mk rest hi =>
      obtain ⟨T', hT', hF'⟩ := tExpand_of_frontier T _ rest _ hF hi
      rw [← hF']
      exact ih T' hT'

/-- Operational termination (Lucas, Marché and Meseguer 2005, restated by Lucas and Meseguer
2014, Section 2): no infinite well-formed proof tree for a goal `s →* t` exists. An infinite
well-formed proof tree is an infinite sequence of leftmost expansions. -/
def OperationallyTerminating (R : CTRS sigma nu) : Prop :=
  ∀ s t : Term sigma nu, Acc (fun T' T => TExpand R T T') (PTree.goal (.steps s t))

theorem operationallyTerminating_iff (R : CTRS sigma nu) :
    OperationallyTerminating R ↔ ∀ s t : Term sigma nu, LFin R (.steps s t) := by
  constructor
  · intro h s t
    have := good_of_acc_tree (h s t)
    simpa [PTree.frontier] using this
  · intro h s t
    exact acc_tree_of_good (by simpa [PTree.frontier] using h s t)

/-! ### Operationally terminating terms -/

/-- A term is operationally terminating when every proof attempt of a goal with that left side
is finite (Lucas and Meseguer 2014, Definition 1). -/
def OTt (R : CTRS sigma nu) (s : Term sigma nu) : Prop :=
  ∀ w, LFin R (.step s w) ∧ LFin R (.steps s w)

theorem lfin_steps_of_cstep {R : CTRS sigma nu} {s t w : Term sigma nu} (hst : CStep R s t)
    (h : LFin R (.steps s w)) : LFin R (.steps t w) := by
  refine good_of_rtg ?_ h
  exact Relation.ReflTransGen.head (Expand.mk [] (Infer.tran s t w)) (derivable_reach hst _)

theorem lfin_step_of_lfin_steps {R : CTRS sigma nu} {t w w' : Term sigma nu}
    (h : LFin R (.steps t w)) : LFin R (.step t w') :=
  lfin_of_good_cons (Acc.inv h (Expand.mk [] (Infer.tran t w' w)))

theorem ot_of_steps {R : CTRS sigma nu} {t : Term sigma nu}
    (h : ∀ w, LFin R (.steps t w)) : OTt R t :=
  fun w => ⟨lfin_step_of_lfin_steps (h w), h w⟩

theorem ot_of_cstep {R : CTRS sigma nu} {s t : Term sigma nu} (h : OTt R s) (hst : CStep R s t) :
    OTt R t :=
  ot_of_steps fun w => lfin_steps_of_cstep hst (h w).2

theorem ot_of_csteps {R : CTRS sigma nu} {s t : Term sigma nu} (h : OTt R s)
    (hst : CSteps R s t) : OTt R t := by
  have h' := csteps_iff_rtg.1 hst
  clear hst
  induction h' with
  | refl => exact h
  | tail _ h2 ih => exact ot_of_cstep ih h2

/-- Operational termination bounds rewriting: an operationally terminating term is strongly
normalizing for the conditional rewrite relation. -/
theorem acc_cstep_of_lfin {R : CTRS sigma nu} {s w : Term sigma nu} (h : LFin R (.steps s w)) :
    Acc (fun t s => CStep R s t) s := by
  have key : ∀ X, Acc (Relation.TransGen (fun b a => Expand R a b)) X →
      ∀ s, X = [Judg.steps s w] → Acc (fun t s => CStep R s t) s := by
    intro X hX
    induction hX with
    | intro X _ ih =>
      intro s hXs
      subst hXs
      refine Acc.intro s fun t hst => ih [Judg.steps t w] ?_ t rfl
      have hpath : Relation.TransGen (Expand R) [Judg.steps s w] [Judg.steps t w] :=
        Relation.TransGen.head' (Expand.mk [] (Infer.tran s t w)) (derivable_reach hst _)
      exact (Relation.transGen_swap (r := Expand R)).2 hpath
  exact key _ h.transGen s rfl

theorem acc_cstep_of_ot {R : CTRS sigma nu} {s : Term sigma nu} (h : OTt R s) :
    Acc (fun t s => CStep R s t) s :=
  acc_cstep_of_lfin (h s).2

/-- A strongly normalizing term whose reducts have finite one-step proof attempts has finite
many-step proof attempts. -/
theorem lfin_steps_of {R : CTRS sigma nu} {a : Term sigma nu}
    (hacc : Acc (fun t s => CStep R s t) a)
    (hred : ∀ a', CSteps R a a' → ∀ w', LFin R (.step a' w')) : ∀ w, LFin R (.steps a w) := by
  induction hacc with
  | intro a _ ih =>
    intro w
    rw [lfin_iff]
    intro ps hi
    rcases infer_steps_inv hi with ⟨rfl, rfl⟩ | ⟨t, rfl⟩
    · exact good_nil R
    · exact good_cons_of_lfin (hred a (csteps_refl R a) t) fun hst =>
        ih t hst (fun a' ha' => hred a' (csteps_head hst ha')) w

theorem ot_of_arg {R : CTRS sigma nu} {f : sigma} {pre post : List (Term sigma nu)}
    {a : Term sigma nu} (h : OTt R (.app f (pre ++ a :: post))) : OTt R a := by
  have hacc : ∀ z, Acc (fun t s => CStep R s t) z → ∀ x, z = .app f (pre ++ x :: post) →
      Acc (fun t s => CStep R s t) x := by
    intro z hz
    induction hz with
    | intro z _ ih =>
      intro x hx
      subst hx
      exact Acc.intro x fun y hxy => ih _ (cstep_cong f pre post hxy) y rfl
  refine ot_of_steps (lfin_steps_of (hacc _ (acc_cstep_of_ot h) a rfl) ?_)
  intro a' ha' w'
  have hC := ot_of_csteps h (csteps_cong f pre post ha')
  have hG := (lfin_iff.1 ((hC (.app f (pre ++ w' :: post))).1)) _ (Infer.cong f pre post a' w')
  exact hG

theorem ot_of_mem {R : CTRS sigma nu} {f : sigma} {args : List (Term sigma nu)}
    (h : OTt R (.app f args)) {a : Term sigma nu} (ha : a ∈ args) : OTt R a := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
  exact ot_of_arg h

theorem ot_of_isSubterm {R : CTRS sigma nu} {w t : Term sigma nu} (h : IsSubterm w t)
    (ht : OTt R t) : OTt R w := by
  induction h with
  | refl => exact ht
  | arg f args hmem _ ih => exact ih (ot_of_mem ht hmem)

/-- `f` is the root of a left-hand side. -/
def CDefined (R : CTRS sigma nu) (f : sigma) : Prop :=
  ∃ ρ ∈ R, ∃ largs : List (Term sigma nu), ρ.lhs = .app f largs

theorem cdefined_of_instance {R : CTRS sigma nu} {ρ : CRule sigma nu} (hρ : ρ ∈ R)
    {σ : Subst sigma nu} {f : sigma} {xs : List (Term sigma nu)}
    (h : Term.app f xs = Subst.apply σ ρ.lhs) : CDefined R f := by
  obtain ⟨g, largs, hg⟩ := crule_lhs_eq_app ρ
  rw [hg, Subst.apply_app] at h
  simp only [Term.app.injEq] at h
  exact ⟨ρ, hρ, largs, by rw [hg, h.1]⟩

theorem ot_var {R : CTRS sigma nu} (x : nu) : OTt R (.var x) := by
  have hstep : ∀ w, LFin R (.step (.var x) w) := by
    intro w
    rw [lfin_iff]
    intro ps hi
    rcases infer_step_inv hi with ⟨f, pre, post, a, b, h, -, -⟩ | ⟨ρ, _, σ, h, -, -⟩
    · exact Term.noConfusion h
    · obtain ⟨g, largs, hg⟩ := crule_lhs_eq_app ρ
      rw [hg, Subst.apply_app] at h
      exact Term.noConfusion h
  have hnone : ∀ t, ¬ CStep R (.var x) t := by
    intro t ht
    rcases cstep_inv ht with ⟨f, pre, post, a, b, h, -, -⟩ | ⟨ρ, _, σ, h, -, -⟩
    · exact Term.noConfusion h
    · obtain ⟨g, largs, hg⟩ := crule_lhs_eq_app ρ
      rw [hg, Subst.apply_app] at h
      exact Term.noConfusion h
  refine ot_of_steps fun w => ?_
  rw [lfin_iff]
  intro ps hi
  rcases infer_steps_inv hi with ⟨-, rfl⟩ | ⟨t, rfl⟩
  · exact good_nil R
  · exact good_cons_of_lfin (hstep t) fun hd => absurd hd (hnone t)

/-- An application whose root is not defined is operationally terminating when its arguments
are. -/
theorem ot_app_of_not_defined {R : CTRS sigma nu} {f : sigma} (hf : ¬ CDefined R f) :
    ∀ args : List (Term sigma nu), (∀ a ∈ args, OTt R a) → OTt R (.app f args) := by
  have key : ∀ xs : List (Term sigma nu),
      Acc (fun ys xs => ArgStepOf (CStep R) xs ys) xs → (∀ a ∈ xs, OTt R a) →
        OTt R (.app f xs) := by
    intro xs hacc
    induction hacc with
    | intro xs _ ih =>
      intro hxs
      have hstep : ∀ w, LFin R (.step (.app f xs) w) := by
        intro w
        rw [lfin_iff]
        intro ps hi
        rcases infer_step_inv hi with ⟨g, pre, post, a, b, h, -, rfl⟩ | ⟨ρ, hρ, σ, h, -, -⟩
        · simp only [Term.app.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact (hxs a (by simp) b).1
        · exact absurd (cdefined_of_instance hρ h) hf
      refine ot_of_steps fun w => ?_
      rw [lfin_iff]
      intro ps hi
      rcases infer_steps_inv hi with ⟨-, rfl⟩ | ⟨t, rfl⟩
      · exact good_nil R
      · refine good_cons_of_lfin (hstep t) fun hd => ?_
        rcases cstep_inv hd with ⟨g, pre, post, a, b, h, rfl, hab⟩ | ⟨ρ, hρ, σ, h, -, -⟩
        · simp only [Term.app.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have harg : ArgStepOf (CStep R) (pre ++ a :: post) (pre ++ b :: post) :=
            ⟨pre, post, a, b, rfl, rfl, hab⟩
          exact (ih _ harg (argStepOf_preserve (fun _ _ ha hab => ot_of_cstep ha hab) hxs harg) w).2
        · exact absurd (cdefined_of_instance hρ h) hf
  intro args hargs
  exact key args (accArgsOf (S := CStep R) args fun a ha => acc_cstep_of_ot (hargs a ha)) hargs

theorem isSubterm_subst_var [DecidableEq nu] (σ : Subst sigma nu) :
    ∀ (t : Term sigma nu) (x : nu), x ∈ Term.vars t → IsSubterm (σ x) (Subst.apply σ t) := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
    intro x hx
    simp only [Term.vars_var, Finset.mem_singleton] at hx
    subst hx
    simpa using IsSubterm.refl (σ x)
  | happ g args ih =>
    intro x hx
    rw [Term.vars_app, Term.mem_varsList_iff] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    rw [Subst.apply_app, Subst.applyList_eq_map]
    exact IsSubterm.arg g _ (List.mem_map_of_mem ha) (ih a ha x hxa)

/-- A variable of the left-hand side is instantiated below the arguments of the call. -/
theorem ot_var_of_lhs [DecidableEq nu] {R : CTRS sigma nu} {ρ : CRule sigma nu}
    {σ : Subst sigma nu} {f : sigma} {xs : List (Term sigma nu)}
    (hl : Term.app f xs = Subst.apply σ ρ.lhs) (hxs : ∀ a ∈ xs, OTt R a) {x : nu}
    (hx : x ∈ Term.vars ρ.lhs) : OTt R (σ x) := by
  obtain ⟨g, largs, hg⟩ := crule_lhs_eq_app ρ
  rw [hg, Subst.apply_app] at hl
  simp only [Term.app.injEq] at hl
  obtain ⟨-, rfl⟩ := hl
  rw [hg, Term.vars_app, Term.mem_varsList_iff] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  have hmem : Subst.apply σ a ∈ Subst.applyList σ largs := by
    rw [Subst.applyList_eq_map]
    exact List.mem_map_of_mem ha
  exact ot_of_isSubterm (isSubterm_subst_var σ a x hxa) (hxs _ hmem)

/-- An instance is operationally terminating when the instantiated variables and every
instantiated defined call below it are. -/
theorem ot_subst [DecidableEq nu] {R : CTRS sigma nu} (σ : Subst sigma nu) :
    ∀ w : Term sigma nu, (∀ x ∈ Term.vars w, OTt R (σ x)) →
      (∀ g targs, IsSubterm (.app g targs) w → CDefined R g →
        (∀ a ∈ Subst.applyList σ targs, OTt R a) → OTt R (.app g (Subst.applyList σ targs))) →
      OTt R (Subst.apply σ w) := by
  intro w
  induction w using Term.rec' with
  | hvar x =>
    intro hv _
    simpa using hv x (by simp)
  | happ g targs ih =>
    intro hv hc
    have hargs : ∀ a ∈ Subst.applyList σ targs, OTt R a := by
      intro a ha
      rw [Subst.applyList_eq_map, List.mem_map] at ha
      obtain ⟨t, ht, rfl⟩ := ha
      refine ih t ht (fun x hx => hv x ?_) (fun g' targs' hsub hdef hargs' =>
        hc g' targs' (IsSubterm.arg g targs ht hsub) hdef hargs')
      rw [Term.vars_app, Term.mem_varsList_iff]
      exact ⟨t, ht, hx⟩
    rw [Subst.apply_app]
    by_cases hg : CDefined R g
    · exact hc g targs (IsSubterm.refl _) hg hargs
    · exact ot_app_of_not_defined hg _ hargs

/-! ### 2D dependency pairs and their chains -/

/-- The pair edges of 2D dependency pairs (Lucas and Meseguer 2014, Definition 4), without the
side conditions `ℓ ⋫ v`, `DRules(R, v) ≠ ∅` and `URules(R, v) ≠ ∅`, which only remove pairs.
From a call that is an instance `σ(ℓ)` of a left-hand side there is a horizontal edge to every
instantiated defined call of the right-hand side when all conditions hold, and a vertical edge
to every instantiated defined call of the left side `sₖ` of a condition when the conditions
before it hold. -/
def Pair2D (R : CTRS sigma nu) (c d : Call sigma nu) : Prop :=
  ∃ ρ ∈ R, ∃ σ : Subst sigma nu, Term.app c.1 c.2 = Subst.apply σ ρ.lhs ∧
    ((CondsHold R σ ρ.conds ∧ ∃ targs, IsSubterm (.app d.1 targs) ρ.rhs ∧ CDefined R d.1 ∧
        d.2 = Subst.applyList σ targs) ∨
      ∃ pre s t post, ρ.conds = pre ++ (s, t) :: post ∧ CondsHold R σ pre ∧
        ∃ targs, IsSubterm (.app d.1 targs) s ∧ CDefined R d.1 ∧ d.2 = Subst.applyList σ targs)

/-- Minimal 2D chains (Lucas and Meseguer 2014, Definition 5, with `Q = ∅`): the arguments of
both calls are operationally terminating, and the source arguments rewrite below the root to an
instance of a left-hand side before the pair edge is taken. -/
def MinChain2D (R : CTRS sigma nu) (c d : Call sigma nu) : Prop :=
  (∀ a ∈ c.2, OTt R a) ∧ (∀ a ∈ d.2, OTt R a) ∧
    ∃ xs, Relation.ReflTransGen (ArgStepOf (CStep R)) c.2 xs ∧ Pair2D R (c.1, xs) d

/-- Determinism of an oriented 3-CTRS (Lucas and Meseguer 2014, Section 2): the variables of a
condition's left side occur in the left-hand side or in the right sides of earlier conditions. -/
def CDeterministic [DecidableEq nu] (R : CTRS sigma nu) : Prop :=
  ∀ ρ ∈ R, ∀ pre s t post, ρ.conds = pre ++ (s, t) :: post →
    ∀ x ∈ Term.vars s, x ∈ Term.vars ρ.lhs ∨ ∃ c ∈ pre, x ∈ Term.vars c.2

/-- Rules of type 3: the right-hand side uses variables of the left-hand side and of the right
sides of the conditions. -/
def CType3 [DecidableEq nu] (R : CTRS sigma nu) : Prop :=
  ∀ ρ ∈ R, ∀ x ∈ Term.vars ρ.rhs, x ∈ Term.vars ρ.lhs ∨ ∃ c ∈ ρ.conds, x ∈ Term.vars c.2

/-- Under determinism, the instance of a condition's left side whose predecessors hold is
operationally terminating when the call arguments and the calls it contains are. -/
theorem ot_cond_lhs [DecidableEq nu] {R : CTRS sigma nu} {ρ : CRule sigma nu}
    {σ : Subst sigma nu} {f : sigma} {xs : List (Term sigma nu)}
    (hdet : ∀ pre s t post, ρ.conds = pre ++ (s, t) :: post →
      ∀ x ∈ Term.vars s, x ∈ Term.vars ρ.lhs ∨ ∃ c ∈ pre, x ∈ Term.vars c.2)
    (hl : Term.app f xs = Subst.apply σ ρ.lhs) (hxs : ∀ a ∈ xs, OTt R a)
    (hcall : ∀ pre s t post, ρ.conds = pre ++ (s, t) :: post → CondsHold R σ pre →
      ∀ g targs, IsSubterm (.app g targs) s → CDefined R g →
        (∀ a ∈ Subst.applyList σ targs, OTt R a) → OTt R (.app g (Subst.applyList σ targs))) :
    ∀ n pre s t post, ρ.conds = pre ++ (s, t) :: post → pre.length = n → CondsHold R σ pre →
      OTt R (Subst.apply σ s) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro pre s t post hsplit hlen hpre
    refine ot_subst σ s (fun x hx => ?_) (hcall pre s t post hsplit hpre)
    rcases hdet pre s t post hsplit x hx with hxl | ⟨c, hc, hxc⟩
    · exact ot_var_of_lhs hl hxs hxl
    · obtain ⟨pre1, pre2, rfl⟩ := List.append_of_mem hc
      have hsplit' : ρ.conds = pre1 ++ (c.1, c.2) :: (pre2 ++ (s, t) :: post) := by
        rw [hsplit]
        simp
      have hlt : pre1.length < n := by
        rw [← hlen]
        simp only [List.length_append, List.length_cons]
        omega
      have hpre1 : CondsHold R σ pre1 := fun c' hc' => hpre c' (by simp [hc'])
      have hot := ihn pre1.length hlt pre1 c.1 c.2 (pre2 ++ (s, t) :: post) hsplit' rfl hpre1
      have hsteps : CSteps R (Subst.apply σ c.1) (Subst.apply σ c.2) := hpre c (by simp)
      exact ot_of_isSubterm (isSubterm_subst_var σ c.2 x hxc) (ot_of_csteps hot hsteps)

/-- The core of 2D dependency-pair soundness: a call accessible for the minimal 2D chain
relation, with operationally terminating arguments, gives operationally terminating
applications after any argument rewriting. -/
theorem ot_app_of_2D_acc [DecidableEq nu] {R : CTRS sigma nu} (hdet : CDeterministic R)
    (h3 : CType3 R) :
    ∀ c : Call sigma nu, Acc (fun d c => MinChain2D R c d) c → (∀ a ∈ c.2, OTt R a) →
      ∀ xs, Relation.ReflTransGen (ArgStepOf (CStep R)) c.2 xs → (∀ a ∈ xs, OTt R a) →
        OTt R (.app c.1 xs) := by
  intro c hc
  induction hc with
  | intro c _ ihc =>
    intro hcSN xs hreach hxs
    have hacc := accArgsOf (S := CStep R) xs fun a ha => acc_cstep_of_ot (hxs a ha)
    induction hacc with
    | intro xs _ ihx =>
      have hchain : ∀ d : Call sigma nu, Pair2D R (c.1, xs) d → (∀ a ∈ d.2, OTt R a) →
          OTt R (.app d.1 d.2) := fun d hd hdOT =>
        ihc d ⟨hcSN, hdOT, xs, hreach, hd⟩ hdOT d.2 .refl hdOT
      have hstep : ∀ w, LFin R (.step (.app c.1 xs) w) := by
        intro w
        rw [lfin_iff]
        intro ps hi
        rcases infer_step_inv hi with ⟨f, pre, post, a, b, h, -, rfl⟩ | ⟨ρ, hρ, σ, h, -, rfl⟩
        · simp only [Term.app.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact (hxs a (by simp) b).1
        · refine good_of_goodSeq _
            (goodSeq_condGoals σ ρ.conds fun pre s t post hsplit hpre => ?_)
          have hot := ot_cond_lhs (hdet ρ hρ) h hxs
            (fun pre' s' t' post' hsplit' hpre' g targs hsub hdef hargs =>
              hchain (g, Subst.applyList σ targs)
                ⟨ρ, hρ, σ, h, Or.inr ⟨pre', s', t', post', hsplit', hpre', targs, hsub, hdef, rfl⟩⟩
                hargs)
            pre.length pre s t post hsplit rfl hpre
          exact (hot (Subst.apply σ t)).2
      refine ot_of_steps fun w => ?_
      rw [lfin_iff]
      intro ps hi
      rcases infer_steps_inv hi with ⟨-, rfl⟩ | ⟨t, rfl⟩
      · exact good_nil R
      · refine good_cons_of_lfin (hstep t) fun hd => ?_
        rcases cstep_inv hd with ⟨f, pre, post, a, b, h, rfl, hab⟩ | ⟨ρ, hρ, σ, h, rfl, hconds⟩
        · simp only [Term.app.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have harg : ArgStepOf (CStep R) (pre ++ a :: post) (pre ++ b :: post) :=
            ⟨pre, post, a, b, rfl, rfl, hab⟩
          exact (ihx _ harg (hreach.tail harg)
            (argStepOf_preserve (fun _ _ ha hab => ot_of_cstep ha hab) hxs harg) w).2
        · have hvert : ∀ pre' s' t' post', ρ.conds = pre' ++ (s', t') :: post' →
              CondsHold R σ pre' → ∀ g targs, IsSubterm (.app g targs) s' → CDefined R g →
                (∀ a ∈ Subst.applyList σ targs, OTt R a) →
                  OTt R (.app g (Subst.applyList σ targs)) :=
            fun pre' s' t' post' hsplit' hpre' g targs hsub hdef hargs =>
              hchain (g, Subst.applyList σ targs)
                ⟨ρ, hρ, σ, h, Or.inr ⟨pre', s', t', post', hsplit', hpre', targs, hsub, hdef, rfl⟩⟩
                hargs
          have hcondOT : ∀ c ∈ ρ.conds, OTt R (Subst.apply σ c.1) := by
            intro c hc
            obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hc
            exact ot_cond_lhs (hdet ρ hρ) h hxs hvert pre.length pre c.1 c.2 post
              (by rw [hsplit]) rfl (fun c' hc' => hconds c' (by rw [hsplit]; simp [hc']))
          have hr : OTt R (Subst.apply σ ρ.rhs) := by
            refine ot_subst σ ρ.rhs (fun x hx => ?_) (fun g targs hsub hdef hargs =>
              hchain (g, Subst.applyList σ targs)
                ⟨ρ, hρ, σ, h, Or.inl ⟨hconds, targs, hsub, hdef, rfl⟩⟩ hargs)
            rcases h3 ρ hρ x hx with hxl | ⟨c, hc, hxc⟩
            · exact ot_var_of_lhs h hxs hxl
            · exact ot_of_isSubterm (isSubterm_subst_var σ c.2 x hxc)
                (ot_of_csteps (hcondOT c hc) (hconds c hc))
          exact (hr w).2

theorem ot_of_2D [DecidableEq nu] {R : CTRS sigma nu} (hdet : CDeterministic R)
    (h3 : CType3 R) (hwf : WellFounded (fun d c => MinChain2D R c d)) :
    ∀ s : Term sigma nu, OTt R s := by
  intro s
  induction s using Term.rec' with
  | hvar x => exact ot_var x
  | happ f args ih => exact ot_app_of_2D_acc hdet h3 (f, args) (hwf.apply _) ih args .refl ih

/-- 2D dependency-pair soundness: a deterministic 3-CTRS without infinite minimal 2D chains is
operationally terminating (the direction "if" of Lucas and Meseguer 2014, Theorem 3, for the
pair set without its side conditions). -/
theorem operationallyTerminating_of_2D [DecidableEq nu] {R : CTRS sigma nu}
    (hdet : CDeterministic R) (h3 : CType3 R)
    (hwf : WellFounded (fun d c => MinChain2D R c d)) : OperationallyTerminating R :=
  (operationallyTerminating_iff R).2 fun s _ => (ot_of_2D hdet h3 hwf s _).2

/-! ### Algebras over `ℕ` on conditional systems -/

/-- The conditions hold algebraically: every condition weakly decreases. -/
def AlgCondsHold (A : sigma → List Nat → Nat) (α : nu → Nat)
    (cs : List (Term sigma nu × Term sigma nu)) : Prop :=
  ∀ c ∈ cs, evalT A α c.2 ≤ evalT A α c.1

/-- Every rule weakly decreases whenever its conditions do. -/
def AlgRulesWeak (A : sigma → List Nat → Nat) (R : CTRS sigma nu) : Prop :=
  ∀ ρ ∈ R, ∀ α : nu → Nat, AlgCondsHold A α ρ.conds → evalT A α ρ.rhs ≤ evalT A α ρ.lhs

/-- A weakly monotone algebra whose rules weakly decrease contains conditional rewriting:
`π(→*_R) ⊆ ≥` in the sense of Lucas and Meseguer 2014, Theorem 10. -/
theorem derivable_eval_le {A : sigma → List Nat → Nat} {R : CTRS sigma nu} (hmono : AlgMono A)
    (hR : AlgRulesWeak A R) :
    ∀ {j : Judg sigma nu}, Derivable R j → ∀ α : nu → Nat,
      match j with
      | .step s t => evalT A α t ≤ evalT A α s
      | .steps s t => evalT A α t ≤ evalT A α s := by
  intro j h
  induction h with
  | intro hi hps ih =>
    intro α
    cases hi with
    | refl t => exact le_refl (evalT A α t)
    | tran s t w =>
      have h1 : evalT A α t ≤ evalT A α s := ih (.step s t) (by simp) α
      have h2 : evalT A α w ≤ evalT A α t := ih (.steps t w) (by simp) α
      exact le_trans h2 h1
    | cong f pre post a b =>
      have h1 : evalT A α b ≤ evalT A α a := ih (.step a b) (by simp) α
      show evalT A α (.app f (pre ++ b :: post)) ≤ evalT A α (.app f (pre ++ a :: post))
      rw [evalT_app, evalT_app]
      exact hmono f _ _ (forall₂_map_le h1 pre post)
    | repl hρ σ =>
      show evalT A α (Subst.apply σ _) ≤ evalT A α (Subst.apply σ _)
      rw [evalT_subst, evalT_subst]
      refine hR _ hρ _ fun c hc => ?_
      have h1 : evalT A α (Subst.apply σ c.2) ≤ evalT A α (Subst.apply σ c.1) :=
        ih (.steps (Subst.apply σ c.1) (Subst.apply σ c.2)) (List.mem_map_of_mem hc) α
      simpa only [evalT_subst] using h1

theorem csteps_eval_le {A : sigma → List Nat → Nat} {R : CTRS sigma nu} (hmono : AlgMono A)
    (hR : AlgRulesWeak A R) {s t : Term sigma nu} (h : CSteps R s t) (α : nu → Nat) :
    evalT A α t ≤ evalT A α s :=
  derivable_eval_le hmono hR h α

theorem cstep_eval_le {A : sigma → List Nat → Nat} {R : CTRS sigma nu} (hmono : AlgMono A)
    (hR : AlgRulesWeak A R) {s t : Term sigma nu} (h : CStep R s t) (α : nu → Nat) :
    evalT A α t ≤ evalT A α s :=
  derivable_eval_le hmono hR h α

/-- Argument rewriting weakly decreases the values of the arguments, position by position. -/
theorem argSteps_evals_le {A : sigma → List Nat → Nat} {R : CTRS sigma nu} (hmono : AlgMono A)
    (hR : AlgRulesWeak A R) (α : nu → Nat) {xs ys : List (Term sigma nu)}
    (h : Relation.ReflTransGen (ArgStepOf (CStep R)) xs ys) :
    List.Forall₂ (fun x y : Nat => x ≤ y) (ys.map (evalT A α)) (xs.map (evalT A α)) := by
  induction h with
  | refl => exact forall₂_refl (fun x => le_refl x) _
  | tail _ hst ih =>
    obtain ⟨pre, post, a, b, rfl, rfl, hab⟩ := hst
    exact forall₂_trans (r := fun x y : Nat => x ≤ y) (fun x y z hxy hyz => le_trans hxy hyz)
      (forall₂_map_le (cstep_eval_le hmono hR hab α) pre post) ih

theorem algCondsHold_of_condsHold {A : sigma → List Nat → Nat} {R : CTRS sigma nu}
    (hmono : AlgMono A) (hR : AlgRulesWeak A R) {σ : Subst sigma nu}
    {cs : List (Term sigma nu × Term sigma nu)} (h : CondsHold R σ cs) (α : nu → Nat) :
    AlgCondsHold A (fun x => evalT A α (σ x)) cs := by
  intro c hc
  have := csteps_eval_le hmono hR (h c hc) α
  simpa only [evalT_subst] using this

end Conditional

/-! ### The removal-triple processor on 2D problems -/

section RemovalTriple

variable {sigma : Type u} {nu : Type v}

/-- Data of the removal-triple processor (Lucas and Meseguer 2014, Theorem 10) for the removal
triple `(≥, ≥, >)` of an algebra over `ℕ`: the interpretation of the rewrite signature, an
argument filtering of the marked symbols (kept positions), and the interpretation of each marked
symbol on its kept arguments. -/
structure CondAlgebra (sigma : Type u) where
  base : sigma → List Nat → Nat
  filter : sigma → List Nat
  marked : sigma → List Nat → Nat

/-- The value of a marked call under the filtering. -/
def callVal (M : CondAlgebra sigma) (α : nu → Nat) (f : sigma) (args : List (Term sigma nu)) :
    Nat :=
  M.marked f (filterVals (M.filter f) (args.map (evalT M.base α)))

theorem callVal_subst (M : CondAlgebra sigma) (α : nu → Nat) (σ : Subst sigma nu) (f : sigma)
    (args : List (Term sigma nu)) :
    callVal M α f (Subst.applyList σ args) = callVal M (fun x => evalT M.base α (σ x)) f args := by
  unfold callVal
  rw [evalL_subst]

/-- Every horizontal pair strictly decreases when the conditions of its rule hold
algebraically. -/
def AlgHorizontalStrict (M : CondAlgebra sigma) (R : CTRS sigma nu) : Prop :=
  ∀ ρ ∈ R, ∀ f largs, ρ.lhs = .app f largs → ∀ g targs, IsSubterm (.app g targs) ρ.rhs →
    CDefined R g → ∀ α : nu → Nat, AlgCondsHold M.base α ρ.conds →
      callVal M α g targs < callVal M α f largs

/-- Every vertical pair strictly decreases when the conditions before its condition hold
algebraically. -/
def AlgVerticalStrict (M : CondAlgebra sigma) (R : CTRS sigma nu) : Prop :=
  ∀ ρ ∈ R, ∀ f largs, ρ.lhs = .app f largs → ∀ pre s t post, ρ.conds = pre ++ (s, t) :: post →
    ∀ g targs, IsSubterm (.app g targs) s → CDefined R g → ∀ α : nu → Nat,
      AlgCondsHold M.base α pre → callVal M α g targs < callVal M α f largs

/-- The removal-triple processor with every pair strictly decreasing: the minimal 2D chain
relation is well founded. The conditions of a pair are used through the algebra: a condition
`σ(s) →* σ(t)` gives `[σ(s)] ≥ [σ(t)]`. -/
theorem wf_minChain2D_of_algebra {R : CTRS sigma nu} (M : CondAlgebra sigma)
    (hmono : AlgMono M.base) (hmmono : AlgMono M.marked) (hR : AlgRulesWeak M.base R)
    (hH : AlgHorizontalStrict M R) (hV : AlgVerticalStrict M R) :
    WellFounded (fun d c => MinChain2D R c d) := by
  let α0 : nu → Nat := fun _ => 0
  let m : Call sigma nu → Nat := fun c => callVal M α0 c.1 c.2
  refine Subrelation.wf (r := fun d c => m d < m c) ?_ (InvImage.wf m Nat.lt_wfRel.wf)
  intro d c hcd
  obtain ⟨-, -, xs, hreach, ρ, hρ, σ, hl, hedge⟩ := hcd
  have hvals := argSteps_evals_le hmono hR α0 hreach
  have hle : m (c.1, xs) ≤ m c :=
    hmmono _ _ _ (forall₂_filterVals hvals (M.filter c.1))
  obtain ⟨g0, largs, hg0⟩ := crule_lhs_eq_app ρ
  have hl' := hl
  rw [hg0, Subst.apply_app] at hl'
  simp only [Term.app.injEq] at hl'
  obtain ⟨hf, hxs⟩ := hl'
  have hsrc : m (c.1, xs) = callVal M (fun x => evalT M.base α0 (σ x)) g0 largs := by
    show callVal M α0 c.1 xs = _
    rw [hf, hxs, callVal_subst]
  have hstrict : m d < m (c.1, xs) := by
    rw [hsrc]
    rcases hedge with ⟨hconds, targs, hsub, hdef, hd⟩ | ⟨pre, s, t, post, hsplit, hpre, targs, hsub, hdef, hd⟩
    · have hdv : m d = callVal M (fun x => evalT M.base α0 (σ x)) d.1 targs := by
        show callVal M α0 d.1 d.2 = _
        rw [hd, callVal_subst]
      rw [hdv]
      exact hH ρ hρ g0 largs hg0 d.1 targs hsub hdef _
        (algCondsHold_of_condsHold hmono hR hconds α0)
    · have hdv : m d = callVal M (fun x => evalT M.base α0 (σ x)) d.1 targs := by
        show callVal M α0 d.1 d.2 = _
        rw [hd, callVal_subst]
      rw [hdv]
      exact hV ρ hρ g0 largs hg0 pre s t post hsplit d.1 targs hsub hdef _
        (algCondsHold_of_condsHold hmono hR hpre α0)
  exact lt_of_lt_of_le hstrict hle

end RemovalTriple

/-! ## Subterm lists and the unconditional specialization -/

section Syntax

variable {sigma : Type u} {nu : Type v}

mutual
/-- All subterms of a term. -/
def subtermsT : Term sigma nu → List (Term sigma nu)
  | .var x => [.var x]
  | .app f args => .app f args :: subtermsL args
/-- All subterms of the terms of a list. -/
def subtermsL : List (Term sigma nu) → List (Term sigma nu)
  | [] => []
  | a :: as => subtermsT a ++ subtermsL as
end

theorem mem_subtermsT_self (t : Term sigma nu) : t ∈ subtermsT t := by
  cases t with
  | var x => simp [subtermsT]
  | app f args => simp [subtermsT]

theorem mem_subtermsL_of_mem {a : Term sigma nu} :
    ∀ {args : List (Term sigma nu)}, a ∈ args → ∀ w, w ∈ subtermsT a → w ∈ subtermsL args
  | b :: bs, h, w, hw => by
    simp only [List.mem_cons] at h
    simp only [subtermsL, List.mem_append]
    rcases h with rfl | h
    · exact Or.inl hw
    · exact Or.inr (mem_subtermsL_of_mem h w hw)

theorem mem_subtermsT_of_isSubterm {w t : Term sigma nu} (h : IsSubterm w t) :
    w ∈ subtermsT t := by
  induction h with
  | refl => exact mem_subtermsT_self _
  | arg f args hmem _ ih =>
    simp only [subtermsT, List.mem_cons]
    exact Or.inr (mem_subtermsL_of_mem hmem _ ih)

theorem isSubterm_trans {a b c : Term sigma nu} (h1 : IsSubterm a b) (h2 : IsSubterm b c) :
    IsSubterm a c := by
  induction h2 with
  | refl => exact h1
  | arg f args hmem _ ih => exact IsSubterm.arg f args hmem ih

/-- The unconditional specialization: the rules with their conditions dropped. -/
def uncond (R : CTRS sigma nu) : TRS sigma nu := R.map fun ρ => ⟨ρ.lhs, ρ.rhs, ρ.lhs_isApp⟩

/-- A one-position list comparison read off `getD`. -/
theorem getD_le_of_forall₂ {xs ys : List Nat} (h : List.Forall₂ (fun x y : Nat => x ≤ y) xs ys)
    (i : Nat) : xs.getD i 0 ≤ ys.getD i 0 := by
  rcases forall₂_getElem? h i with ⟨h1, h2⟩ | ⟨x, y, h1, h2, hxy⟩
  · simp [List.getD_eq_getElem?_getD, h1, h2]
  · simp [List.getD_eq_getElem?_getD, h1, h2, hxy]

end Syntax

/-! ## The conditional recursor -/

/-- Symbols of the conditional recursor. -/
inductive CSym where
  | zero
  | succ
  | wrap
  | recur
  | isZero
  | pred
  | tt
  | ff
  deriving DecidableEq

/-- Terms of the conditional recursor. -/
abbrev CTerm : Type := Term CSym Nat

/-- `isZero(zero) → true`. -/
def izZeroRule : CRule CSym Nat := ⟨.app .isZero [.app .zero []], .app .tt [], [], rfl⟩

/-- `isZero(succ(x)) → false`. -/
def izSuccRule : CRule CSym Nat := ⟨.app .isZero [.app .succ [.var 3]], .app .ff [], [], rfl⟩

/-- `pred(succ(x)) → x`. -/
def predRule : CRule CSym Nat := ⟨.app .pred [.app .succ [.var 3]], .var 3, [], rfl⟩

/-- `recur(b, s, n) → b ⇐ isZero(n) →* true`. -/
def recZeroRule : CRule CSym Nat :=
  ⟨.app .recur [.var 0, .var 1, .var 2], .var 0, [(.app .isZero [.var 2], .app .tt [])], rfl⟩

/-- `recur(b, s, n) → wrap(s, recur(b, s, pred(n))) ⇐ isZero(n) →* false`. -/
def recSuccRule : CRule CSym Nat :=
  ⟨.app .recur [.var 0, .var 1, .var 2],
    .app .wrap [.var 1, .app .recur [.var 0, .var 1, .app .pred [.var 2]]],
    [(.app .isZero [.var 2], .app .ff [])], rfl⟩

/-- The conditional recursor: the free recursor in the language of conditional rewriting, with
the counter tested by the conditions `isZero(n) →* true` and `isZero(n) →* false`. -/
def condRecursor : CTRS CSym Nat := [izZeroRule, izSuccRule, predRule, recZeroRule, recSuccRule]

theorem mem_condRecursor {ρ : CRule CSym Nat} (h : ρ ∈ condRecursor) :
    ρ = izZeroRule ∨ ρ = izSuccRule ∨ ρ = predRule ∨ ρ = recZeroRule ∨ ρ = recSuccRule := by
  simpa [condRecursor] using h

theorem condRecursor_defined_iff (g : CSym) :
    CDefined condRecursor g ↔ g = .isZero ∨ g = .pred ∨ g = .recur := by
  constructor
  · rintro ⟨ρ, hρ, largs, hl⟩
    rcases mem_condRecursor hρ with rfl | rfl | rfl | rfl | rfl <;>
      simp only [izZeroRule, izSuccRule, predRule, recZeroRule, recSuccRule, Term.app.injEq] at hl <;>
      obtain ⟨rfl, -⟩ := hl <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨izZeroRule, by simp [condRecursor], _, rfl⟩
    · exact ⟨predRule, by simp [condRecursor], _, rfl⟩
    · exact ⟨recZeroRule, by simp [condRecursor], _, rfl⟩

theorem singleton_split {β : Type u} {c d : β} {pre post : List β} (h : [c] = pre ++ d :: post) :
    pre = [] ∧ d = c ∧ post = [] := by
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.1.symm, h.2.symm⟩
  | cons p pre' =>
    simp only [List.cons_append, List.cons.injEq] at h
    exact absurd h.2 (by simp)

theorem condRecursor_deterministic : CDeterministic condRecursor := by
  intro ρ hρ pre s t post hsplit x hx
  left
  rcases mem_condRecursor hρ with rfl | rfl | rfl | rfl | rfl
  · simp [izZeroRule] at hsplit
  · simp [izSuccRule] at hsplit
  · simp [predRule] at hsplit
  · obtain ⟨-, hd, -⟩ := singleton_split hsplit
    simp only [Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    simp [recZeroRule] at hx ⊢
    omega
  · obtain ⟨-, hd, -⟩ := singleton_split hsplit
    simp only [Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    simp [recSuccRule] at hx ⊢
    omega

theorem condRecursor_type3 : CType3 condRecursor := by
  intro ρ hρ x hx
  left
  rcases mem_condRecursor hρ with rfl | rfl | rfl | rfl | rfl <;>
    simp [izZeroRule, izSuccRule, predRule, recZeroRule, recSuccRule] at hx ⊢ <;> omega

/-- Arities of the symbols of the conditional recursor. -/
def cArity : CSym → Nat
  | .zero => 0
  | .succ => 1
  | .wrap => 2
  | .recur => 3
  | .isZero => 1
  | .pred => 1
  | .tt => 0
  | .ff => 0

/-- The algebra over `ℕ` of the conditional recursor: `zero = true = 0`, `false = 1`,
`succ(x) = x + 1`, `pred(x) = x ∸ 1`, `isZero(x) = x`, `recur(b, s, n) = b`, `wrap(s, r) = r`. -/
def condBase : CSym → List Nat → Nat
  | .zero, _ => 0
  | .succ, xs => xs.getD 0 0 + 1
  | .pred, xs => xs.getD 0 0 - 1
  | .isZero, xs => xs.getD 0 0
  | .tt, _ => 0
  | .ff, _ => 1
  | .recur, xs => xs.getD 0 0
  | .wrap, xs => xs.getD 1 0

theorem condBase_mono : AlgMono condBase := by
  intro f xs ys h
  have h0 := getD_le_of_forall₂ h 0
  have h1 := getD_le_of_forall₂ h 1
  cases f <;> simp only [condBase] <;> omega

theorem condBase_rulesWeak : AlgRulesWeak condBase condRecursor := by
  intro ρ hρ α _
  rcases mem_condRecursor hρ with rfl | rfl | rfl | rfl | rfl <;>
    simp [izZeroRule, izSuccRule, predRule, recZeroRule, recSuccRule, evalT_app, condBase]

/-! ### Terms, liveness of the conditions, and the looping-condition control -/

/-- `zero`. -/
def zC : CTerm := .app .zero []
/-- `succ(t)`. -/
def sC (t : CTerm) : CTerm := .app .succ [t]
/-- `pred(t)`. -/
def pC (t : CTerm) : CTerm := .app .pred [t]
/-- `isZero(t)`. -/
def izC (t : CTerm) : CTerm := .app .isZero [t]
/-- `wrap(s, t)`. -/
def wC (s t : CTerm) : CTerm := .app .wrap [s, t]
/-- `recur(b, s, n)`. -/
def rC (b s n : CTerm) : CTerm := .app .recur [b, s, n]
/-- `true`. -/
def ttC : CTerm := .app .tt []
/-- `false`. -/
def ffC : CTerm := .app .ff []

theorem no_cstep_of_undefined {f : CSym} (hf : ¬ CDefined condRecursor f)
    {args : List CTerm} (hargs : ∀ a ∈ args, ∀ t, ¬ CStep condRecursor a t) :
    ∀ t, ¬ CStep condRecursor (.app f args) t := by
  intro t h
  rcases cstep_inv h with ⟨g, pre, post, a, b, h1, -, hab⟩ | ⟨ρ, hρ, σ, h1, -, -⟩
  · simp only [Term.app.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact hargs a (by simp) b hab
  · exact hf (cdefined_of_instance hρ h1)

theorem no_cstep_zC (t : CTerm) : ¬ CStep condRecursor zC t :=
  no_cstep_of_undefined (by simp [condRecursor_defined_iff]) (by simp) t

theorem no_cstep_ffC (t : CTerm) : ¬ CStep condRecursor ffC t :=
  no_cstep_of_undefined (by simp [condRecursor_defined_iff]) (by simp) t

theorem no_cstep_sC_zC (t : CTerm) : ¬ CStep condRecursor (sC zC) t :=
  no_cstep_of_undefined (by simp [condRecursor_defined_iff])
    (by intro a ha; simp at ha; subst ha; exact no_cstep_zC) t

theorem cstep_izC_sC_zC {t : CTerm} (h : CStep condRecursor (izC (sC zC)) t) : t = ffC := by
  rcases cstep_inv h with ⟨g, pre, post, a, b, h1, -, hab⟩ | ⟨ρ, hρ, σ, h1, h2, -⟩
  · simp only [izC, Term.app.injEq] at h1
    obtain ⟨-, h1⟩ := h1
    have ha : a = sC zC := by
      cases pre with
      | nil => simp only [List.nil_append, List.cons.injEq] at h1; exact h1.1.symm
      | cons p pre' => simp at h1
    subst ha
    exact absurd hab (no_cstep_sC_zC b)
  · rcases mem_condRecursor hρ with rfl | rfl | rfl | rfl | rfl <;>
      simp [izZeroRule, izSuccRule, predRule, recZeroRule, recSuccRule, izC, sC] at h1 h2 ⊢
    exact h2

theorem csteps_izC_sC_zC {t : CTerm} (h : CSteps condRecursor (izC (sC zC)) t) :
    t = izC (sC zC) ∨ t = ffC := by
  have h' := csteps_iff_rtg.1 h
  clear h
  induction h' with
  | refl => exact Or.inl rfl
  | tail _ hst ih =>
    rcases ih with rfl | rfl
    · exact Or.inr (cstep_izC_sC_zC hst)
    · exact absurd hst (no_cstep_ffC _)

/-- Both truth values of the conditions occur and decide which rule fires: at the counter
`zero` the rule with `isZero(n) →* true` fires and the rule with `isZero(n) →* false` is
blocked; at `succ(zero)` the reverse holds. -/
theorem condRecursor_live :
    (CStep condRecursor (rC zC zC zC) zC ∧
      ¬ CStep condRecursor (rC zC zC zC) (wC zC (rC zC zC (pC zC)))) ∧
    (CStep condRecursor (rC zC zC (sC zC)) (wC zC (rC zC zC (pC (sC zC)))) ∧
      ¬ CStep condRecursor (rC zC zC (sC zC)) zC) := by
  have hz : CSteps condRecursor (izC zC) ttC :=
    csteps_of_cstep (cstep_repl (ρ := izZeroRule) (by simp [condRecursor]) (fun _ => zC)
      (by simp [CondsHold, izZeroRule]))
  have hs : CSteps condRecursor (izC (sC zC)) ffC :=
    csteps_of_cstep (cstep_repl (ρ := izSuccRule) (by simp [condRecursor]) (fun _ => zC)
      (by simp [CondsHold, izSuccRule]))
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact cstep_repl (ρ := recZeroRule) (by simp [condRecursor]) (fun _ => zC)
      (by simpa [CondsHold, recZeroRule] using hz)
  · intro h
    rcases cstep_inv h with ⟨g, pre, post, a, b, h1, h2, -⟩ | ⟨ρ, hρ, σ, h1, h2, hc⟩
    · simp only [rC, wC, Term.app.injEq] at h1 h2
      exact absurd (h1.1.trans h2.1.symm) (by decide)
    · rcases mem_condRecursor hρ with rfl | rfl | rfl | rfl | rfl
      · simp [izZeroRule, rC] at h1
      · simp [izSuccRule, rC] at h1
      · simp [predRule, rC] at h1
      · simp [recZeroRule, rC, wC, zC] at h1 h2
        rw [← h1.1] at h2
        exact absurd h2 (by simp)
      · simp [recSuccRule, rC, zC] at h1
        have hcs := hc (.app .isZero [.var 2], .app .ff []) (by simp [recSuccRule])
        have hle := csteps_eval_le condBase_mono condBase_rulesWeak hcs (fun _ => 0)
        simp [evalT_app, condBase, ← h1.2.2] at hle
  · exact cstep_repl (ρ := recSuccRule) (by simp [condRecursor])
      (fun x => if x = 2 then sC zC else zC)
      (by simpa [CondsHold, recSuccRule] using hs)
  · intro h
    rcases cstep_inv h with ⟨g, pre, post, a, b, h1, h2, -⟩ | ⟨ρ, hρ, σ, h1, h2, hc⟩
    · simp only [rC, zC, Term.app.injEq] at h1 h2
      exact absurd (h1.1.trans h2.1.symm) (by decide)
    · rcases mem_condRecursor hρ with rfl | rfl | rfl | rfl | rfl
      · simp [izZeroRule, rC] at h1
      · simp [izSuccRule, rC] at h1
      · simp [predRule, rC] at h1
      · simp [recZeroRule, rC] at h1
        have hcs := hc (.app .isZero [.var 2], .app .tt []) (by simp [recZeroRule])
        have hcs' : CSteps condRecursor (izC (sC zC)) ttC := by
          simpa [izC, ttC, ← h1.2.2] using hcs
        rcases csteps_izC_sC_zC hcs' with h' | h'
        · simp [izC, ttC] at h'
        · simp [ttC, ffC] at h'
      · simp [recSuccRule, zC] at h2

/-- The looping-condition control: `recur(b, s, n) → b ⇐ recur(b, s, n) →* zero`. -/
def loopCondRule : CRule CSym Nat :=
  ⟨.app .recur [.var 0, .var 1, .var 2], .var 0,
    [(.app .recur [.var 0, .var 1, .var 2], .app .zero [])], rfl⟩

/-- The one-rule conditional system of the looping condition. -/
def loopCTRS : CTRS CSym Nat := [loopCondRule]

theorem loopCTRS_derivable :
    ∀ {j : Judg CSym Nat}, Derivable loopCTRS j →
      match j with
      | .step _ _ => False
      | .steps s t => s = t := by
  intro j h
  induction h with
  | intro hi hps ih =>
    cases hi with
    | refl => rfl
    | tran s t w => exact (ih (.step s t) (by simp) : False).elim
    | cong f pre post a b => exact (ih (.step a b) (by simp) : False)
    | repl hρ σ =>
      simp only [loopCTRS, List.mem_singleton] at hρ
      subst hρ
      have := ih _ (List.mem_singleton_self _)
      simp at this

/-- The conditional rewrite relation of the looping-condition control is empty. -/
theorem loopCTRS_no_step (s t : CTerm) : ¬ CStep loopCTRS s t :=
  fun h => loopCTRS_derivable h

theorem loopCTRS_not_operationallyTerminating : ¬ OperationallyTerminating loopCTRS := by
  rw [operationallyTerminating_iff]
  intro h
  let u : CTerm := rC zC zC zC
  let X : Nat → List (Judg CSym Nat) := fun n =>
    Judg.steps u zC :: List.replicate n (Judg.steps zC zC)
  let Y : Nat → List (Judg CSym Nat) := fun n =>
    [Judg.step u zC, Judg.steps zC zC] ++ List.replicate n (Judg.steps zC zC)
  have hXY : ∀ n, Expand loopCTRS (X n) (Y n) := fun n =>
    Expand.mk (List.replicate n (Judg.steps zC zC)) (Infer.tran u zC zC)
  have hYX : ∀ n, Expand loopCTRS (Y n) (X (n + 1)) := fun n =>
    Expand.mk (Judg.steps zC zC :: List.replicate n (Judg.steps zC zC))
      (Infer.repl (ρ := loopCondRule) (by simp [loopCTRS]) (fun _ => zC))
  have key : ∀ Z, Good loopCTRS Z → ∀ n, Z ≠ X n ∧ Z ≠ Y n := by
    intro Z hZ
    induction hZ with
    | intro Z _ ih =>
      intro n
      constructor
      · rintro rfl
        exact (ih (Y n) (hXY n) n).2 rfl
      · rintro rfl
        exact (ih (X (n + 1)) (hYX n) (n + 1)).1 rfl
  exact (key (X 0) (h u zC) 0).1 rfl

/-- The unconditional specialization of the looping-condition control terminates. -/
theorem uncond_loopCTRS_terminating : ∀ t : CTerm, SN (uncond loopCTRS) t := by
  refine terminating_of_subtermCriterion (uncond loopCTRS) ?_ (proj := fun _ => 0) ?_
  · intro rule hrule
    simp only [uncond, loopCTRS, List.map_cons, List.map_nil, List.mem_singleton] at hrule
    subst hrule
    intro x hx
    simp [loopCondRule] at hx ⊢
    omega
  · intro rule hrule f largs _ g targs hsub _
    simp only [uncond, loopCTRS, List.map_cons, List.map_nil, List.mem_singleton] at hrule
    subst hrule
    exact absurd hsub not_isSubterm_app_var

/-- The unconditional specialization of the conditional recursor does not terminate: the
recursive rule fires at every counter. -/
theorem uncond_condRecursor_not_sn : ¬ SN (uncond condRecursor) (rC zC zC zC) := by
  have hmem : (⟨recSuccRule.lhs, recSuccRule.rhs, recSuccRule.lhs_isApp⟩ : Rule CSym Nat) ∈
      uncond condRecursor := List.mem_map.2 ⟨recSuccRule, by simp [condRecursor], rfl⟩
  have key : ∀ t, SN (uncond condRecursor) t → ∀ b s n, IsSubterm (rC b s n) t → False := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro b s n hsub
      have hroot : Step (uncond condRecursor) (rC b s n) (wC s (rC b s (pC n))) :=
        Step.root ⟨_, hmem, fun x => if x = 0 then b else if x = 1 then s else n,
          by simp [recSuccRule, rC], by simp [recSuccRule, rC, wC, pC]⟩
      obtain ⟨t', ht', hsub'⟩ := step_lift_subterm hsub hroot
      exact ih t' ht' b s (pC n)
        (isSubterm_trans (IsSubterm.arg CSym.wrap _ (by simp) (IsSubterm.refl _)) hsub')
  exact fun h => key _ h zC zC zC (IsSubterm.refl _)

/-! ## Row: twoDDPForCTRS -/

/-- The witness data: the algebra `condBase`, the filtering that keeps the counter of `recur♯`,
and `recur♯(n) = n + 1`; the other marked symbols are interpreted by `0`. -/
def twoDWitnessAlg : CondAlgebra CSym where
  base := condBase
  filter := fun
    | .recur => [2]
    | _ => []
  marked := fun
    | .recur, xs => xs.getD 0 0 + 1
    | _, _ => 0

/-- Native data: the removal-triple data of Lucas and Meseguer 2014, Theorem 10, for the triple
`(≥, ≥, >)` of an algebra over `ℕ`. -/
abbrev twoDDPForCTRSData : Type := CondAlgebra CSym

/-- Lucas and Meseguer (2D Dependency Pairs for Proving Operational Termination of CTRSs,
WRLA 2014, LNCS 8663, Theorem 10 with Definition 12): the removal triple is induced by a weakly
monotone algebra that contains `→*_R` (every rule weakly decreases whenever its conditions do),
and the argument filtering keeps positions below the arity. -/
def twoDDPForCTRSLaws (M : twoDDPForCTRSData) : Prop :=
  AlgMono M.base ∧ AlgMono M.marked ∧ AlgRulesWeak M.base condRecursor ∧
    ∀ f, ∀ i ∈ M.filter f, i < cArity f

/-- Every 2D pair of the conditional recursor (Definition 4) strictly decreases under the
filtered algebra whenever its conditions hold. -/
def twoDDPForCTRSAccepts (M : twoDDPForCTRSData) : Prop :=
  AlgHorizontalStrict M condRecursor ∧ AlgVerticalStrict M condRecursor

/-- Verdict: escape. -/
def twoDDPForCTRSResult (M : twoDDPForCTRSData) : Prop :=
  twoDDPForCTRSAccepts M ∧ OperationallyTerminating condRecursor

/-- Soundness of the 2D dependency-pair method: finite 2D chains give operational
termination. -/
theorem twoDDPForCTRS_sound :
    ∀ M, twoDDPForCTRSLaws M → twoDDPForCTRSAccepts M → OperationallyTerminating condRecursor :=
  fun M hL hA => operationallyTerminating_of_2D condRecursor_deterministic condRecursor_type3
    (wf_minChain2D_of_algebra M hL.1 hL.2.1 hL.2.2.1 hA.1 hA.2)

def twoDDPForCTRSWitness : twoDDPForCTRSData := twoDWitnessAlg

theorem twoDWitness_marked_mono : AlgMono twoDWitnessAlg.marked := by
  intro f xs ys h
  have h0 := getD_le_of_forall₂ h 0
  cases f <;> simp only [twoDWitnessAlg] <;> omega

theorem twoDDPForCTRSWitness_laws : twoDDPForCTRSLaws twoDDPForCTRSWitness := by
  refine ⟨condBase_mono, twoDWitness_marked_mono, condBase_rulesWeak, ?_⟩
  intro f i hi
  cases f <;> simp_all [twoDDPForCTRSWitness, twoDWitnessAlg, cArity]

theorem twoDWitness_horizontal : AlgHorizontalStrict twoDWitnessAlg condRecursor := by
  intro ρ hρ f largs hl g targs hsub hdef α hc
  rw [condRecursor_defined_iff] at hdef
  have hm := mem_subtermsT_of_isSubterm hsub
  rcases mem_condRecursor hρ with rfl | rfl | rfl | rfl | rfl
  · simp [izZeroRule, subtermsT, subtermsL] at hm
    obtain ⟨rfl, -⟩ := hm
    simp at hdef
  · simp [izSuccRule, subtermsT, subtermsL] at hm
    obtain ⟨rfl, -⟩ := hm
    simp at hdef
  · simp [predRule, subtermsT] at hm
  · simp [recZeroRule, subtermsT] at hm
  · simp only [recSuccRule, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    have h1 := hc (.app .isZero [.var 2], .app .ff []) (by simp [recSuccRule])
    simp [evalT_app, twoDWitnessAlg, condBase] at h1
    simp [recSuccRule, subtermsT, subtermsL] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp at hdef
    · simp [callVal, filterVals, twoDWitnessAlg, evalT_app, condBase]
      omega
    · simp [callVal, filterVals, twoDWitnessAlg]

theorem twoDWitness_vertical : AlgVerticalStrict twoDWitnessAlg condRecursor := by
  intro ρ hρ f largs hl pre s t post hsplit g targs hsub hdef α _
  rw [condRecursor_defined_iff] at hdef
  rcases mem_condRecursor hρ with rfl | rfl | rfl | rfl | rfl
  · simp [izZeroRule] at hsplit
  · simp [izSuccRule] at hsplit
  · simp [predRule] at hsplit
  · simp only [recZeroRule, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    obtain ⟨-, hd, -⟩ := singleton_split hsplit
    simp only [Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    have hm := mem_subtermsT_of_isSubterm hsub
    simp [subtermsT, subtermsL] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp [callVal, filterVals, twoDWitnessAlg]
  · simp only [recSuccRule, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    obtain ⟨-, hd, -⟩ := singleton_split hsplit
    simp only [Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    have hm := mem_subtermsT_of_isSubterm hsub
    simp [subtermsT, subtermsL] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp [callVal, filterVals, twoDWitnessAlg]

theorem twoDDPForCTRSWitness_result : twoDDPForCTRSResult twoDDPForCTRSWitness :=
  ⟨⟨twoDWitness_horizontal, twoDWitness_vertical⟩,
    twoDDPForCTRS_sound _ twoDDPForCTRSWitness_laws ⟨twoDWitness_horizontal, twoDWitness_vertical⟩⟩

/-- The conditions are live (both truth values occur and select the rule), and the vertical
dimension is load-bearing: the looping-condition control has an empty rewrite relation and a
terminating unconditional specialization, and it is not operationally terminating. -/
theorem twoDDPForCTRSWitness_feature :
    ((CStep condRecursor (rC zC zC zC) zC ∧
        ¬ CStep condRecursor (rC zC zC zC) (wC zC (rC zC zC (pC zC)))) ∧
      (CStep condRecursor (rC zC zC (sC zC)) (wC zC (rC zC zC (pC (sC zC)))) ∧
        ¬ CStep condRecursor (rC zC zC (sC zC)) zC)) ∧
    (¬ OperationallyTerminating loopCTRS ∧ (∀ s t : CTerm, ¬ CStep loopCTRS s t) ∧
      ∀ t : CTerm, SN (uncond loopCTRS) t) :=
  ⟨condRecursor_live, loopCTRS_not_operationallyTerminating, loopCTRS_no_step,
    uncond_loopCTRS_terminating⟩

/-- The filtering that keeps the payload of `recur♯`. -/
def twoDPayloadAlg : CondAlgebra CSym :=
  { twoDWitnessAlg with
    filter := fun
      | .recur => [1]
      | _ => [] }

/-- Filtering `recur♯` to its payload keeps the laws and loses acceptance: the recursive pair
`recur♯(b, s, n) → recur♯(b, s, pred(n))` keeps the payload `s`. -/
theorem twoDDPForCTRS_mutation :
    twoDDPForCTRSLaws twoDPayloadAlg ∧ ¬ twoDDPForCTRSAccepts twoDPayloadAlg := by
  refine ⟨⟨condBase_mono, twoDWitness_marked_mono, condBase_rulesWeak, ?_⟩, fun h => ?_⟩
  · intro f i hi
    cases f <;> simp_all [twoDPayloadAlg, cArity]
  · have := h.1 recSuccRule (by simp [condRecursor]) .recur [.var 0, .var 1, .var 2] rfl .recur
      [.var 0, .var 1, .app .pred [.var 2]]
      (IsSubterm.arg CSym.wrap _ (by simp) (IsSubterm.refl _))
      ((condRecursor_defined_iff _).2 (by simp)) (fun _ => 1)
      (by
        intro c hc
        simp [recSuccRule] at hc
        subst hc
        simp [evalT_app, twoDPayloadAlg, twoDWitnessAlg, condBase])
    simp [callVal, filterVals, twoDPayloadAlg, twoDWitnessAlg, evalT_app, condBase] at this

/-! ## The unraveling `U(R)` -/

section Unraveling

variable {sigma : Type u} {nu : Type v}

/-- Symbols of the unraveled system: the original symbols and the fresh symbols `U^ρ_i`, indexed
by the position of the rule and of the condition. -/
abbrev USym (sigma : Type u) : Type u := sigma ⊕ (Nat × Nat)

mutual
/-- The embedding of original terms. -/
def embT : Term sigma nu → Term (USym sigma) nu
  | .var x => .var x
  | .app f args => .app (.inl f) (embL args)
/-- The embedding of an argument list. -/
def embL : List (Term sigma nu) → List (Term (USym sigma) nu)
  | [] => []
  | a :: as => embT a :: embL as
end

theorem embL_eq_map : ∀ args : List (Term sigma nu), embL args = args.map embT
  | [] => rfl
  | a :: as => by simp [embL, embL_eq_map as]

theorem embT_app (f : sigma) (args : List (Term sigma nu)) :
    embT (.app f args) = .app (.inl f) (args.map embT) := by
  simp [embT, embL_eq_map]

theorem embT_isApp {t : Term sigma nu} (h : t.isApp = true) : (embT t).isApp = true := by
  cases t with
  | var x => simp at h
  | app f args => simp [embT]

theorem embT_subst (σ : Subst sigma nu) :
    ∀ t : Term sigma nu,
      embT (Subst.apply σ t) = Subst.apply (fun x => embT (σ x)) (embT t) := by
  intro t
  induction t using Term.rec' with
  | hvar x => simp [embT]
  | happ f args ih =>
    rw [Subst.apply_app, embT_app, embT_app, Subst.apply_app, Subst.applyList_eq_map,
      Subst.applyList_eq_map, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun a ha => ih a ha

mutual
/-- The variables of a term from left to right. -/
def tvarsT : Term sigma nu → List nu
  | .var x => [x]
  | .app _ args => tvarsL args
/-- The variables of an argument list from left to right. -/
def tvarsL : List (Term sigma nu) → List nu
  | [] => []
  | a :: as => tvarsT a ++ tvarsL as
end

/-- The rules `U^ρ_i(tᵢ, Xᵢ) → U^ρ_{i+1}(sᵢ₊₁, Xᵢ₊₁)` and `U^ρ_n(tₙ, Xₙ) → r`, where `Xᵢ₊₁`
extends `Xᵢ` by the extra variables of `tᵢ`. -/
def uChain [DecidableEq nu] (k : Nat) (r : Term sigma nu) :
    Nat → List nu → Term sigma nu → List (Term sigma nu × Term sigma nu) →
      List (Rule (USym sigma) nu)
  | i, X, t, [] => [⟨.app (.inr (k, i)) (embT t :: X.map .var), embT r, rfl⟩]
  | i, X, t, (s', t') :: cs =>
    ⟨.app (.inr (k, i)) (embT t :: X.map .var),
      .app (.inr (k, i + 1))
        (embT s' :: (X ++ (tvarsT t).dedup.filter (· ∉ X)).map .var), rfl⟩ ::
      uChain k r (i + 1) (X ++ (tvarsT t).dedup.filter (· ∉ X)) t' cs

/-- The unraveled rules of the rule at position `k`. -/
def unravelRule [DecidableEq nu] (k : Nat) (ρ : CRule sigma nu) : List (Rule (USym sigma) nu) :=
  match ρ.conds with
  | [] => [⟨embT ρ.lhs, embT ρ.rhs, embT_isApp ρ.lhs_isApp⟩]
  | (s, t) :: cs =>
    ⟨embT ρ.lhs, .app (.inr (k, 0)) (embT s :: (tvarsT ρ.lhs).dedup.map .var),
        embT_isApp ρ.lhs_isApp⟩ ::
      uChain k ρ.rhs 0 (tvarsT ρ.lhs).dedup t cs

/-- The unraveled rules of the rules from position `k` on. -/
def unravelFrom [DecidableEq nu] : Nat → CTRS sigma nu → TRS (USym sigma) nu
  | _, [] => []
  | k, ρ :: R => unravelRule k ρ ++ unravelFrom (k + 1) R

/-- The unraveling `U(R)` (Ohlebusch, Advanced Topics in Term Rewriting, 2002, Definition
7.2.48, as restated by Sternagel and Sternagel, WST 2016, Section 2): a conditional rule
`ℓ → r ⇐ s₁ → t₁, …, sₙ → tₙ` becomes `ℓ → U₁(s₁, v(ℓ))`,
`Uᵢ(tᵢ, v(ℓ), ev(t₁, …, tᵢ₋₁)) → Uᵢ₊₁(sᵢ₊₁, v(ℓ), ev(t₁, …, tᵢ))` and
`Uₙ(tₙ, v(ℓ), ev(t₁, …, tₙ₋₁)) → r`; unconditional rules are kept. -/
def unravel [DecidableEq nu] (R : CTRS sigma nu) : TRS (USym sigma) nu := unravelFrom 0 R

theorem unravelFrom_mem [DecidableEq nu] :
    ∀ (R : CTRS sigma nu) (k : Nat) (ρ : CRule sigma nu), ρ ∈ R →
      ∃ k', ∀ rule ∈ unravelRule k' ρ, rule ∈ unravelFrom k R
  | [], _, _, h => by simp at h
  | ρ' :: R, k, ρ, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨k, fun rule hr => by simp [unravelFrom, hr]⟩
    · obtain ⟨k', hk'⟩ := unravelFrom_mem R (k + 1) ρ h
      exact ⟨k', fun rule hr => by simp [unravelFrom, hk' rule hr]⟩

theorem applyList_vars (θ : Subst (USym sigma) nu) (X : List nu) :
    Subst.applyList θ (X.map Term.var) = X.map θ := by
  rw [Subst.applyList_eq_map, List.map_map]
  rfl

theorem rtg_step_arg0 {U : TRS (USym sigma) nu} (g : USym sigma) (rest : List (Term (USym sigma) nu))
    {a b : Term (USym sigma) nu} (h : Relation.ReflTransGen (Step U) a b) :
    Relation.ReflTransGen (Step U) (.app g (a :: rest)) (.app g (b :: rest)) := by
  have := StepStar.arg_congr U g [] rest h
  simpa using this

theorem transGen_step_arg {U : TRS (USym sigma) nu} (g : USym sigma)
    (pre post : List (Term (USym sigma) nu)) {a b : Term (USym sigma) nu}
    (h : Relation.TransGen (Step U) a b) :
    Relation.TransGen (Step U) (.app g (pre ++ a :: post)) (.app g (pre ++ b :: post)) :=
  Relation.TransGen.lift (fun x => Term.app g (pre ++ x :: post))
    (fun _ _ hxy => Step.arg g pre post hxy) h

theorem step_rule_inst {U : TRS (USym sigma) nu} {rule : Rule (USym sigma) nu} (h : rule ∈ U)
    (θ : Subst (USym sigma) nu) {s t : Term (USym sigma) nu} (hs : s = Subst.apply θ rule.lhs)
    (ht : t = Subst.apply θ rule.rhs) : Step U s t := by
  subst hs ht
  exact Step.root ⟨rule, h, θ, rfl, rfl⟩

/-- Simulation of the horizontal chain of the unraveled rules: from the stage whose first
argument is the instance of the current condition's left side, the conditions lead to the
instance of the right-hand side. -/
theorem uChain_sim_H [DecidableEq nu] {U : TRS (USym sigma) nu} (k : Nat) (r : Term sigma nu)
    (θ : Subst (USym sigma) nu) :
    ∀ (cs : List (Term sigma nu × Term sigma nu)) (i : Nat) (X : List nu) (s t : Term sigma nu),
      (∀ rule ∈ uChain k r i X t cs, rule ∈ U) →
      Relation.ReflTransGen (Step U) (Subst.apply θ (embT s)) (Subst.apply θ (embT t)) →
      (∀ c ∈ cs, Relation.ReflTransGen (Step U) (Subst.apply θ (embT c.1))
        (Subst.apply θ (embT c.2))) →
      Relation.TransGen (Step U) (.app (.inr (k, i)) (Subst.apply θ (embT s) :: X.map θ))
        (Subst.apply θ (embT r)) := by
  intro cs
  induction cs with
  | nil =>
    intro i X s t hmem hst _
    have hrule := hmem _ List.mem_cons_self
    refine Relation.TransGen.tail' (rtg_step_arg0 _ _ hst) (step_rule_inst hrule θ ?_ rfl)
    simp [applyList_vars]
  | cons c cs ih =>
    obtain ⟨s', t'⟩ := c
    intro i X s t hmem hst hcs
    have hrule := hmem _ List.mem_cons_self
    have hstep : Step U (.app (.inr (k, i)) (Subst.apply θ (embT t) :: X.map θ))
        (.app (.inr (k, i + 1)) (Subst.apply θ (embT s') ::
          (X ++ (tvarsT t).dedup.filter (· ∉ X)).map θ)) :=
      step_rule_inst hrule θ
          (by simp only [Subst.apply_app, Subst.applyList_cons, applyList_vars])
          (by simp only [Subst.apply_app, Subst.applyList_cons, applyList_vars])
    have hrest := ih (i + 1) (X ++ (tvarsT t).dedup.filter (· ∉ X)) s' t'
      (fun rule hr => hmem rule (List.mem_cons_of_mem _ hr)) (hcs (s', t') (by simp))
      (fun c hc => hcs c (by simp [hc]))
    exact Relation.TransGen.trans_right (rtg_step_arg0 _ _ hst)
      (Relation.TransGen.head' hstep hrest.to_reflTransGen)

/-- Simulation of the vertical chain: when the conditions before a condition hold, the stage
whose first argument is the instance of that condition's left side is reached. -/
theorem uChain_sim_V [DecidableEq nu] {U : TRS (USym sigma) nu} (k : Nat) (r : Term sigma nu)
    (θ : Subst (USym sigma) nu) :
    ∀ (cs : List (Term sigma nu × Term sigma nu)) (i : Nat) (X : List nu) (s t : Term sigma nu),
      (∀ rule ∈ uChain k r i X t cs, rule ∈ U) →
      ∀ pre s0 t0 post, (s, t) :: cs = pre ++ (s0, t0) :: post →
        (∀ c ∈ pre, Relation.ReflTransGen (Step U) (Subst.apply θ (embT c.1))
          (Subst.apply θ (embT c.2))) →
        ∃ j Xs, Relation.ReflTransGen (Step U)
          (.app (.inr (k, i)) (Subst.apply θ (embT s) :: X.map θ))
          (.app (.inr (k, j)) (Subst.apply θ (embT s0) :: Xs)) := by
  intro cs
  induction cs with
  | nil =>
    intro i X s t _ pre s0 t0 post hsplit _
    obtain ⟨rfl, hd, -⟩ := singleton_split hsplit
    simp only [Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    exact ⟨i, X.map θ, .refl⟩
  | cons c cs ih =>
    obtain ⟨s', t'⟩ := c
    intro i X s t hmem pre s0 t0 post hsplit hpre
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hsplit
      obtain ⟨⟨rfl, rfl⟩, -⟩ := hsplit
      exact ⟨i, X.map θ, .refl⟩
    | cons p pre' =>
      simp only [List.cons_append, List.cons.injEq] at hsplit
      obtain ⟨rfl, hsplit'⟩ := hsplit
      have hst := hpre (s, t) (by simp)
      have hrule := hmem _ List.mem_cons_self
      have hstep : Step U (.app (.inr (k, i)) (Subst.apply θ (embT t) :: X.map θ))
          (.app (.inr (k, i + 1)) (Subst.apply θ (embT s') ::
            (X ++ (tvarsT t).dedup.filter (· ∉ X)).map θ)) :=
        step_rule_inst hrule θ
          (by simp only [Subst.apply_app, Subst.applyList_cons, applyList_vars])
          (by simp only [Subst.apply_app, Subst.applyList_cons, applyList_vars])
      obtain ⟨j, Xs, hreach⟩ := ih (i + 1) (X ++ (tvarsT t).dedup.filter (· ∉ X)) s' t'
        (fun rule hr => hmem rule (List.mem_cons_of_mem _ hr)) pre' s0 t0 post hsplit'
        (fun c hc => hpre c (by simp [hc]))
      exact ⟨j, Xs, ((rtg_step_arg0 _ _ hst).tail hstep).trans hreach⟩

/-- Every conditional step is simulated by at least one step of the unraveling, and every
reachability by a reachability. -/
theorem derivable_unravel_sim [DecidableEq nu] {R : CTRS sigma nu} :
    ∀ {j : Judg sigma nu}, Derivable R j →
      match j with
      | .step s t => Relation.TransGen (Step (unravel R)) (embT s) (embT t)
      | .steps s t => Relation.ReflTransGen (Step (unravel R)) (embT s) (embT t) := by
  intro j h
  induction h with
  | intro hi hps ih =>
    cases hi with
    | refl => exact .refl
    | tran s t w =>
      have h1 : Relation.TransGen (Step (unravel R)) (embT s) (embT t) := ih (.step s t) (by simp)
      have h2 : Relation.ReflTransGen (Step (unravel R)) (embT t) (embT w) :=
        ih (.steps t w) (by simp)
      exact h1.to_reflTransGen.trans h2
    | cong f pre post a b =>
      have h1 : Relation.TransGen (Step (unravel R)) (embT a) (embT b) := ih (.step a b) (by simp)
      show Relation.TransGen (Step (unravel R)) (embT (.app f (pre ++ a :: post)))
        (embT (.app f (pre ++ b :: post)))
      rw [embT_app, embT_app]
      simpa using transGen_step_arg (.inl f) (pre.map embT) (post.map embT) h1
    | @repl ρ hρ σ =>
      show Relation.TransGen (Step (unravel R)) (embT (Subst.apply σ ρ.lhs))
        (embT (Subst.apply σ ρ.rhs))
      have hconds : ∀ c ∈ ρ.conds, Relation.ReflTransGen (Step (unravel R))
          (Subst.apply (fun x => embT (σ x)) (embT c.1))
          (Subst.apply (fun x => embT (σ x)) (embT c.2)) := by
        intro c hc
        have h1 : Relation.ReflTransGen (Step (unravel R)) (embT (Subst.apply σ c.1))
            (embT (Subst.apply σ c.2)) :=
          ih (.steps (Subst.apply σ c.1) (Subst.apply σ c.2)) (List.mem_map_of_mem hc)
        simpa only [embT_subst] using h1
      rw [embT_subst, embT_subst]
      obtain ⟨k, hk⟩ := unravelFrom_mem R 0 ρ hρ
      unfold unravelRule at hk
      split at hk
      · exact .single (step_rule_inst (hk _ List.mem_cons_self) _ rfl rfl)
      · rename_i s t cs hcs
        have hfirst := step_rule_inst (U := unravel R) (hk _ List.mem_cons_self)
          (fun x => embT (σ x)) rfl rfl
        refine Relation.TransGen.head hfirst ?_
        have := uChain_sim_H (U := unravel R) k ρ.rhs (fun x => embT (σ x)) cs 0
          (tvarsT ρ.lhs).dedup s t (fun rule hr => hk rule (List.mem_cons_of_mem _ hr))
          (hconds (s, t) (by rw [hcs]; simp)) (fun c hc => hconds c (by rw [hcs]; simp [hc]))
        simpa [applyList_vars] using this

theorem transGen_stepOrSub_of_steps {U : TRS (USym sigma) nu} {a b : Term (USym sigma) nu}
    (h : Relation.TransGen (Step U) a b) : Relation.TransGen (StepOrSub U) b a := by
  induction h with
  | single h => exact .single (Or.inl h)
  | tail _ h ih => exact Relation.TransGen.head (Or.inl h) ih

theorem rtg_stepOrSub_of_steps {U : TRS (USym sigma) nu} {a b : Term (USym sigma) nu}
    (h : Relation.ReflTransGen (Step U) a b) : Relation.ReflTransGen (StepOrSub U) b a := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact Relation.ReflTransGen.head (Or.inl h) ih

/-- Termination of the unraveling on original terms gives operational termination: the order
`(→_U(R) ∪ ▷)⁺` read on original terms bounds the proof search (it contains the conditional
steps, the passage to arguments, and the passage from a left-hand side to the conditions whose
predecessors hold). -/
theorem ot_of_unravel [DecidableEq nu] (R : CTRS sigma nu)
    (hsn : ∀ s : Term sigma nu, SN (unravel R) (embT s)) : ∀ s : Term sigma nu, OTt R s := by
  intro s
  have hacc : Acc (fun t s => Relation.TransGen (StepOrSub (unravel R)) (embT t) (embT s)) s :=
    InvImage.accessible embT (acc_stepOrSub_of_sn (hsn s)).transGen
  induction hacc with
  | intro s _ ih =>
    have hstep : ∀ w, LFin R (.step s w) := by
      intro w
      rw [lfin_iff]
      intro ps hi
      rcases infer_step_inv hi with ⟨f, pre, post, a, b, rfl, -, rfl⟩ | ⟨ρ, hρ, σ, rfl, -, rfl⟩
      · have hlt : Relation.TransGen (StepOrSub (unravel R)) (embT a)
            (embT (.app f (pre ++ a :: post))) := by
          rw [embT_app]
          exact .single (Or.inr ⟨.inl f, _, rfl, List.mem_map_of_mem (by simp)⟩)
        exact (ih a hlt b).1
      · refine good_of_goodSeq _ (goodSeq_condGoals σ ρ.conds fun pre s0 t0 post hsplit hpre => ?_)
        obtain ⟨k, hk⟩ := unravelFrom_mem R 0 ρ hρ
        have hconds : ∀ c ∈ pre, Relation.ReflTransGen (Step (unravel R))
            (Subst.apply (fun x => embT (σ x)) (embT c.1))
            (Subst.apply (fun x => embT (σ x)) (embT c.2)) := by
          intro c hc
          have h1 := (derivable_unravel_sim (hpre c hc) :
            Relation.ReflTransGen (Step (unravel R)) (embT (Subst.apply σ c.1))
              (embT (Subst.apply σ c.2)))
          simpa only [embT_subst] using h1
        unfold unravelRule at hk
        split at hk
        · rename_i hnil
          rw [hnil] at hsplit
          simp at hsplit
        · rename_i s1 t1 cs hcs
          have hfirst := step_rule_inst (U := unravel R) (hk _ List.mem_cons_self)
            (fun x => embT (σ x)) rfl rfl
          obtain ⟨j, Xs, hreach⟩ := uChain_sim_V (U := unravel R) k ρ.rhs
            (fun x => embT (σ x)) cs 0 (tvarsT ρ.lhs).dedup s1 t1
            (fun rule hr => hk rule (List.mem_cons_of_mem _ hr)) pre s0 t0 post
            (by rw [← hcs, hsplit]) hconds
          have hpath : Relation.TransGen (Step (unravel R)) (embT (Subst.apply σ ρ.lhs))
              (.app (.inr (k, j)) (Subst.apply (fun x => embT (σ x)) (embT s0) :: Xs)) := by
            rw [embT_subst]
            refine Relation.TransGen.head' hfirst ?_
            simpa [applyList_vars] using hreach
          have hlt : Relation.TransGen (StepOrSub (unravel R)) (embT (Subst.apply σ s0))
              (embT (Subst.apply σ ρ.lhs)) := by
            rw [embT_subst σ s0]
            exact Relation.TransGen.head' (Or.inr ⟨_, _, rfl, by simp⟩)
              (transGen_stepOrSub_of_steps hpath).to_reflTransGen
          exact (ih _ hlt (Subst.apply σ t0)).2
    refine ot_of_steps fun w => ?_
    rw [lfin_iff]
    intro ps hi
    rcases infer_steps_inv hi with ⟨-, rfl⟩ | ⟨t, rfl⟩
    · exact good_nil R
    · refine good_cons_of_lfin (hstep t) fun hd => ?_
      have hsim : Relation.TransGen (Step (unravel R)) (embT s) (embT t) :=
        derivable_unravel_sim hd
      exact (ih t (transGen_stepOrSub_of_steps hsim) w).2

theorem operationallyTerminating_of_unravel [DecidableEq nu] (R : CTRS sigma nu)
    (hsn : ∀ s : Term sigma nu, SN (unravel R) (embT s)) : OperationallyTerminating R :=
  (operationallyTerminating_iff R).2 fun s _ => (ot_of_unravel R hsn s _).2

end Unraveling

/-! ## Reduction pairs of algebras over `ℕ` on rewrite systems -/

section MarkedAlgebra

variable {sigma : Type u} {nu : Type v}

/-- A weakly monotone algebra over `ℕ` with an interpretation of the marked symbols: the
reduction pair `(≥, >)` on calls of Arts and Giesl (TCS 236, 2000). -/
structure MarkedAlgebra (sigma : Type u) where
  base : sigma → List Nat → Nat
  marked : sigma → List Nat → Nat

/-- Every rule of a rewrite system weakly decreases. -/
def AlgTRSWeak (A : sigma → List Nat → Nat) (U : TRS sigma nu) : Prop :=
  ∀ rule ∈ U, ∀ α : nu → Nat, evalT A α rule.rhs ≤ evalT A α rule.lhs

/-- Every dependency pair strictly decreases. -/
def AlgPairsStrict (M : MarkedAlgebra sigma) (U : TRS sigma nu) : Prop :=
  ∀ rule ∈ U, ∀ f largs, rule.lhs = .app f largs → ∀ g targs, IsSubterm (.app g targs) rule.rhs →
    IsDefined U g → ∀ α : nu → Nat,
      M.marked g (targs.map (evalT M.base α)) < M.marked f (largs.map (evalT M.base α))

theorem step_eval_le {A : sigma → List Nat → Nat} {U : TRS sigma nu} (hmono : AlgMono A)
    (hU : AlgTRSWeak A U) {a b : Term sigma nu} (h : Step U a b) (α : nu → Nat) :
    evalT A α b ≤ evalT A α a := by
  induction h with
  | root h =>
    obtain ⟨rule, hrule, σ, rfl, rfl⟩ := h
    rw [evalT_subst, evalT_subst]
    exact hU rule hrule _
  | arg f pre post _ ih =>
    rw [evalT_app, evalT_app]
    exact hmono f _ _ (forall₂_map_le ih pre post)

/-- The reduction pair on calls of a marked algebra. -/
def algCallPair (M : MarkedAlgebra sigma) (U : TRS sigma nu) (hmono : AlgMono M.base)
    (hmmono : AlgMono M.marked) (hU : AlgTRSWeak M.base U) (hP : AlgPairsStrict M U) :
    CallReductionPair U where
  weak c d := M.marked d.1 (d.2.map (evalT M.base fun _ => 0)) ≤
    M.marked c.1 (c.2.map (evalT M.base fun _ => 0))
  strict c d := M.marked d.1 (d.2.map (evalT M.base fun _ => 0)) <
    M.marked c.1 (c.2.map (evalT M.base fun _ => 0))
  weak_refl _ := le_rfl
  weak_trans h₁ h₂ := le_trans h₂ h₁
  weak_strict h₁ h₂ := lt_of_lt_of_le h₂ h₁
  strict_wf := InvImage.wf (fun c : Call sigma nu => M.marked c.1 (c.2.map (evalT M.base fun _ => 0)))
    Nat.lt_wfRel.wf
  arg_weak f xs ys _ h := by
    obtain ⟨pre, post, a, b, rfl, rfl, hab⟩ := h
    exact hmmono f _ _ (forall₂_map_le (step_eval_le hmono hU hab _) pre post)
  pair_strict rule hrule σ f largs hl g targs hsub hdef _ _ := by
    show M.marked g ((Subst.applyList σ targs).map _) < M.marked f ((Subst.applyList σ largs).map _)
    rw [evalL_subst, evalL_subst]
    exact hP rule hrule f largs hl g targs hsub hdef _

/-- Termination by a marked algebra: rules weakly decrease and dependency pairs strictly
decrease. -/
theorem sn_of_markedAlgebra [DecidableEq nu] (M : MarkedAlgebra sigma) (U : TRS sigma nu)
    (hvars : ∀ rule ∈ U, Term.vars rule.rhs ⊆ Term.vars rule.lhs) (hmono : AlgMono M.base)
    (hmmono : AlgMono M.marked) (hU : AlgTRSWeak M.base U) (hP : AlgPairsStrict M U) :
    ∀ t : Term sigma nu, SN U t :=
  terminating_of_callReductionPair U hvars (algCallPair M U hmono hmmono hU hP)

end MarkedAlgebra

/-! ## Row: operationalTerminationCTRS -/

/-- `isZero(zero) → true`, embedded. -/
def uIzZero : Rule (USym CSym) Nat :=
  ⟨.app (.inl .isZero) [.app (.inl .zero) []], .app (.inl .tt) [], rfl⟩
/-- `isZero(succ(x)) → false`, embedded. -/
def uIzSucc : Rule (USym CSym) Nat :=
  ⟨.app (.inl .isZero) [.app (.inl .succ) [.var 3]], .app (.inl .ff) [], rfl⟩
/-- `pred(succ(x)) → x`, embedded. -/
def uPred : Rule (USym CSym) Nat := ⟨.app (.inl .pred) [.app (.inl .succ) [.var 3]], .var 3, rfl⟩
/-- `recur(b, s, n) → U₃(isZero(n), b, s, n)`. -/
def uRecZ1 : Rule (USym CSym) Nat :=
  ⟨.app (.inl .recur) [.var 0, .var 1, .var 2],
    .app (.inr (3, 0)) [.app (.inl .isZero) [.var 2], .var 0, .var 1, .var 2], rfl⟩
/-- `U₃(true, b, s, n) → b`. -/
def uRecZ2 : Rule (USym CSym) Nat :=
  ⟨.app (.inr (3, 0)) [.app (.inl .tt) [], .var 0, .var 1, .var 2], .var 0, rfl⟩
/-- `recur(b, s, n) → U₄(isZero(n), b, s, n)`. -/
def uRecS1 : Rule (USym CSym) Nat :=
  ⟨.app (.inl .recur) [.var 0, .var 1, .var 2],
    .app (.inr (4, 0)) [.app (.inl .isZero) [.var 2], .var 0, .var 1, .var 2], rfl⟩
/-- `U₄(false, b, s, n) → wrap(s, recur(b, s, pred(n)))`. -/
def uRecS2 : Rule (USym CSym) Nat :=
  ⟨.app (.inr (4, 0)) [.app (.inl .ff) [], .var 0, .var 1, .var 2],
    .app (.inl .wrap) [.var 1, .app (.inl .recur) [.var 0, .var 1, .app (.inl .pred) [.var 2]]],
    rfl⟩

/-- The unraveled conditional recursor, rule by rule. -/
def uCondRules : TRS (USym CSym) Nat := [uIzZero, uIzSucc, uPred, uRecZ1, uRecZ2, uRecS1, uRecS2]

theorem unravel_condRecursor : unravel condRecursor = uCondRules := rfl

theorem mem_uCondRules {rule : Rule (USym CSym) Nat} (h : rule ∈ uCondRules) :
    rule = uIzZero ∨ rule = uIzSucc ∨ rule = uPred ∨ rule = uRecZ1 ∨ rule = uRecZ2 ∨
      rule = uRecS1 ∨ rule = uRecS2 := by
  simpa [uCondRules] using h

theorem uCondRules_defined_iff (g : USym CSym) :
    IsDefined uCondRules g ↔
      g = .inl .isZero ∨ g = .inl .pred ∨ g = .inl .recur ∨ g = .inr (3, 0) ∨ g = .inr (4, 0) := by
  constructor
  · rintro ⟨rule, hrule, largs, hl⟩
    rcases mem_uCondRules hrule with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [uIzZero, uIzSucc, uPred, uRecZ1, uRecZ2, uRecS1, uRecS2, Term.app.injEq] at hl <;>
      obtain ⟨rfl, -⟩ := hl <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨uIzZero, by simp [uCondRules], _, rfl⟩
    · exact ⟨uPred, by simp [uCondRules], _, rfl⟩
    · exact ⟨uRecZ1, by simp [uCondRules], _, rfl⟩
    · exact ⟨uRecZ2, by simp [uCondRules], _, rfl⟩
    · exact ⟨uRecS2, by simp [uCondRules], _, rfl⟩

theorem uCondRules_vars : ∀ rule ∈ uCondRules, Term.vars rule.rhs ⊆ Term.vars rule.lhs := by
  intro rule hrule x hx
  rcases mem_uCondRules hrule with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [uIzZero, uIzSucc, uPred, uRecZ1, uRecZ2, uRecS1, uRecS2] at hx ⊢ <;> omega

/-- The witness algebra on the unraveled signature: `condBase` on the original symbols and
`U(c, b, s, n) = b` on the fresh symbols; `recur♯(b, s, n) = 2n + 1` and
`U₄♯(c, b, s, n) = 2 min(c, 1) + 2 (n ∸ 1)`, written with truncated subtraction. -/
def uWitnessAlg : MarkedAlgebra (USym CSym) where
  base := fun
    | .inl f, xs => condBase f xs
    | .inr _, xs => xs.getD 1 0
  marked := fun
    | .inl .recur, xs => 2 * xs.getD 2 0 + 1
    | .inr p, xs => if p = (4, 0) then 2 * (xs.getD 0 0 - (xs.getD 0 0 - 1)) + 2 * (xs.getD 3 0 - 1)
        else 0
    | .inl _, _ => 0

/-- Native data: a weakly monotone algebra over `ℕ` with marked symbols on the signature of
`U(R)`, the certificate of termination of the unraveling by dependency pairs. -/
abbrev operationalTerminationCTRSData : Type := MarkedAlgebra (USym CSym)

/-- Lucas, Marché and Meseguer (Operational termination of conditional term rewriting systems,
IPL 95(4), 2005; Definition of operational termination restated in Lucas and Meseguer 2014,
Section 2), with the unraveling of Ohlebusch (2002, Definition 7.2.48): the certificate is a
reduction pair of an algebra that is weakly monotone and orients every rule of `U(R)` weakly
(Arts and Giesl 2000). -/
def operationalTerminationCTRSLaws (M : operationalTerminationCTRSData) : Prop :=
  AlgMono M.base ∧ AlgMono M.marked ∧ AlgTRSWeak M.base (unravel condRecursor)

/-- Every dependency pair of `U(R)` strictly decreases: `U(R)` terminates. -/
def operationalTerminationCTRSAccepts (M : operationalTerminationCTRSData) : Prop :=
  AlgPairsStrict M (unravel condRecursor)

/-- Verdict: escape. -/
def operationalTerminationCTRSResult (M : operationalTerminationCTRSData) : Prop :=
  operationalTerminationCTRSAccepts M ∧ OperationallyTerminating condRecursor

/-- Soundness: termination of the unraveling, certified by the reduction pair, gives
operational termination of the deterministic conditional system. -/
theorem operationalTerminationCTRS_sound :
    ∀ M, operationalTerminationCTRSLaws M → operationalTerminationCTRSAccepts M →
      OperationallyTerminating condRecursor := by
  intro M hL hA
  have hvars : ∀ rule ∈ unravel condRecursor, Term.vars rule.rhs ⊆ Term.vars rule.lhs := by
    rw [unravel_condRecursor]
    exact uCondRules_vars
  have hsn := sn_of_markedAlgebra M (unravel condRecursor) hvars hL.1 hL.2.1 hL.2.2 hA
  exact operationallyTerminating_of_unravel condRecursor fun s => hsn _

def operationalTerminationCTRSWitness : operationalTerminationCTRSData := uWitnessAlg

theorem uWitness_base_mono : AlgMono uWitnessAlg.base := by
  intro f xs ys h
  rcases f with f | p
  · exact condBase_mono f xs ys h
  · exact getD_le_of_forall₂ h 1

theorem uWitness_marked_mono : AlgMono uWitnessAlg.marked := by
  intro f xs ys h
  have h0 := getD_le_of_forall₂ h 0
  have h2 := getD_le_of_forall₂ h 2
  have h3 := getD_le_of_forall₂ h 3
  rcases f with f | p
  · cases f <;> simp only [uWitnessAlg] <;> omega
  · simp only [uWitnessAlg]
    split_ifs <;> omega

theorem uWitness_rulesWeak : AlgTRSWeak uWitnessAlg.base uCondRules := by
  intro rule hrule α
  rcases mem_uCondRules hrule with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [uIzZero, uIzSucc, uPred, uRecZ1, uRecZ2, uRecS1, uRecS2, evalT_app, uWitnessAlg,
      condBase]

theorem operationalTerminationCTRSWitness_laws :
    operationalTerminationCTRSLaws operationalTerminationCTRSWitness := by
  refine ⟨uWitness_base_mono, uWitness_marked_mono, ?_⟩
  rw [unravel_condRecursor]
  exact uWitness_rulesWeak

theorem uWitness_pairsStrict : AlgPairsStrict uWitnessAlg uCondRules := by
  intro rule hrule f largs hl g targs hsub hdef α
  rw [uCondRules_defined_iff] at hdef
  have hm := mem_subtermsT_of_isSubterm hsub
  rcases mem_uCondRules hrule with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [uIzZero, subtermsT, subtermsL] at hm
    obtain ⟨rfl, -⟩ := hm
    simp at hdef
  · simp [uIzSucc, subtermsT, subtermsL] at hm
    obtain ⟨rfl, -⟩ := hm
    simp at hdef
  · simp [uPred, subtermsT] at hm
  · simp only [uRecZ1, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    simp [uRecZ1, subtermsT, subtermsL] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [uWitnessAlg, evalT_app, condBase]
  · simp [uRecZ2, subtermsT] at hm
  · simp only [uRecS1, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    simp [uRecS1, subtermsT, subtermsL] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [uWitnessAlg, evalT_app, condBase]
      omega
    · simp [uWitnessAlg, condBase]
  · simp only [uRecS2, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    simp [uRecS2, subtermsT, subtermsL] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp at hdef
    · simp [uWitnessAlg, evalT_app, condBase]
      omega
    · simp [uWitnessAlg, evalT_app, condBase]

theorem operationalTerminationCTRSWitness_result :
    operationalTerminationCTRSResult operationalTerminationCTRSWitness := by
  have hA : operationalTerminationCTRSAccepts operationalTerminationCTRSWitness := by
    show AlgPairsStrict uWitnessAlg (unravel condRecursor)
    rw [unravel_condRecursor]
    exact uWitness_pairsStrict
  exact ⟨hA, operationalTerminationCTRS_sound _ operationalTerminationCTRSWitness_laws hA⟩

/-- Live conditions against the unconditional specialization: the conditions select the rule
(both truth values occur), and dropping them makes the recursive rule loop, while the
conditional system is operationally terminating. -/
theorem operationalTerminationCTRSWitness_feature :
    ((CStep condRecursor (rC zC zC zC) zC ∧
        ¬ CStep condRecursor (rC zC zC zC) (wC zC (rC zC zC (pC zC)))) ∧
      (CStep condRecursor (rC zC zC (sC zC)) (wC zC (rC zC zC (pC (sC zC)))) ∧
        ¬ CStep condRecursor (rC zC zC (sC zC)) zC)) ∧
    ¬ SN (uncond condRecursor) (rC zC zC zC) ∧ OperationallyTerminating condRecursor :=
  ⟨condRecursor_live, uncond_condRecursor_not_sn,
    operationalTerminationCTRSWitness_result.2⟩

/-- The witness with the counter coefficient of `recur♯` set to `0`. -/
def uBlindAlg : MarkedAlgebra (USym CSym) :=
  { uWitnessAlg with
    marked := fun
      | .inl .recur, _ => 0
      | .inr p, xs => if p = (4, 0) then
          2 * (xs.getD 0 0 - (xs.getD 0 0 - 1)) + 2 * (xs.getD 3 0 - 1) else 0
      | .inl _, _ => 0 }

/-- Reading no counter in `recur♯` keeps the laws and loses the strict pairs: the pair
`recur♯(b, s, n) → U₃♯(isZero(n), b, s, n)` no longer decreases. -/
theorem operationalTerminationCTRS_mutation :
    operationalTerminationCTRSLaws uBlindAlg ∧ ¬ operationalTerminationCTRSAccepts uBlindAlg := by
  refine ⟨⟨uWitness_base_mono, ?_, ?_⟩, fun h => ?_⟩
  · intro f xs ys h
    have h0 := getD_le_of_forall₂ h 0
    have h3 := getD_le_of_forall₂ h 3
    rcases f with f | p
    · cases f <;> simp only [uBlindAlg] <;> omega
    · simp only [uBlindAlg]
      split_ifs <;> omega
  · rw [unravel_condRecursor]
    exact uWitness_rulesWeak
  · have hA : AlgPairsStrict uBlindAlg uCondRules := by
      rw [← unravel_condRecursor]
      exact h
    have := hA uRecZ1 (by simp [uCondRules]) (.inl .recur) [.var 0, .var 1, .var 2] rfl
      (.inr (3, 0)) [.app (.inl .isZero) [.var 2], .var 0, .var 1, .var 2] (IsSubterm.refl _)
      ((uCondRules_defined_iff _).2 (by simp)) (fun _ => 0)
    simp [uBlindAlg] at this

/-! ## Positions of argument lists, subterm lifting, integer evaluation -/

section Positions

variable {α : Type u}

theorem argStepOf_getElem? {S : α → α → Prop} {xs ys : List α} (h : ArgStepOf S xs ys)
    (i : Nat) (y : α) (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ Relation.ReflTransGen S x y := by
  obtain ⟨pre, post, a, b, rfl, rfl, hab⟩ := h
  rcases lt_trichotomy i pre.length with hi | hi | hi
  · rw [List.getElem?_append_left hi] at hy ⊢
    exact ⟨y, hy, .refl⟩
  · subst hi
    rw [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero] at hy ⊢
    cases hy
    exact ⟨a, rfl, .single hab⟩
  · rw [List.getElem?_append_right hi.le] at hy ⊢
    obtain ⟨k, hk⟩ : ∃ k, i - pre.length = k + 1 := ⟨i - pre.length - 1, by omega⟩
    rw [hk, List.getElem?_cons_succ] at hy ⊢
    exact ⟨y, hy, .refl⟩

theorem argStepsOf_getElem? {S : α → α → Prop} {xs ys : List α}
    (h : Relation.ReflTransGen (ArgStepOf S) xs ys) (i : Nat) :
    ∀ y, ys[i]? = some y → ∃ x, xs[i]? = some x ∧ Relation.ReflTransGen S x y := by
  induction h with
  | refl => exact fun y hy => ⟨y, hy, .refl⟩
  | tail _ hstep ih =>
    intro y hy
    obtain ⟨m, hm, hmy⟩ := argStepOf_getElem? hstep i y hy
    obtain ⟨x, hx, hxm⟩ := ih m hm
    exact ⟨x, hx, hxm.trans hmy⟩

theorem rtg_eq_of_nf' {r : α → α → Prop} {a b : α} (ha : ∀ u, ¬ r a u)
    (h : Relation.ReflTransGen r a b) : b = a := by
  rcases Relation.ReflTransGen.cases_head h with h0 | ⟨c, hac, -⟩
  · exact h0.symm
  · exact absurd hac (ha c)

theorem no_argStepOf_of_nf' {S : α → α → Prop} {xs ys : List α}
    (h : ∀ x ∈ xs, ∀ u, ¬ S x u) : ¬ ArgStepOf S xs ys := by
  rintro ⟨pre, post, a, b, rfl, -, hab⟩
  exact h a (by simp) b hab

theorem argStepsOf_cons_nf' {S : α → α → Prop} {a : α} (ha : ∀ u, ¬ S a u)
    {rest ys : List α} (h : Relation.ReflTransGen (ArgStepOf S) (a :: rest) ys) :
    ∃ rest', ys = a :: rest' ∧ Relation.ReflTransGen (ArgStepOf S) rest rest' := by
  induction h with
  | refl => exact ⟨rest, rfl, .refl⟩
  | tail _ hst ih =>
    obtain ⟨rest', rfl, hr⟩ := ih
    rcases (argStepOf_cons_iff a rest' _).1 hst with ⟨b, hab, -⟩ | ⟨rest'', hrr, rfl⟩
    · exact absurd hab (ha b)
    · exact ⟨rest'', rfl, hr.tail hrr⟩

theorem argSteps_head_only' {S : α → α → Prop} {a : α} {rest : List α}
    (hrest : ∀ x ∈ rest, ∀ u, ¬ S x u) {ys : List α}
    (h : Relation.ReflTransGen (ArgStepOf S) (a :: rest) ys) :
    ∃ y, ys = y :: rest ∧ Relation.ReflTransGen S a y := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | tail _ hst ih =>
    obtain ⟨y, rfl, hy⟩ := ih
    rcases (argStepOf_cons_iff y rest _).1 hst with ⟨y', hyy', rfl⟩ | ⟨rest', hrr, -⟩
    · exact ⟨y', rfl, hy.tail hyy'⟩
    · exact absurd hrr (no_argStepOf_of_nf' hrest)

end Positions

section CtxLift

variable {sigma : Type u} {nu : Type v}

theorem ctxStep_lift_subterm {Root : Term sigma nu → Term sigma nu → Prop}
    {u t : Term sigma nu} (h : IsSubterm u t) :
    ∀ {w}, CtxStep Root u w → ∃ t', CtxStep Root t t' ∧ IsSubterm w t' := by
  induction h with
  | refl =>
    intro w hw
    exact ⟨w, hw, .refl w⟩
  | arg f args hmem _ ih =>
    intro w hw
    obtain ⟨a', ha', hsub⟩ := ih hw
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
    exact ⟨.app f (pre ++ a' :: post), CtxStep.arg f pre post ha', .arg f _ (by simp) hsub⟩

theorem ctxStep_mono {Root Root' : Term sigma nu → Term sigma nu → Prop}
    (h : ∀ s t, Root s t → Root' s t) {s t : Term sigma nu} (hst : CtxStep Root s t) :
    CtxStep Root' s t := by
  induction hst with
  | root hr => exact CtxStep.root (h _ _ hr)
  | arg f pre post _ ih => exact CtxStep.arg f pre post ih

mutual
/-- Evaluation of a term in an algebra over `ℤ`. -/
def zevalT (A : sigma → List Int → Int) (w : nu → Int) : Term sigma nu → Int
  | .var x => w x
  | .app f args => A f (zevalL A w args)
/-- Evaluation of an argument list over `ℤ`. -/
def zevalL (A : sigma → List Int → Int) (w : nu → Int) : List (Term sigma nu) → List Int
  | [] => []
  | a :: as => zevalT A w a :: zevalL A w as
end

theorem zevalL_eq_map (A : sigma → List Int → Int) (w : nu → Int) :
    ∀ args : List (Term sigma nu), zevalL A w args = args.map (zevalT A w)
  | [] => rfl
  | a :: as => by simp [zevalL, zevalL_eq_map A w as]

theorem zevalT_app (A : sigma → List Int → Int) (w : nu → Int) (f : sigma)
    (args : List (Term sigma nu)) : zevalT A w (.app f args) = A f (args.map (zevalT A w)) := by
  simp [zevalT, zevalL_eq_map]

end CtxLift

/-! ## Integer term rewriting -/

/-- The predefined symbols of integer term rewriting (Fuhs, Giesl, Plücker, Schneider-Kamp and
Falke, Proving Termination of Integer Term Rewriting, RTA 2009, LNCS 5595, Definition 1): the
integers, the Booleans, `ArithOp = {+, −, ∗, /, %}`, `RelOp = {>, ⩾, <, ⩽, ==, !=}` and
`BoolOp = {∧, ⇒}`. -/
inductive IntSym where
  | lit (n : Int)
  | tt
  | ff
  | add
  | sub
  | mul
  | div
  | mod
  | gt
  | ge
  | lt
  | le
  | eq
  | ne
  | and
  | imp
  deriving DecidableEq

/-- The predefined rules `n ∘ m → q` of `PD` (Definition 1); `t / 0` and `t % 0` are normal
forms, and division and remainder truncate. -/
def pdEval : IntSym → IntSym → IntSym → Option IntSym
  | .add, .lit n, .lit m => some (.lit (n + m))
  | .sub, .lit n, .lit m => some (.lit (n - m))
  | .mul, .lit n, .lit m => some (.lit (n * m))
  | .div, .lit n, .lit m => if m = 0 then none else some (.lit (n.tdiv m))
  | .mod, .lit n, .lit m => if m = 0 then none else some (.lit (n.tmod m))
  | .gt, .lit n, .lit m => some (if m < n then .tt else .ff)
  | .ge, .lit n, .lit m => some (if m ≤ n then .tt else .ff)
  | .lt, .lit n, .lit m => some (if n < m then .tt else .ff)
  | .le, .lit n, .lit m => some (if n ≤ m then .tt else .ff)
  | .eq, .lit n, .lit m => some (if n = m then .tt else .ff)
  | .ne, .lit n, .lit m => some (if n = m then .ff else .tt)
  | .and, .tt, .tt => some .tt
  | .and, .tt, .ff => some .ff
  | .and, .ff, .tt => some .ff
  | .and, .ff, .ff => some .ff
  | .imp, .tt, .tt => some .tt
  | .imp, .tt, .ff => some .ff
  | .imp, .ff, .tt => some .tt
  | .imp, .ff, .ff => some .tt
  | _, _, _ => none

section ITRS

variable {F : Type} {nu : Type}

/-- Symbols of an ITRS: the user signature `F` and the predefined symbols. -/
abbrev ISym (F : Type) : Type := F ⊕ IntSym

/-- A predefined constant (an integer or a Boolean) as a term. -/
def iconst (k : IntSym) : Term (ISym F) nu := .app (.inr k) []

/-- The rules of `PD` at the root. -/
def PDRoot (s t : Term (ISym F) nu) : Prop :=
  ∃ o a b q, pdEval o a b = some q ∧ s = .app (.inr o) [iconst a, iconst b] ∧ t = iconst q

/-- Root steps of `R ∪ PD`. -/
def FullRoot (R : TRS (ISym F) nu) (s t : Term (ISym F) nu) : Prop :=
  rootStep R s t ∨ PDRoot s t

/-- Normal forms of `R ∪ PD`. -/
def INF (R : TRS (ISym F) nu) (t : Term (ISym F) nu) : Prop :=
  ∀ u, ¬ CtxStep (FullRoot R) t u

/-- Innermost root steps of `R ∪ PD`: the arguments of the redex are normal forms. -/
def InnerRoot (R : TRS (ISym F) nu) (s t : Term (ISym F) nu) : Prop :=
  (∃ f args, s = .app f args ∧ ∀ a ∈ args, INF R a) ∧ FullRoot R s t

/-- The rewrite relation `↪_R = →ⁱ_{R ∪ PD}` of an ITRS (Definition 1). -/
abbrev IStep (R : TRS (ISym F) nu) : Term (ISym F) nu → Term (ISym F) nu → Prop :=
  CtxStep (InnerRoot R)

/-- Left-hand sides are rooted by user symbols (Definition 1: `ℓ ∉ ℤ ∪ 𝔹` and `ℓ` contains no
predefined operation, so its root is in `F`). -/
def UserRooted (R : TRS (ISym F) nu) : Prop :=
  ∀ rule ∈ R, ∃ f largs, rule.lhs = .app (.inl f) largs

theorem not_rootStep_inr {R : TRS (ISym F) nu} (hU : UserRooted R) (k : IntSym)
    (args : List (Term (ISym F) nu)) (u : Term (ISym F) nu) :
    ¬ rootStep R (.app (.inr k) args) u := by
  rintro ⟨rule, hrule, σ, hl, -⟩
  obtain ⟨f, largs, hf⟩ := hU rule hrule
  rw [hf, Subst.apply_app] at hl
  simp at hl

theorem not_ctxStep_iconst {R : TRS (ISym F) nu} (hU : UserRooted R) (k : IntSym)
    (u : Term (ISym F) nu) : ¬ CtxStep (FullRoot R) (iconst k) u := by
  intro h
  rcases (ctxStep_app_iff (FullRoot R) (.inr k) [] u).1 h with hr | ⟨ys, hys, -⟩
  · rcases hr with hr | ⟨o, a, b, q, -, hs, -⟩
    · exact not_rootStep_inr hU k [] u hr
    · simp at hs
  · exact not_argStepOf_nil ys hys

theorem iconst_inf {R : TRS (ISym F) nu} (hU : UserRooted R) (k : IntSym) :
    INF R (iconst k) :=
  not_ctxStep_iconst hU k

theorem istep_full {R : TRS (ISym F) nu} {s t : Term (ISym F) nu} (h : IStep R s t) :
    CtxStep (FullRoot R) s t :=
  ctxStep_mono (fun _ _ hr => hr.2) h

theorem rsn_iconst {R : TRS (ISym F) nu} (hU : UserRooted R) (k : IntSym) :
    RSN (InnerRoot R) (iconst k) :=
  Acc.intro _ fun u h => absurd (istep_full h) (not_ctxStep_iconst hU k u)

theorem rsn_app_inr {R : TRS (ISym F) nu} (hU : UserRooted R) (k : IntSym) :
    ∀ args : List (Term (ISym F) nu), (∀ a ∈ args, RSN (InnerRoot R) a) →
      RSN (InnerRoot R) (.app (.inr k) args) :=
  rsn_app_of_root fun xs u _ hr => by
    rcases hr.2 with h | ⟨o, a, b, q, -, -, rfl⟩
    · exact absurd h (not_rootStep_inr hU k xs u)
    · exact rsn_iconst hU q

theorem rsn_app_inl_undefined {R : TRS (ISym F) nu} {g : F} (hg : ¬ IsDefined R (.inl g)) :
    ∀ args : List (Term (ISym F) nu), (∀ a ∈ args, RSN (InnerRoot R) a) →
      RSN (InnerRoot R) (.app (.inl g) args) :=
  rsn_app_of_root fun xs u _ hr => by
    rcases hr.2 with h | ⟨o, a, b, q, -, hs, -⟩
    · exact absurd h (not_rootStep_of_not_defined hg xs u)
    · simp at hs

/-- An instance is terminating when the instantiated variables and every instantiated call of a
defined user symbol below it are. -/
theorem rsn_subst_itrs [DecidableEq nu] {R : TRS (ISym F) nu} (hU : UserRooted R)
    (σ : Subst (ISym F) nu) :
    ∀ w : Term (ISym F) nu, (∀ x ∈ Term.vars w, RSN (InnerRoot R) (σ x)) →
      (∀ g targs, IsSubterm (.app (.inl g) targs) w → IsDefined R (.inl g) →
        (∀ a ∈ Subst.applyList σ targs, RSN (InnerRoot R) a) →
          RSN (InnerRoot R) (.app (.inl g) (Subst.applyList σ targs))) →
      RSN (InnerRoot R) (Subst.apply σ w) := by
  intro w
  induction w using Term.rec' with
  | hvar x =>
    intro hv _
    simpa using hv x (by simp)
  | happ g targs ih =>
    intro hv hc
    have hargs : ∀ a ∈ Subst.applyList σ targs, RSN (InnerRoot R) a := by
      intro a ha
      rw [Subst.applyList_eq_map, List.mem_map] at ha
      obtain ⟨t, ht, rfl⟩ := ha
      refine ih t ht (fun x hx => hv x ?_) (fun g' targs' hsub hdef hargs' =>
        hc g' targs' (IsSubterm.arg g targs ht hsub) hdef hargs')
      rw [Term.vars_app, Term.mem_varsList_iff]
      exact ⟨t, ht, hx⟩
    rw [Subst.apply_app]
    rcases g with g | k
    · by_cases hg : IsDefined R (.inl g)
      · exact hc g targs (IsSubterm.refl _) hg hargs
      · exact rsn_app_inl_undefined hg _ hargs
    · exact rsn_app_inr hU k _ hargs

/-- Dependency pairs of an ITRS (Definition 2) as edges between calls, with the innermost
condition of chains: from an instance of a left-hand side whose arguments are normal forms to an
instantiated subterm of the right-hand side headed by a defined user symbol. -/
def IPair (R : TRS (ISym F) nu) (c d : Call (ISym F) nu) : Prop :=
  (∀ a ∈ c.2, INF R a) ∧ ∃ rule ∈ R, ∃ σ : Subst (ISym F) nu,
    Term.app c.1 c.2 = Subst.apply σ rule.lhs ∧ ∃ g targs,
      IsSubterm (.app (.inl g) targs) rule.rhs ∧ IsDefined R (.inl g) ∧
        d = (.inl g, Subst.applyList σ targs)

/-- The dependency-pair criterion for ITRSs (Corollary 3, direction "if"): without infinite
minimal chains the ITRS terminates. -/
theorem itrs_terminating_of_chains [DecidableEq nu] (R : TRS (ISym F) nu) (hU : UserRooted R)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs)
    (hwf : WellFounded (fun d c => MinChainOf (InnerRoot R) (IPair R) c d)) :
    ∀ t, RSN (InnerRoot R) t := by
  refine rsn_of_minChainOf_wf (InnerRoot R) (IPair R) ?_ ?_ hwf
  · rintro x u ⟨⟨f, args, h, -⟩, -⟩
    exact Term.noConfusion h
  · intro f xs u hr hxs hcall
    obtain ⟨⟨f', args', hfa, hnf⟩, hfull⟩ := hr
    simp only [Term.app.injEq] at hfa
    obtain ⟨rfl, rfl⟩ := hfa
    rcases hfull with ⟨rule, hrule, σ, hl, rfl⟩ | ⟨o, a, b, q, -, -, rfl⟩
    · refine rsn_subst_itrs hU σ rule.rhs (fun x hx => ?_) (fun g targs hsub hdef hargs =>
        hcall (.inl g, Subst.applyList σ targs) ⟨hnf, rule, hrule, σ, hl, g, targs, hsub, hdef, rfl⟩
          hargs)
      obtain ⟨g0, largs, hg0⟩ := lhs_eq_app rule
      have hl' := hl
      rw [hg0, Subst.apply_app] at hl'
      simp only [Term.app.injEq] at hl'
      obtain ⟨-, rfl⟩ := hl'
      have hxl := hvars rule hrule hx
      rw [hg0, Term.vars_app, Term.mem_varsList_iff] at hxl
      obtain ⟨a, ha, hxa⟩ := hxl
      have hmem : Subst.apply σ a ∈ Subst.applyList σ largs := by
        rw [Subst.applyList_eq_map]
        exact List.mem_map_of_mem ha
      exact rsn_of_isSubterm (isSubterm_subst_var σ a x hxa) (hxs _ hmem)
    · exact rsn_iconst hU q

/-- A dependency-pair problem: a list of pairs of calls `s♯ → t♯`. -/
abbrev IProblem (F : Type) (nu : Type) := List (Call (ISym F) nu × Call (ISym F) nu)

/-- The edge of a pair instance whose source arguments are normal forms. -/
def PEdge (R : TRS (ISym F) nu) (P : IProblem F nu) (c d : Call (ISym F) nu) : Prop :=
  (∀ a ∈ c.2, INF R a) ∧ ∃ p ∈ P, ∃ σ : Subst (ISym F) nu,
    c = (p.1.1, Subst.applyList σ p.1.2) ∧ d = (p.2.1, Subst.applyList σ p.2.2)

/-- Minimal innermost chains of a problem. -/
abbrev IChain (R : TRS (ISym F) nu) (P : IProblem F nu) :
    Call (ISym F) nu → Call (ISym F) nu → Prop :=
  MinChainOf (InnerRoot R) (PEdge R P)

/-- An integer max-polynomial interpretation, read as functions: `pol` on `F ∪ F_int`, `tup` on
the tuple symbols, and the value of the fresh constant `c` of the reduction pair processor. -/
structure IInterp (F : Type) where
  pol : ISym F → List Int → Int
  tup : F → List Int → Int
  bound : Int

/-- The value of a marked call. -/
def icallVal (M : IInterp F) (w : nu → Int) (c : Call (ISym F) nu) : Int :=
  match c.1 with
  | .inl f => M.tup f (c.2.map (zevalT M.pol w))
  | .inr _ => 0

/-- An I-interpretation (Definition 5): integers, `+`, `−`, `∗`, `%` and `/` are interpreted as
fixed. -/
def IInterpretation (M : IInterp F) : Prop :=
  (∀ n : Int, M.pol (.inr (.lit n)) [] = n) ∧
    (∀ a b : Int, M.pol (.inr .add) [a, b] = a + b) ∧
    (∀ a b : Int, M.pol (.inr .sub) [a, b] = a - b) ∧
    (∀ a b : Int, M.pol (.inr .mul) [a, b] = a * b) ∧
    (∀ a b : Int, M.pol (.inr .mod) [a, b] = |a|) ∧
    (∀ a b : Int, M.pol (.inr .div) [a, b] = |a| - min (|b| - 1) |a|)

/-- `σ ⊨ t = u'` for some pair `u → v` of `P` (Definition 7): the instantiated right side
reduces to an instantiated left side of `P` in normal form. -/
def Connects (R : TRS (ISym F) nu) (P : IProblem F nu) (d : Call (ISym F) nu) : Prop :=
  ∃ q ∈ P, ∃ σ' : Subst (ISym F) nu, d.1 = q.1.1 ∧
    Relation.ReflTransGen (ArgStepOf (IStep R)) d.2 (Subst.applyList σ' q.1.2) ∧
      ∀ a ∈ Subst.applyList σ' q.1.2, INF R a

/-- `s → t ∈ P≿` (Theorem 8). -/
def PWeak (R : TRS (ISym F) nu) (P : IProblem F nu) (M : IInterp F)
    (p : Call (ISym F) nu × Call (ISym F) nu) : Prop :=
  ∀ σ : Subst (ISym F) nu, (∀ a ∈ Subst.applyList σ p.1.2, INF R a) →
    Connects R P (p.2.1, Subst.applyList σ p.2.2) → ∀ w : nu → Int,
      icallVal M w (p.2.1, Subst.applyList σ p.2.2) ≤ icallVal M w (p.1.1, Subst.applyList σ p.1.2)

/-- `s → t ∈ P≻` (Theorem 8). -/
def PStrict (R : TRS (ISym F) nu) (P : IProblem F nu) (M : IInterp F)
    (p : Call (ISym F) nu × Call (ISym F) nu) : Prop :=
  ∀ σ : Subst (ISym F) nu, (∀ a ∈ Subst.applyList σ p.1.2, INF R a) →
    Connects R P (p.2.1, Subst.applyList σ p.2.2) → ∀ w : nu → Int,
      icallVal M w (p.2.1, Subst.applyList σ p.2.2) < icallVal M w (p.1.1, Subst.applyList σ p.1.2)

/-- `s → t ∈ P_bound` (Theorem 8): `s ≿ c` for the fresh constant `c`. -/
def PBound (R : TRS (ISym F) nu) (P : IProblem F nu) (M : IInterp F)
    (p : Call (ISym F) nu × Call (ISym F) nu) : Prop :=
  ∀ σ : Subst (ISym F) nu, (∀ a ∈ Subst.applyList σ p.1.2, INF R a) →
    Connects R P (p.2.1, Subst.applyList σ p.2.2) → ∀ w : nu → Int,
      M.bound ≤ icallVal M w (p.1.1, Subst.applyList σ p.1.2)

/-- The usable-rules and properness conditions of Theorem 8 in their semantic form (footnote
13): reductions of the arguments of an instantiated right side of `P` weakly decrease its
value. -/
def RhsWeak (R : TRS (ISym F) nu) (P : IProblem F nu) (M : IInterp F) : Prop :=
  ∀ p ∈ P, ∀ σ : Subst (ISym F) nu, (∀ a ∈ Subst.applyList σ p.1.2, INF R a) →
    ∀ xs, Relation.ReflTransGen (ArgStepOf (IStep R)) (Subst.applyList σ p.2.2) xs →
      ∀ w : nu → Int,
        icallVal M w (p.2.1, xs) ≤ icallVal M w (p.2.1, Subst.applyList σ p.2.2)

/-- The conditional reduction pair processor for ITRSs (Theorem 8), read on minimal chains: if
every pair is weakly decreasing, the pairs outside `P₁` are strictly decreasing and the pairs
outside `P₂` are bounded, then chains of `P` are finite once chains of `P₁ ⊇ P \ P≻` and of
`P₂ ⊇ P \ P_bound` are. -/
theorem wf_iChain_of_processor (R : TRS (ISym F) nu) (P P1 P2 : IProblem F nu) (M : IInterp F)
    (hweak : ∀ p ∈ P, PWeak R P M p) (hstrict : ∀ p ∈ P, p ∉ P1 → PStrict R P M p)
    (hbound : ∀ p ∈ P, p ∉ P2 → PBound R P M p) (hrhs : RhsWeak R P M)
    (hwf1 : WellFounded (fun d c => IChain R P1 c d))
    (hwf2 : WellFounded (fun d c => IChain R P2 c d)) :
    WellFounded (fun d c => IChain R P c d) := by
  classical
  let μ : Call (ISym F) nu → Int := fun c => icallVal M (fun _ => 0) c
  let T : Call (ISym F) nu → Prop := fun d => ∃ p ∈ P, ∃ σ : Subst (ISym F) nu,
    (∀ a ∈ Subst.applyList σ p.1.2, INF R a) ∧ d = (p.2.1, Subst.applyList σ p.2.2)
  have hT : ∀ c d, IChain R P c d → T d := by
    rintro c d ⟨-, -, xs, -, hnf, p, hp, σ, hsrc, hd⟩
    have hxs : xs = Subst.applyList σ p.1.2 := (Prod.ext_iff.1 hsrc).2
    exact ⟨p, hp, σ, hxs ▸ hnf, hd⟩
  have hedge : ∀ c d, T c → IChain R P c d → (∃ e, IChain R P d e) →
      μ d ≤ μ c ∧ (IChain R P1 c d ∨ μ d < μ c) ∧ (IChain R P2 c d ∨ M.bound ≤ μ c) := by
    rintro c d ⟨p0, hp0, σ0, hnf0, rfl⟩ ⟨hcSN, hdSN, xs, hreach, hnf, p, hp, σ, hsrc, rfl⟩
      ⟨e, -, -, ys, hreach', hnf', q, hq, σ', hsrc', -⟩
    have hxs : xs = Subst.applyList σ p.1.2 := (Prod.ext_iff.1 hsrc).2
    have hsym : p0.2.1 = p.1.1 := (Prod.ext_iff.1 hsrc).1
    have hys : ys = Subst.applyList σ' q.1.2 := (Prod.ext_iff.1 hsrc').2
    have hd1 : p.2.1 = q.1.1 := (Prod.ext_iff.1 hsrc').1
    have hconn : Connects R P (p.2.1, Subst.applyList σ p.2.2) :=
      ⟨q, hq, σ', hd1, hys ▸ hreach', hys ▸ hnf'⟩
    have hnfσ : ∀ a ∈ Subst.applyList σ p.1.2, INF R a := hxs ▸ hnf
    have h1 : μ (p0.2.1, xs) ≤ μ (p0.2.1, Subst.applyList σ0 p0.2.2) :=
      hrhs p0 hp0 σ0 hnf0 xs hreach (fun _ => 0)
    have hsrcμ : μ (p0.2.1, xs) = μ (p.1.1, Subst.applyList σ p.1.2) := by
      rw [hsym, hxs]
    have hw := hweak p hp σ hnfσ hconn (fun _ => 0)
    refine ⟨?_, ?_, ?_⟩
    · show μ (p.2.1, Subst.applyList σ p.2.2) ≤ μ (p0.2.1, Subst.applyList σ0 p0.2.2)
      have : μ (p.2.1, Subst.applyList σ p.2.2) ≤ μ (p.1.1, Subst.applyList σ p.1.2) := hw
      omega
    · by_cases hp1 : p ∈ P1
      · exact Or.inl ⟨hcSN, hdSN, xs, hreach, hnf, p, hp1, σ, hsrc, rfl⟩
      · have hs := hstrict p hp hp1 σ hnfσ hconn (fun _ => 0)
        have hs' : μ (p.2.1, Subst.applyList σ p.2.2) < μ (p.1.1, Subst.applyList σ p.1.2) := hs
        right
        show μ (p.2.1, Subst.applyList σ p.2.2) < μ (p0.2.1, Subst.applyList σ0 p0.2.2)
        omega
    · by_cases hp2 : p ∈ P2
      · exact Or.inl ⟨hcSN, hdSN, xs, hreach, hnf, p, hp2, σ, hsrc, rfl⟩
      · have hb := hbound p hp hp2 σ hnfσ hconn (fun _ => 0)
        have hb' : M.bound ≤ μ (p.1.1, Subst.applyList σ p.1.2) := hb
        right
        show M.bound ≤ μ (p0.2.1, Subst.applyList σ0 p0.2.2)
        omega
  have hterminal : ∀ d, (¬ ∃ e, IChain R P d e) → Acc (fun d c => IChain R P c d) d :=
    fun d hd => Acc.intro d fun e he => absurd ⟨e, he⟩ hd
  have L0 : ∀ c, Acc (fun d c => IChain R P2 c d) c → T c → μ c < M.bound →
      Acc (fun d c => IChain R P c d) c := by
    intro c hc
    induction hc with
    | intro c _ ih =>
      intro hTc hlt
      refine Acc.intro c fun d hcd => ?_
      by_cases hcont : ∃ e, IChain R P d e
      · obtain ⟨hle, -, h2⟩ := hedge c d hTc hcd hcont
        rcases h2 with h2 | h2
        · exact ih d h2 (hT c d hcd) (lt_of_le_of_lt hle hlt)
        · exact absurd h2 (not_le.2 hlt)
      · exact hterminal d hcont
  let ν : Call (ISym F) nu → Nat := fun c => (μ c - M.bound + 1).toNat
  have hνle : ∀ c d, μ d ≤ μ c → ν d ≤ ν c := fun c d h => Int.toNat_le_toNat (by omega)
  have hνlt : ∀ c d, μ d < μ c → M.bound ≤ μ c → ν d < ν c :=
    fun c d h1 h2 => (Int.toNat_lt_toNat (by omega)).2 (by omega)
  have L1 : ∀ n, ∀ c, T c → ν c = n → Acc (fun d c => IChain R P c d) c := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      have inner : ∀ c, Acc (fun d c => IChain R P1 c d) c → T c → ν c ≤ n →
          Acc (fun d c => IChain R P c d) c := by
        intro c hc
        induction hc with
        | intro c _ ih =>
          intro hTc hν
          by_cases hlow : μ c < M.bound
          · exact L0 c (hwf2.apply c) hTc hlow
          · refine Acc.intro c fun d hcd => ?_
            by_cases hcont : ∃ e, IChain R P d e
            · obtain ⟨hle, h1, -⟩ := hedge c d hTc hcd hcont
              rcases h1 with h1 | h1
              · exact ih d h1 (hT c d hcd) (le_trans (hνle c d hle) hν)
              · exact ihn (ν d) (lt_of_lt_of_le (hνlt c d h1 (not_lt.1 hlow)) hν) d
                  (hT c d hcd) rfl
            · exact hterminal d hcont
      intro c hTc hν
      exact inner c (hwf1.apply c) hTc hν.le
  exact ⟨fun c => Acc.intro c fun d hcd => L1 (ν d) d (hT c d hcd) rfl⟩

/-- A problem with a single pair whose right side is headed differently from its left side has
no chain of length two. -/
theorem wf_iChain_single (R : TRS (ISym F) nu) (p : Call (ISym F) nu × Call (ISym F) nu)
    (hp : p.2.1 ≠ p.1.1) : WellFounded (fun d c => IChain R [p] c d) := by
  refine ⟨fun c => Acc.intro c fun d hcd => Acc.intro d fun e hde => ?_⟩
  obtain ⟨_, _, xs, _, _, p1, hp1, σ, _, hd⟩ := hcd
  obtain ⟨_, _, ys, _, _, p2, hp2, σ', hsrc, _⟩ := hde
  have e1 : p1 = p := List.mem_singleton.1 hp1
  have e2 : p2 = p := List.mem_singleton.1 hp2
  have h1 : d.1 = p1.2.1 := by rw [hd]
  have h2 : d.1 = p2.1.1 := (Prod.ext_iff.1 hsrc).1
  rw [e1] at h1
  rw [e2] at h2
  exact absurd (h1.symm.trans h2) hp

theorem no_istep_of_inf {R : TRS (ISym F) nu} {a u : Term (ISym F) nu} (h : INF R a) :
    ¬ IStep R a u :=
  fun hs => h u (istep_full hs)

theorem istep_app_inr_inv {R : TRS (ISym F) nu} (hU : UserRooted R) {k : IntSym}
    {args : List (Term (ISym F) nu)} {u : Term (ISym F) nu} (h : IStep R (.app (.inr k) args) u) :
    (∃ a b q, pdEval k a b = some q ∧ args = [iconst a, iconst b] ∧ u = iconst q) ∨
      ∃ args', ArgStepOf (IStep R) args args' ∧ u = .app (.inr k) args' := by
  rcases (ctxStep_app_iff (InnerRoot R) (.inr k) args u).1 h with hr | hargs
  · rcases hr.2 with h' | ⟨o, a, b, q, hq, hs, rfl⟩
    · exact absurd h' (not_rootStep_inr hU k args u)
    · simp only [Term.app.injEq, Sum.inr.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact Or.inl ⟨a, b, q, hq, rfl, rfl⟩
  · exact Or.inr hargs

/-- An innermost root step by a rule whose instantiated left-hand side has normal-form
arguments. -/
theorem istep_root_rule {R : TRS (ISym F) nu} {rule : Rule (ISym F) nu} (hrule : rule ∈ R)
    (σ : Subst (ISym F) nu) {f : ISym F} {args : List (Term (ISym F) nu)}
    (hl : Term.app f args = Subst.apply σ rule.lhs) (hnf : ∀ a ∈ args, INF R a) :
    IStep R (.app f args) (Subst.apply σ rule.rhs) :=
  CtxStep.root ⟨⟨f, args, rfl, hnf⟩, Or.inl ⟨rule, hrule, σ, hl, rfl⟩⟩

/-- A step of `PD` on two constants. -/
theorem istep_pd {R : TRS (ISym F) nu} (hU : UserRooted R) {o a b q : IntSym}
    (hq : pdEval o a b = some q) : IStep R (.app (.inr o) [iconst a, iconst b]) (iconst q) := by
  refine CtxStep.root ⟨⟨_, _, rfl, ?_⟩, Or.inr ⟨o, a, b, q, hq, rfl, rfl⟩⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  exacts [iconst_inf hU a, iconst_inf hU b]

/-- `a > 0` reduces to `true` only when `a` is a positive integer. -/
theorem reach_gt_tt {R : TRS (ISym F) nu} (hU : UserRooted R) {a : Term (ISym F) nu}
    (ha : INF R a)
    (h : Relation.ReflTransGen (IStep R) (.app (.inr .gt) [a, iconst (.lit 0)]) (iconst .tt)) :
    ∃ n : Int, a = iconst (.lit n) ∧ 0 < n := by
  rcases Relation.ReflTransGen.cases_head h with h0 | ⟨c, hc, hrest⟩
  · simp [iconst] at h0
  · rcases istep_app_inr_inv hU hc with ⟨a', b', q, hq, hargs, rfl⟩ | ⟨args', hargs', -⟩
    · simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, hb⟩ := hargs
      simp only [iconst, Term.app.injEq, Sum.inr.injEq, and_true] at hb
      subst hb
      have hqt := rtg_eq_of_nf' (fun u hu => no_istep_of_inf (iconst_inf hU q) hu) hrest
      simp only [iconst, Term.app.injEq, Sum.inr.injEq, and_true] at hqt
      subst hqt
      cases a'
      case lit n =>
        refine ⟨n, rfl, ?_⟩
        by_contra hn
        simp only [pdEval, if_neg hn, Option.some.injEq] at hq
        exact absurd hq (by decide)
      all_goals simp [pdEval] at hq
    · refine absurd hargs' (no_argStepOf_of_nf' ?_)
      intro x hx u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact no_istep_of_inf ha hu
      · exact no_istep_of_inf (iconst_inf hU _) hu

/-- Every reduct of `a − 1` has the value of `a` minus one under an I-interpretation. -/
theorem reach_sub_one {R : TRS (ISym F) nu} (hU : UserRooted R) {M : IInterp F}
    (hM : IInterpretation M) (w : nu → Int) {a y : Term (ISym F) nu} (ha : INF R a)
    (h : Relation.ReflTransGen (IStep R) (.app (.inr .sub) [a, iconst (.lit 1)]) y) :
    zevalT M.pol w y = zevalT M.pol w a - 1 := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, hrest⟩
  · simp [zevalT_app, iconst, hM.1, hM.2.2.1]
  · rcases istep_app_inr_inv hU hc with ⟨a', b', q, hq, hargs, rfl⟩ | ⟨args', hargs', -⟩
    · simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, hb⟩ := hargs
      simp only [iconst, Term.app.injEq, Sum.inr.injEq, and_true] at hb
      subst hb
      have hy := rtg_eq_of_nf' (fun u hu => no_istep_of_inf (iconst_inf hU q) hu) hrest
      subst hy
      cases a'
      case lit n =>
        simp only [pdEval, Option.some.injEq] at hq
        subst hq
        simp [zevalT_app, iconst, hM.1]
      all_goals simp [pdEval] at hq
    · refine absurd hargs' (no_argStepOf_of_nf' ?_)
      intro x hx u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact no_istep_of_inf ha hu
      · exact no_istep_of_inf (iconst_inf hU _) hu

end ITRS

/-! ## The integer recursor as an ITRS -/

/-- User symbols of the integer recursor. -/
inductive IUser where
  | irec
  | rif
  | wrap
  deriving DecidableEq

/-- Terms of the integer recursor. -/
abbrev ITerm : Type := Term (ISym IUser) Nat

/-- An integer literal. -/
def ilit (n : Int) : ITerm := iconst (.lit n)

/-- `rec(b, s, x) → rif(x > 0, b, s, x)`. -/
def iRecRule : Rule (ISym IUser) Nat :=
  ⟨.app (.inl .irec) [.var 0, .var 1, .var 2],
    .app (.inl .rif) [.app (.inr .gt) [.var 2, ilit 0], .var 0, .var 1, .var 2], rfl⟩

/-- `rif(true, b, s, x) → wrap(s, rec(b, s, x − 1))`. -/
def iIfTrueRule : Rule (ISym IUser) Nat :=
  ⟨.app (.inl .rif) [iconst .tt, .var 0, .var 1, .var 2],
    .app (.inl .wrap) [.var 1, .app (.inl .irec) [.var 0, .var 1, .app (.inr .sub) [.var 2, ilit 1]]],
    rfl⟩

/-- `rif(false, b, s, x) → b`. -/
def iIfFalseRule : Rule (ISym IUser) Nat :=
  ⟨.app (.inl .rif) [iconst .ff, .var 0, .var 1, .var 2], .var 0, rfl⟩

/-- The integer recursor as an ITRS, with the test `x > 0` evaluated by `PD` as in the rules
(1)–(3) of `sum` in Fuhs et al. 2009; it is the unconditional form of the conditional ITRS
`rec(b, s, x) → wrap(s, rec(b, s, x − 1)) | x > 0 →* true`,
`rec(b, s, x) → b | x > 0 →* false` (footnote 7 of the source). -/
def intRecursor : TRS (ISym IUser) Nat := [iRecRule, iIfTrueRule, iIfFalseRule]

theorem mem_intRecursor {rule : Rule (ISym IUser) Nat} (h : rule ∈ intRecursor) :
    rule = iRecRule ∨ rule = iIfTrueRule ∨ rule = iIfFalseRule := by
  simpa [intRecursor] using h

theorem intRecursor_userRooted : UserRooted intRecursor := by
  intro rule hrule
  rcases mem_intRecursor hrule with rfl | rfl | rfl
  exacts [⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩]

theorem intRecursor_vars : ∀ rule ∈ intRecursor, Term.vars rule.rhs ⊆ Term.vars rule.lhs := by
  intro rule hrule x hx
  rcases mem_intRecursor hrule with rfl | rfl | rfl <;>
    simp [iRecRule, iIfTrueRule, iIfFalseRule, ilit, iconst] at hx ⊢ <;> omega

theorem intRecursor_defined_iff (g : ISym IUser) :
    IsDefined intRecursor g ↔ g = .inl .irec ∨ g = .inl .rif := by
  constructor
  · rintro ⟨rule, hrule, largs, hl⟩
    rcases mem_intRecursor hrule with rfl | rfl | rfl <;>
      simp only [iRecRule, iIfTrueRule, iIfFalseRule, Term.app.injEq] at hl <;>
      obtain ⟨rfl, -⟩ := hl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨iRecRule, by simp [intRecursor], _, rfl⟩
    · exact ⟨iIfTrueRule, by simp [intRecursor], _, rfl⟩

/-- `REC(b, s, x) → RIF(x > 0, b, s, x)`. -/
def ip1 : Call (ISym IUser) Nat × Call (ISym IUser) Nat :=
  ((.inl .irec, [.var 0, .var 1, .var 2]),
    (.inl .rif, [.app (.inr .gt) [.var 2, ilit 0], .var 0, .var 1, .var 2]))

/-- `RIF(true, b, s, x) → REC(b, s, x − 1)`. -/
def ip2 : Call (ISym IUser) Nat × Call (ISym IUser) Nat :=
  ((.inl .rif, [iconst .tt, .var 0, .var 1, .var 2]),
    (.inl .irec, [.var 0, .var 1, .app (.inr .sub) [.var 2, ilit 1]]))

/-- The dependency pairs of the integer recursor (Definition 2). -/
def intDP : IProblem IUser Nat := [ip1, ip2]

theorem intPair_edge {c d : Call (ISym IUser) Nat} (h : IPair intRecursor c d) :
    PEdge intRecursor intDP c d := by
  obtain ⟨hnf, rule, hrule, σ, hl, g, targs, hsub, hdef, rfl⟩ := h
  refine ⟨hnf, ?_⟩
  rw [intRecursor_defined_iff] at hdef
  have hm := mem_subtermsT_of_isSubterm hsub
  rcases mem_intRecursor hrule with rfl | rfl | rfl
  · simp only [iRecRule, Subst.apply_app, Term.app.injEq] at hl
    simp [iRecRule, subtermsT, subtermsL, ilit, iconst] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨ip1, by simp [intDP], σ, Prod.ext hl.1 hl.2, rfl⟩
  · simp only [iIfTrueRule, Subst.apply_app, Term.app.injEq] at hl
    simp [iIfTrueRule, subtermsT, subtermsL, ilit, iconst] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp at hdef
    · exact ⟨ip2, by simp [intDP], σ, Prod.ext hl.1 hl.2, rfl⟩
  · simp [iIfFalseRule, subtermsT] at hm

theorem intChain_of_minChain {c d : Call (ISym IUser) Nat}
    (h : MinChainOf (InnerRoot intRecursor) (IPair intRecursor) c d) :
    IChain intRecursor intDP c d := by
  obtain ⟨h1, h2, xs, hr, hp⟩ := h
  exact ⟨h1, h2, xs, hr, intPair_edge hp⟩

/-- The side condition of Theorem 8 for the integer recursor, derived from the I-interpretation
laws and the independence of `RIF♯` from the position of the test `x > 0` (properness). -/
theorem intDP_rhsWeak {M : IInterp IUser} (hM : IInterpretation M)
    (hrif : ∀ (a a' : Int) (xs : List Int), M.tup .rif (a :: xs) = M.tup .rif (a' :: xs)) :
    RhsWeak intRecursor intDP M := by
  intro p hp σ hnf xs hreach w
  simp only [intDP, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · have hnf' : ∀ x ∈ [σ 0, σ 1, σ 2], ∀ u, ¬ IStep intRecursor x u := by
      intro x hx u hu
      exact no_istep_of_inf (hnf x (by simpa [ip1] using hx)) hu
    have hreach' : Relation.ReflTransGen (ArgStepOf (IStep intRecursor))
        (Subst.apply σ (.app (.inr .gt) [.var 2, ilit 0]) :: [σ 0, σ 1, σ 2]) xs := by
      simpa [ip1] using hreach
    obtain ⟨y, rfl, -⟩ := argSteps_head_only' hnf' hreach'
    show M.tup .rif ((y :: [σ 0, σ 1, σ 2]).map (zevalT M.pol w)) ≤
      M.tup .rif ((Subst.applyList σ ip1.2.2).map (zevalT M.pol w))
    simp only [ip1, Subst.applyList_cons, Subst.applyList_nil, Subst.apply_var, List.map_cons,
      List.map_nil]
    exact le_of_eq (hrif _ _ _)
  · have hn : ∀ i : Nat, i < 3 → INF intRecursor (σ i) := by
      intro i hi
      exact hnf (σ i) (by interval_cases i <;> simp [ip2])
    have hreach' : Relation.ReflTransGen (ArgStepOf (IStep intRecursor))
        (σ 0 :: σ 1 :: [Subst.apply σ (.app (.inr .sub) [.var 2, ilit 1])]) xs := by
      simpa [ip2] using hreach
    obtain ⟨r1, rfl, hr1⟩ := argStepsOf_cons_nf' (fun u hu => no_istep_of_inf (hn 0 (by omega)) hu)
      hreach'
    obtain ⟨r2, rfl, hr2⟩ := argStepsOf_cons_nf' (fun u hu => no_istep_of_inf (hn 1 (by omega)) hu)
      hr1
    obtain ⟨y, rfl, hy⟩ := argSteps_head_only' (by simp) hr2
    have hyv := reach_sub_one intRecursor_userRooted hM w (hn 2 (by omega))
      (by simpa [ilit] using hy)
    show M.tup .irec ((σ 0 :: σ 1 :: [y]).map (zevalT M.pol w)) ≤
      M.tup .irec ((Subst.applyList σ ip2.2.2).map (zevalT M.pol w))
    have hsubv : zevalT M.pol w (Subst.apply σ (.app (.inr .sub) [.var 2, ilit 1])) =
        zevalT M.pol w (σ 2) - 1 := by
      simp [zevalT_app, ilit, iconst, hM.1, hM.2.2.1]
    simp only [ip2, Subst.applyList_cons, Subst.applyList_nil, Subst.apply_var, List.map_cons,
      List.map_nil, hyv]
    rw [hsubv]

/-! ## Row: integerTermRewriting -/

/-- The substitution of `b`, `s`, `x` for the variables `0`, `1`, `2`. -/
def sub3 (b s x : ITerm) : Subst (ISym IUser) Nat :=
  fun v => if v = 0 then b else if v = 1 then s else x

/-- `Pol` of the witness: the fixed interpretation of the integers and of `ArithOp`, and `0` on the
user, relational and Boolean symbols. -/
def intPol : ISym IUser → List Int → Int
  | .inr (.lit n), _ => n
  | .inr .add, xs => xs.getD 0 0 + xs.getD 1 0
  | .inr .sub, xs => xs.getD 0 0 - xs.getD 1 0
  | .inr .mul, xs => xs.getD 0 0 * xs.getD 1 0
  | .inr .mod, xs => |xs.getD 0 0|
  | .inr .div, xs => |xs.getD 0 0| - min (|xs.getD 1 0| - 1) |xs.getD 0 0|
  | _, _ => 0

/-- The witness: `REC♯(b, s, x) = x`, `RIF♯(c, b, s, x) = x` and the fresh constant `c = 1`. -/
def intWitnessInterp : IInterp IUser where
  pol := intPol
  tup := fun
    | .irec, xs => xs.getD 2 0
    | .rif, xs => xs.getD 3 0
    | .wrap, _ => 0
  bound := 1

theorem intPol_interp : IInterpretation intWitnessInterp := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> intro a b <;> simp [intWitnessInterp, intPol]

/-- Native data: an integer max-polynomial interpretation read as functions, with the value of
the fresh constant of the reduction pair processor. -/
abbrev integerTermRewritingData : Type := IInterp IUser

/-- Fuhs, Giesl, Plücker, Schneider-Kamp and Falke (Proving Termination of Integer Term Rewriting,
RTA 2009, LNCS 5595, Definition 5, and the properness condition of Theorem 8): an I-interpretation
under which `RIF♯` does not depend on the position of the relational test. -/
def integerTermRewritingLaws (M : integerTermRewritingData) : Prop :=
  IInterpretation M ∧ ∀ (a a' : Int) (xs : List Int), M.tup .rif (a :: xs) = M.tup .rif (a' :: xs)

/-- The conditional reduction pair processor (Theorem 8) on the dependency pairs of the integer
recursor: both pairs weakly decrease, `RIF♯(true, b, s, x) → REC♯(b, s, x − 1)` strictly
decreases, and `REC♯(b, s, x) → RIF♯(x > 0, b, s, x)` is bounded by `c` through its connection
`x > 0 →* true`. -/
def integerTermRewritingAccepts (M : integerTermRewritingData) : Prop :=
  PWeak intRecursor intDP M ip1 ∧ PWeak intRecursor intDP M ip2 ∧
    PStrict intRecursor intDP M ip2 ∧ PBound intRecursor intDP M ip1

/-- Verdict: escape. -/
def integerTermRewritingResult (M : integerTermRewritingData) : Prop :=
  integerTermRewritingAccepts M ∧ ∀ t : ITerm, RSN (InnerRoot intRecursor) t

/-- Soundness through the bounded-decrease reduction pair: the processor leaves the problems
`{REC♯ → RIF♯}` and `{RIF♯ → REC♯}`, which have no chain of length two, and Corollary 3 gives
termination of `↪_R`. -/
theorem integerTermRewriting_sound :
    ∀ M, integerTermRewritingLaws M → integerTermRewritingAccepts M →
      ∀ t : ITerm, RSN (InnerRoot intRecursor) t := by
  intro M hL hA
  have hwf := wf_iChain_of_processor intRecursor intDP [ip1] [ip2] M
    (by
      intro p hp
      simp only [intDP, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      exacts [hA.1, hA.2.1])
    (by
      intro p hp hp1
      simp only [intDP, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · simp at hp1
      · exact hA.2.2.1)
    (by
      intro p hp hp2
      simp only [intDP, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hA.2.2.2
      · simp at hp2)
    (intDP_rhsWeak hL.1 hL.2) (wf_iChain_single intRecursor ip1 (by decide))
    (wf_iChain_single intRecursor ip2 (by decide))
  exact itrs_terminating_of_chains intRecursor intRecursor_userRooted intRecursor_vars
    (Subrelation.wf (fun {_ _} h => intChain_of_minChain h) hwf)

def integerTermRewritingWitness : integerTermRewritingData := intWitnessInterp

theorem integerTermRewritingWitness_laws : integerTermRewritingLaws integerTermRewritingWitness :=
  ⟨intPol_interp, fun _ _ _ => rfl⟩

theorem intWitness_accepts : integerTermRewritingAccepts intWitnessInterp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ _ _ w
    simp [icallVal, ip1, intWitnessInterp]
  · intro σ _ _ w
    simp [icallVal, ip2, intWitnessInterp, zevalT_app, intPol, ilit, iconst]
  · intro σ _ _ w
    simp [icallVal, ip2, intWitnessInterp, zevalT_app, intPol, ilit, iconst]
  · intro σ hnf hconn w
    obtain ⟨q, hq, σ', hq1, hreach, -⟩ := hconn
    simp only [intDP, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simp [ip1] at hq1
    · have hnf' : ∀ x ∈ [σ 0, σ 1, σ 2], ∀ u, ¬ IStep intRecursor x u := by
        intro x hx u hu
        exact no_istep_of_inf (hnf x (by simpa [ip1] using hx)) hu
      have hreach' : Relation.ReflTransGen (ArgStepOf (IStep intRecursor))
          (Subst.apply σ (.app (.inr .gt) [.var 2, ilit 0]) :: [σ 0, σ 1, σ 2])
          (iconst .tt :: [σ' 0, σ' 1, σ' 2]) := by
        simpa [ip1, ip2, iconst] using hreach
      obtain ⟨y, hy, hry⟩ := argSteps_head_only' hnf' hreach'
      simp only [List.cons.injEq] at hy
      obtain ⟨rfl, -⟩ := hy
      have hx2 : INF intRecursor (σ 2) := hnf (σ 2) (by simp [ip1])
      obtain ⟨n, hn, hpos⟩ := reach_gt_tt intRecursor_userRooted hx2
        (by simpa [ilit, iconst] using hry)
      simp [icallVal, ip1, intWitnessInterp, hn, iconst, intPol, zevalT_app]
      omega

theorem integerTermRewritingWitness_result :
    integerTermRewritingResult integerTermRewritingWitness :=
  ⟨intWitness_accepts, integerTermRewriting_sound _ integerTermRewritingWitness_laws intWitness_accepts⟩

/-- A negative counter reaches the base value: `x > 0 →* false` fires the base rule. -/
theorem intRecursor_negative :
    Relation.ReflTransGen (IStep intRecursor) (.app (.inl .irec) [ilit 0, ilit 0, ilit (-3)])
      (ilit 0) := by
  have hU := intRecursor_userRooted
  have h1 : IStep intRecursor (.app (.inl .irec) [ilit 0, ilit 0, ilit (-3)])
      (.app (.inl .rif) [.app (.inr .gt) [ilit (-3), ilit 0], ilit 0, ilit 0, ilit (-3)]) := by
    refine istep_root_rule (rule := iRecRule) (by simp [intRecursor]) (sub3 (ilit 0) (ilit 0) (ilit (-3)))
      rfl ?_
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact iconst_inf hU _
  have h2 : IStep intRecursor
      (.app (.inl .rif) [.app (.inr .gt) [ilit (-3), ilit 0], ilit 0, ilit 0, ilit (-3)])
      (.app (.inl .rif) [iconst .ff, ilit 0, ilit 0, ilit (-3)]) :=
    CtxStep.arg (.inl .rif) [] [ilit 0, ilit 0, ilit (-3)] (istep_pd hU (by decide))
  have h3 : IStep intRecursor (.app (.inl .rif) [iconst .ff, ilit 0, ilit 0, ilit (-3)]) (ilit 0) := by
    refine istep_root_rule (rule := iIfFalseRule) (by simp [intRecursor])
      (sub3 (ilit 0) (ilit 0) (ilit (-3))) rfl ?_
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> exact iconst_inf hU _
  exact Relation.ReflTransGen.head h1 (Relation.ReflTransGen.head h2 (Relation.ReflTransGen.single h3))

/-- The recursive rule without its test: `rec(b, s, x) → wrap(s, rec(b, s, x − 1))`. -/
def iNoTestRule : Rule (ISym IUser) Nat :=
  ⟨.app (.inl .irec) [.var 0, .var 1, .var 2],
    .app (.inl .wrap) [.var 1, .app (.inl .irec) [.var 0, .var 1, .app (.inr .sub) [.var 2, ilit 1]]],
    rfl⟩

/-- The ITRS of the recursive rule without its test. -/
def intNoTest : TRS (ISym IUser) Nat := [iNoTestRule]

/-- Without its test the recursive rule descends through the negative integers forever. -/
theorem intNoTest_not_terminating :
    ¬ RSN (InnerRoot intNoTest) (.app (.inl .irec) [ilit 0, ilit 0, ilit 0]) := by
  have hU : UserRooted intNoTest := by
    intro rule hrule
    simp only [intNoTest, List.mem_singleton] at hrule
    subst hrule
    exact ⟨_, _, rfl⟩
  have key : ∀ t, RSN (InnerRoot intNoTest) t → ∀ n : Int,
      (IsSubterm (.app (.inl .irec) [ilit 0, ilit 0, ilit n]) t ∨
        IsSubterm (.app (.inl .irec) [ilit 0, ilit 0, .app (.inr .sub) [ilit n, ilit 1]]) t) →
        False := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro n hn
      rcases hn with hs | hs
      · have hstep : IStep intNoTest (.app (.inl .irec) [ilit 0, ilit 0, ilit n])
            (.app (.inl .wrap)
              [ilit 0, .app (.inl .irec) [ilit 0, ilit 0, .app (.inr .sub) [ilit n, ilit 1]]]) := by
          refine istep_root_rule (rule := iNoTestRule) (by simp [intNoTest])
            (sub3 (ilit 0) (ilit 0) (ilit n)) rfl ?_
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> exact iconst_inf hU _
        obtain ⟨t', ht', hsub'⟩ := ctxStep_lift_subterm hs hstep
        exact ih t' ht' n (Or.inr (isSubterm_trans
          (IsSubterm.arg (.inl .wrap) _ (by simp) (IsSubterm.refl _)) hsub'))
      · have hstep : IStep intNoTest
            (.app (.inl .irec) [ilit 0, ilit 0, .app (.inr .sub) [ilit n, ilit 1]])
            (.app (.inl .irec) [ilit 0, ilit 0, ilit (n - 1)]) :=
          CtxStep.arg (.inl .irec) [ilit 0, ilit 0] [] (istep_pd hU (by simp [pdEval]))
        obtain ⟨t', ht', hsub'⟩ := ctxStep_lift_subterm hs hstep
        exact ih t' ht' (n - 1) (Or.inl hsub')
  exact fun h => key _ h 0 (Or.inl (IsSubterm.refl _))

/-- Negative values are handled by the base rule, and the rule without its constraint loops
through the negative integers. -/
theorem integerTermRewritingWitness_feature :
    Relation.ReflTransGen (IStep intRecursor) (.app (.inl .irec) [ilit 0, ilit 0, ilit (-3)])
        (ilit 0) ∧
      ¬ RSN (InnerRoot intNoTest) (.app (.inl .irec) [ilit 0, ilit 0, ilit 0]) :=
  ⟨intRecursor_negative, intNoTest_not_terminating⟩

/-- The witness with the value bound `c = 2`. -/
def intBound2 : IInterp IUser := { intWitnessInterp with bound := 2 }

/-- Raising the bound of the fresh constant to `2` keeps the laws and loses the bounded pair: at
`x = 1` the test `x > 0` holds and `REC♯(b, s, 1) ≿ 2` fails. -/
theorem integerTermRewriting_mutation :
    integerTermRewritingLaws intBound2 ∧ ¬ integerTermRewritingAccepts intBound2 := by
  refine ⟨⟨intPol_interp, fun _ _ _ => rfl⟩, fun h => ?_⟩
  have hU := intRecursor_userRooted
  have hnf : ∀ a ∈ Subst.applyList (sub3 (ilit 0) (ilit 0) (ilit 1)) ip1.1.2, INF intRecursor a := by
    show ∀ a ∈ [ilit 0, ilit 0, ilit 1], INF intRecursor a
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact iconst_inf hU _
  have hconn : Connects intRecursor intDP
      (ip1.2.1, Subst.applyList (sub3 (ilit 0) (ilit 0) (ilit 1)) ip1.2.2) := by
    refine ⟨ip2, by simp [intDP], sub3 (ilit 0) (ilit 0) (ilit 1), rfl, ?_, ?_⟩
    · show Relation.ReflTransGen (ArgStepOf (IStep intRecursor))
        [.app (.inr .gt) [ilit 1, ilit 0], ilit 0, ilit 0, ilit 1]
        [iconst .tt, ilit 0, ilit 0, ilit 1]
      exact Relation.ReflTransGen.single
        ⟨[], [ilit 0, ilit 0, ilit 1], _, _, rfl, rfl, istep_pd hU (by decide)⟩
    · show ∀ a ∈ [iconst .tt, ilit 0, ilit 0, ilit 1], INF intRecursor a
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> exact iconst_inf hU _
  have hb := h.2.2.2 (sub3 (ilit 0) (ilit 0) (ilit 1)) hnf hconn (fun _ => 0)
  simp [icallVal, ip1, intBound2, intWitnessInterp, sub3, ilit, iconst, intPol, zevalT_app] at hb

/-! ## Logically constrained rewriting -/

/-- Theory symbols over the integers and the Booleans (Kop and Nishida, Term Rewriting with
Logical Constraints, FroCoS 2013, Example 4). -/
inductive TSym where
  | lit (n : Int)
  | tt
  | ff
  | add
  | sub
  | mul
  | gt
  | ge
  | lt
  | le
  | eq
  | and
  | not
  deriving DecidableEq

/-- The theory values: `I_int = ℤ` and `I_bool = 𝔹`. -/
inductive LVal where
  | int (n : Int)
  | bool (b : Bool)
  deriving DecidableEq

/-- The interpretation `J` of the theory symbols; `none` on ill-sorted arguments. -/
def jop : TSym → List LVal → Option LVal
  | .lit n, [] => some (.int n)
  | .tt, [] => some (.bool true)
  | .ff, [] => some (.bool false)
  | .add, [.int a, .int b] => some (.int (a + b))
  | .sub, [.int a, .int b] => some (.int (a - b))
  | .mul, [.int a, .int b] => some (.int (a * b))
  | .gt, [.int a, .int b] => some (.bool (decide (b < a)))
  | .ge, [.int a, .int b] => some (.bool (decide (b ≤ a)))
  | .lt, [.int a, .int b] => some (.bool (decide (a < b)))
  | .le, [.int a, .int b] => some (.bool (decide (a ≤ b)))
  | .eq, [.int a, .int b] => some (.bool (decide (a = b)))
  | .and, [.bool a, .bool b] => some (.bool (a && b))
  | .not, [.bool a] => some (.bool (!a))
  | _, _ => none

section LCTRS

variable {F : Type} {nu : Type}

/-- Symbols of an LCTRS: the term symbols `F` and the theory symbols, which share only the
values. -/
abbrev LSym (F : Type) : Type := F ⊕ TSym

mutual
/-- The value `⟦s⟧` of a ground logical term; `none` on variables, on term symbols and on
ill-sorted applications. -/
def jeval : Term (LSym F) nu → Option LVal
  | .var _ => none
  | .app (.inl _) _ => none
  | .app (.inr k) args => (jevalL args).bind (jop k)
/-- The values of a list of ground logical terms. -/
def jevalL : List (Term (LSym F) nu) → Option (List LVal)
  | [] => some []
  | a :: as => (jeval a).bind fun v => (jevalL as).map (v :: ·)
end

theorem jeval_app_inr (k : TSym) (args : List (Term (LSym F) nu)) :
    jeval (.app (.inr k) args) = (jevalL args).bind (jop k) := by
  simp [jeval]

theorem jeval_app_inl (f : F) (args : List (Term (LSym F) nu)) :
    jeval (.app (.inl f) args) = none := by
  simp [jeval]

theorem jevalL_some_mem :
    ∀ {l : List (Term (LSym F) nu)} {vs : List LVal}, jevalL l = some vs →
      ∀ a ∈ l, ∃ va, jeval a = some va
  | [], _, _, a, ha => by simp at ha
  | x :: xs, vs, h, a, ha => by
    simp only [jevalL] at h
    cases hx : jeval x with
    | none => simp [hx] at h
    | some vx =>
      cases hxs : jevalL xs with
      | none => simp [hx, hxs] at h
      | some vxs =>
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ⟨vx, hx⟩
        · exact jevalL_some_mem hxs a ha

theorem jevalL_congr_mid {a b : Term (LSym F) nu} (h : jeval a = jeval b) :
    ∀ pre post : List (Term (LSym F) nu), jevalL (pre ++ a :: post) = jevalL (pre ++ b :: post)
  | [], post => by simp [jevalL, h]
  | x :: pre, post => by simp only [List.cons_append, jevalL, jevalL_congr_mid h pre post]

/-- The value constant of a value. -/
def valT : LVal → Term (LSym F) nu
  | .int n => .app (.inr (.lit n)) []
  | .bool true => .app (.inr .tt) []
  | .bool false => .app (.inr .ff) []

theorem jeval_valT (v : LVal) : jeval (valT v : Term (LSym F) nu) = some v := by
  rcases v with n | (_ | _) <;> simp [valT, jeval, jevalL, jop]

/-- A value: a theory constant. -/
def IsValue (t : Term (LSym F) nu) : Prop := ∃ v : LVal, t = valT v

/-- A constrained rule `ℓ → r [φ]` (Kop and Nishida 2013, Section 3). -/
structure LRule (F : Type) (nu : Type) where
  lhs : Term (LSym F) nu
  rhs : Term (LSym F) nu
  cond : Term (LSym F) nu
  lhs_isApp : lhs.isApp = true

/-- `LVar(ℓ → r [φ]) = Var(φ) ∪ (Var(r) \ Var(ℓ))`. -/
def LVars [DecidableEq nu] (ρ : LRule F nu) : Finset nu :=
  Term.vars ρ.cond ∪ (Term.vars ρ.rhs \ Term.vars ρ.lhs)

/-- `γ` respects `ρ` (Kop and Nishida 2013, Section 3): `γ(x)` is a value for every
`x ∈ LVar(ρ)` and `φγ` is valid. -/
def Respects [DecidableEq nu] (ρ : LRule F nu) (γ : Subst (LSym F) nu) : Prop :=
  (∀ x ∈ LVars ρ, IsValue (γ x)) ∧ jeval (Subst.apply γ ρ.cond) = some (.bool true)

/-- Calculation symbols: theory symbols that are not values. -/
def IsCalc : TSym → Prop
  | .lit _ => False
  | .tt => False
  | .ff => False
  | _ => True

/-- A calculation at the root: `f(v₁, …, vₙ) →calc v` for a calculation symbol `f`, values `vᵢ`,
and the value `v` of `f(v₁, …, vₙ)`. -/
def CalcRoot (s t : Term (LSym F) nu) : Prop :=
  ∃ k args v, IsCalc k ∧ s = .app (.inr k) args ∧ (∀ a ∈ args, IsValue a) ∧
    jeval s = some v ∧ t = valT v

/-- Root steps of `→R = →rule ∪ →calc`; the rewrite relation of the LCTRS is its context
closure. -/
def LRoot [DecidableEq nu] (R : List (LRule F nu)) (s t : Term (LSym F) nu) : Prop :=
  (∃ ρ ∈ R, ∃ γ : Subst (LSym F) nu, Respects ρ γ ∧ s = Subst.apply γ ρ.lhs ∧
      t = Subst.apply γ ρ.rhs) ∨ CalcRoot s t

/-- Left-hand sides are rooted by term symbols that are not theory symbols. -/
def LTermRooted (R : List (LRule F nu)) : Prop :=
  ∀ ρ ∈ R, ∃ f largs, ρ.lhs = .app (.inl f) largs

/-- The defined symbols of an LCTRS. -/
def LDefined (R : List (LRule F nu)) (g : F) : Prop :=
  ∃ ρ ∈ R, ∃ largs, ρ.lhs = .app (.inl g) largs

theorem valT_eq_app (v : LVal) :
    ∃ k, (valT v : Term (LSym F) nu) = .app (.inr k) [] ∧ ¬ IsCalc k := by
  rcases v with n | (_ | _)
  · exact ⟨.lit n, rfl, fun h => h⟩
  · exact ⟨.ff, rfl, fun h => h⟩
  · exact ⟨.tt, rfl, fun h => h⟩

theorem no_lstep_valT [DecidableEq nu] {R : List (LRule F nu)} (hR : LTermRooted R) (v : LVal)
    (u : Term (LSym F) nu) : ¬ CtxStep (LRoot R) (valT v) u := by
  obtain ⟨k, hk, hkc⟩ := valT_eq_app (F := F) (nu := nu) v
  rw [hk]
  intro h
  rcases (ctxStep_app_iff (LRoot R) (.inr k) [] u).1 h with hr | ⟨ys, hys, -⟩
  · rcases hr with ⟨ρ, hρ, γ, -, hl, -⟩ | ⟨k', args, v', hc, hs, -, -, -⟩
    · obtain ⟨f, largs, hf⟩ := hR ρ hρ
      rw [hf, Subst.apply_app] at hl
      simp at hl
    · simp only [Term.app.injEq, Sum.inr.injEq] at hs
      obtain ⟨rfl, -⟩ := hs
      exact hkc hc
  · exact not_argStepOf_nil ys hys

theorem rsn_valT [DecidableEq nu] {R : List (LRule F nu)} (hR : LTermRooted R) (v : LVal) :
    RSN (LRoot R) (valT v) :=
  Acc.intro _ fun u h => absurd h (no_lstep_valT hR v u)

theorem rsn_of_isValue [DecidableEq nu] {R : List (LRule F nu)} (hR : LTermRooted R)
    {t : Term (LSym F) nu} (h : IsValue t) : RSN (LRoot R) t := by
  obtain ⟨v, rfl⟩ := h
  exact rsn_valT hR v

theorem rsn_app_inr_lctrs [DecidableEq nu] {R : List (LRule F nu)} (hR : LTermRooted R)
    (k : TSym) :
    ∀ args : List (Term (LSym F) nu), (∀ a ∈ args, RSN (LRoot R) a) →
      RSN (LRoot R) (.app (.inr k) args) :=
  rsn_app_of_root fun xs u _ hr => by
    rcases hr with ⟨ρ, hρ, γ, -, hl, -⟩ | ⟨k', args', v, -, -, -, -, rfl⟩
    · obtain ⟨f, largs, hf⟩ := hR ρ hρ
      rw [hf, Subst.apply_app] at hl
      simp at hl
    · exact rsn_valT hR v

theorem rsn_app_inl_undefined_lctrs [DecidableEq nu] {R : List (LRule F nu)}
    (hR : LTermRooted R) {g : F} (hg : ¬ LDefined R g) :
    ∀ args : List (Term (LSym F) nu), (∀ a ∈ args, RSN (LRoot R) a) →
      RSN (LRoot R) (.app (.inl g) args) :=
  rsn_app_of_root fun xs u _ hr => by
    rcases hr with ⟨ρ, hρ, γ, -, hl, -⟩ | ⟨k', args', v, -, hs, -, -, -⟩
    · obtain ⟨f, largs, hf⟩ := hR ρ hρ
      rw [hf, Subst.apply_app] at hl
      simp only [Term.app.injEq, Sum.inl.injEq] at hl
      exact absurd ⟨ρ, hρ, largs, by rw [hf, hl.1]⟩ hg
    · simp at hs

theorem rsn_subst_lctrs [DecidableEq nu] {R : List (LRule F nu)} (hR : LTermRooted R)
    (γ : Subst (LSym F) nu) :
    ∀ w : Term (LSym F) nu, (∀ x ∈ Term.vars w, RSN (LRoot R) (γ x)) →
      (∀ g targs, IsSubterm (.app (.inl g) targs) w → LDefined R g →
        (∀ a ∈ Subst.applyList γ targs, RSN (LRoot R) a) →
          RSN (LRoot R) (.app (.inl g) (Subst.applyList γ targs))) →
      RSN (LRoot R) (Subst.apply γ w) := by
  intro w
  induction w using Term.rec' with
  | hvar x =>
    intro hv _
    simpa using hv x (by simp)
  | happ g targs ih =>
    intro hv hc
    have hargs : ∀ a ∈ Subst.applyList γ targs, RSN (LRoot R) a := by
      intro a ha
      rw [Subst.applyList_eq_map, List.mem_map] at ha
      obtain ⟨t, ht, rfl⟩ := ha
      refine ih t ht (fun x hx => hv x ?_) (fun g' targs' hsub hdef hargs' =>
        hc g' targs' (IsSubterm.arg g targs ht hsub) hdef hargs')
      rw [Term.vars_app, Term.mem_varsList_iff]
      exact ⟨t, ht, hx⟩
    rw [Subst.apply_app]
    rcases g with g | k
    · by_cases hg : LDefined R g
      · exact hc g targs (IsSubterm.refl _) hg hargs
      · exact rsn_app_inl_undefined_lctrs hR hg _ hargs
    · exact rsn_app_inr_lctrs hR k _ hargs

/-- The dependency pairs `ℓ♯ → p♯ [φ]` of an LCTRS (Kop, Termination of LCTRSs, WST 2013,
Section 3) as edges between calls: from an instance of a left-hand side by a respecting
substitution to an instantiated subterm of the right-hand side headed by a defined symbol. -/
def LPair [DecidableEq nu] (R : List (LRule F nu)) (c d : Call (LSym F) nu) : Prop :=
  ∃ ρ ∈ R, ∃ γ : Subst (LSym F) nu, Respects ρ γ ∧ Term.app c.1 c.2 = Subst.apply γ ρ.lhs ∧
    ∃ g targs, IsSubterm (.app (.inl g) targs) ρ.rhs ∧ LDefined R g ∧
      d = (.inl g, Subst.applyList γ targs)

/-- Dependency-pair soundness for LCTRSs (Kop 2013, Theorem 3, direction "if"): without infinite
minimal chains the LCTRS terminates. -/
theorem lctrs_terminating_of_chains [DecidableEq nu] (R : List (LRule F nu))
    (hR : LTermRooted R) (hwf : WellFounded (fun d c => MinChainOf (LRoot R) (LPair R) c d)) :
    ∀ t, RSN (LRoot R) t := by
  refine rsn_of_minChainOf_wf (LRoot R) (LPair R) ?_ ?_ hwf
  · rintro x u (⟨ρ, hρ, γ, -, hl, -⟩ | ⟨k, args, v, -, hs, -, -, -⟩)
    · obtain ⟨f, largs, hf⟩ := hR ρ hρ
      rw [hf, Subst.apply_app] at hl
      exact Term.noConfusion hl
    · exact Term.noConfusion hs
  · intro f xs u hr hxs hcall
    rcases hr with ⟨ρ, hρ, γ, hresp, hl, rfl⟩ | ⟨k, args, v, -, -, -, -, rfl⟩
    · refine rsn_subst_lctrs hR γ ρ.rhs (fun x hx => ?_) (fun g targs hsub hdef hargs =>
        hcall (.inl g, Subst.applyList γ targs) ⟨ρ, hρ, γ, hresp, hl, g, targs, hsub, hdef, rfl⟩
          hargs)
      by_cases hxl : x ∈ Term.vars ρ.lhs
      · obtain ⟨g0, largs, hg0⟩ := hR ρ hρ
        have hl' := hl
        rw [hg0, Subst.apply_app] at hl'
        simp only [Term.app.injEq] at hl'
        obtain ⟨-, rfl⟩ := hl'
        rw [hg0, Term.vars_app, Term.mem_varsList_iff] at hxl
        obtain ⟨a, ha, hxa⟩ := hxl
        have hmem : Subst.apply γ a ∈ Subst.applyList γ largs := by
          rw [Subst.applyList_eq_map]
          exact List.mem_map_of_mem ha
        exact rsn_of_isSubterm (isSubterm_subst_var γ a x hxa) (hxs _ hmem)
      · refine rsn_of_isValue hR (hresp.1 x ?_)
        simp only [LVars, Finset.mem_union, Finset.mem_sdiff]
        exact Or.inr ⟨hx, hxl⟩
    · exact rsn_valT hR v

/-- Ground logical terms keep their value under rewriting: rules never apply to them, and
calculations preserve the value. -/
theorem jeval_lstep [DecidableEq nu] {R : List (LRule F nu)} (hR : LTermRooted R)
    {t u : Term (LSym F) nu} (h : CtxStep (LRoot R) t u) :
    ∀ v, jeval t = some v → jeval u = some v := by
  induction h with
  | root hr =>
    intro v hv
    rcases hr with ⟨ρ, hρ, γ, -, rfl, -⟩ | ⟨k, args, v', -, -, -, hj, rfl⟩
    · obtain ⟨f, largs, hf⟩ := hR ρ hρ
      rw [hf, Subst.apply_app, jeval_app_inl] at hv
      exact absurd hv (by simp)
    · rw [hj] at hv
      rw [jeval_valT]
      exact hv
  | @arg f pre post a b _ ih =>
    intro v hv
    rcases f with f | k
    · rw [jeval_app_inl] at hv
      exact absurd hv (by simp)
    · rw [jeval_app_inr] at hv ⊢
      cases hl : jevalL (pre ++ a :: post) with
      | none =>
        rw [hl] at hv
        exact absurd hv (by simp)
      | some vs =>
        obtain ⟨va, hva⟩ := jevalL_some_mem hl a (by simp)
        have hab : jeval a = jeval b := by rw [hva, ih va hva]
        rw [← jevalL_congr_mid hab pre post, hl]
        rw [hl] at hv
        exact hv

theorem jeval_lsteps [DecidableEq nu] {R : List (LRule F nu)} (hR : LTermRooted R)
    {t u : Term (LSym F) nu} (h : Relation.ReflTransGen (CtxStep (LRoot R)) t u) :
    ∀ v, jeval t = some v → jeval u = some v := by
  induction h with
  | refl => exact fun v hv => hv
  | tail _ hst ih => exact fun v hv => jeval_lstep hR hst v (ih v hv)

/-- The value of the projected argument of a call. -/
def lval (ν : F → Nat) (c : Call (LSym F) nu) : Option LVal :=
  match c.1 with
  | .inl f => (c.2[ν f]?).bind jeval
  | .inr _ => none

/-- The value criterion (Kop, Termination of LCTRSs, WST 2013, Definition 9 and Theorem 10) with
`P₂ = ∅`, sort `int` and the well-founded order `n ≻ m ⇔ m < n ∧ b < n` on `ℤ`, read on
respecting substitutions: for every dependency pair, the projected arguments of its instantiated
left and right sides are ground logical terms with integer values `n ≻ m`. -/
def ValueCriterion [DecidableEq nu] (R : List (LRule F nu)) (ν : F → Nat) (b : Int) : Prop :=
  ∀ ρ ∈ R, ∀ f largs, ρ.lhs = .app (.inl f) largs → ∀ g targs,
    IsSubterm (.app (.inl g) targs) ρ.rhs → LDefined R g → ∀ γ : Subst (LSym F) nu,
      Respects ρ γ → ∃ n m : Int, ((Subst.applyList γ largs)[ν f]?).bind jeval = some (.int n) ∧
        ((Subst.applyList γ targs)[ν g]?).bind jeval = some (.int m) ∧ m < n ∧ b < n

theorem bind_getElem_eq_some {l : List (Term (LSym F) nu)} {i : Nat} {v : LVal}
    (h : (l[i]?).bind jeval = some v) : ∃ t, l[i]? = some t ∧ jeval t = some v := by
  cases hl : l[i]? with
  | none =>
    rw [hl] at h
    exact absurd h (by simp)
  | some t =>
    rw [hl] at h
    exact ⟨t, rfl, h⟩

/-- The value criterion makes the minimal chain relation well founded: along a chain the values
of the projected arguments descend in `≻`, because ground logical terms keep their values
under the argument rewriting between two pairs. -/
theorem wf_lChain_of_valueCriterion [DecidableEq nu] (R : List (LRule F nu))
    (hR : LTermRooted R) (ν : F → Nat) (b : Int) (hvc : ValueCriterion R ν b) :
    WellFounded (fun d c => MinChainOf (LRoot R) (LPair R) c d) := by
  have hedge : ∀ c d, MinChainOf (LRoot R) (LPair R) c d →
      ∃ m, lval ν d = some (.int m) ∧ ∀ n, lval ν c = some (.int n) → m < n ∧ b < n := by
    rintro c d ⟨-, -, xs, hreach, ρ, hρ, γ, hresp, hl, g, targs, hsub, hdef, rfl⟩
    obtain ⟨f, largs, hf⟩ := hR ρ hρ
    obtain ⟨n, m, hn, hm, hmn, hbn⟩ := hvc ρ hρ f largs hf g targs hsub hdef γ hresp
    refine ⟨m, hm, fun n' hn' => ?_⟩
    have hl' := hl
    rw [hf, Subst.apply_app] at hl'
    simp only [Term.app.injEq] at hl'
    obtain ⟨hc1, rfl⟩ := hl'
    obtain ⟨l0, hl0, hjl0⟩ := bind_getElem_eq_some hn
    have hn'' : (c.2[ν f]?).bind jeval = some (.int n') := by
      simpa [lval, hc1] using hn'
    obtain ⟨t0, ht0, hjt0⟩ := bind_getElem_eq_some hn''
    obtain ⟨x0, hx0, hrx⟩ := argStepsOf_getElem? hreach (ν f) l0 hl0
    rw [ht0] at hx0
    cases hx0
    have hval := jeval_lsteps hR hrx _ hjt0
    rw [hjl0] at hval
    simp only [Option.some.injEq, LVal.int.injEq] at hval
    subst hval
    exact ⟨hmn, hbn⟩
  have hacc : ∀ k : Nat, ∀ d, (∃ m, lval ν d = some (.int m) ∧ (m - b).toNat ≤ k) →
      Acc (fun d c => MinChainOf (LRoot R) (LPair R) c d) d := by
    intro k
    induction k with
    | zero =>
      rintro d ⟨m, hm, hk⟩
      refine Acc.intro d fun e hde => ?_
      obtain ⟨m', -, hlt⟩ := hedge d e hde
      have h1 := (hlt m hm).2
      have h2 := Int.toNat_le.1 hk
      omega
    | succ k ih =>
      rintro d ⟨m, hm, hk⟩
      refine Acc.intro d fun e hde => ?_
      obtain ⟨m', hm', hlt⟩ := hedge d e hde
      obtain ⟨h1, h2⟩ := hlt m hm
      have h3 := Int.toNat_le.1 hk
      exact ih e ⟨m', hm', Int.toNat_le.2 (by omega)⟩
  exact ⟨fun c => Acc.intro c fun d hcd => by
    obtain ⟨m, hm, -⟩ := hedge c d hcd
    exact hacc _ d ⟨m, hm, le_rfl⟩⟩

end LCTRS

/-! ## Row: lctrs -/

/-- Term symbols of the integer recursor as an LCTRS. -/
inductive LUser where
  | lrec
  | lwrap
  deriving DecidableEq

/-- Terms of the integer recursor as an LCTRS. -/
abbrev LTerm : Type := Term (LSym LUser) Nat

/-- An integer value. -/
def llit (n : Int) : LTerm := .app (.inr (.lit n)) []

/-- `rec(b, s, x) → wrap(s, rec(b, s, x − 1)) [x > 0]`. -/
def lRecSucc : LRule LUser Nat :=
  ⟨.app (.inl .lrec) [.var 0, .var 1, .var 2],
    .app (.inl .lwrap) [.var 1, .app (.inl .lrec) [.var 0, .var 1, .app (.inr .sub) [.var 2, llit 1]]],
    .app (.inr .gt) [.var 2, llit 0], rfl⟩

/-- `rec(b, s, x) → b [x ≤ 0]`. -/
def lRecZero : LRule LUser Nat :=
  ⟨.app (.inl .lrec) [.var 0, .var 1, .var 2], .var 0, .app (.inr .le) [.var 2, llit 0], rfl⟩

/-- The integer recursor with its two constraints, natively as an LCTRS. -/
def lctrsRecursor : List (LRule LUser Nat) := [lRecSucc, lRecZero]

theorem mem_lctrsRecursor {ρ : LRule LUser Nat} (h : ρ ∈ lctrsRecursor) :
    ρ = lRecSucc ∨ ρ = lRecZero := by
  simpa [lctrsRecursor] using h

theorem lctrsRecursor_termRooted : LTermRooted lctrsRecursor := by
  intro ρ hρ
  rcases mem_lctrsRecursor hρ with rfl | rfl
  exacts [⟨_, _, rfl⟩, ⟨_, _, rfl⟩]

theorem lctrsRecursor_defined_iff (g : LUser) : LDefined lctrsRecursor g ↔ g = .lrec := by
  constructor
  · rintro ⟨ρ, hρ, largs, hl⟩
    rcases mem_lctrsRecursor hρ with rfl | rfl <;>
      simp only [lRecSucc, lRecZero, Term.app.injEq, Sum.inl.injEq] at hl <;> exact hl.1.symm
  · rintro rfl
    exact ⟨lRecSucc, by simp [lctrsRecursor], _, rfl⟩

/-- The substitution of `b`, `s`, `x` for the variables `0`, `1`, `2`. -/
def lsub3 (b s x : LTerm) : Subst (LSym LUser) Nat :=
  fun v => if v = 0 then b else if v = 1 then s else x

/-- A substitution that respects the recursive rule instantiates the counter by a positive
integer. -/
theorem respects_lRecSucc {γ : Subst (LSym LUser) Nat} (h : Respects lRecSucc γ) :
    ∃ n : Int, γ 2 = llit n ∧ 0 < n := by
  obtain ⟨v, hv⟩ := h.1 2 (by simp [LVars, lRecSucc, llit])
  have hc := h.2
  rcases v with n | (_ | _)
  · refine ⟨n, hv, ?_⟩
    simp [lRecSucc, hv, valT, llit, jeval, jevalL, jop] at hc
    exact hc
  · simp [lRecSucc, hv, valT, llit, jeval, jevalL, jop] at hc
  · simp [lRecSucc, hv, valT, llit, jeval, jevalL, jop] at hc

/-- Native data of the value criterion: a projection of the marked symbols to an argument
position, and the bound `b` of the well-founded order `n ≻ m ⇔ m < n ∧ b < n` on `ℤ`. -/
structure LValueData where
  proj : LUser → Nat
  bound : Int

/-- Native data: the projection and the value bound. -/
abbrev lctrsData : Type := LValueData

/-- Kop (Termination of LCTRSs, WST 2013, Definition 9): a projection function assigns to each
marked symbol one of its argument positions; with Kop and Nishida (Term Rewriting with Logical
Constraints, FroCoS 2013, LNAI 8152, Section 3) for the constrained system. -/
def lctrsLaws (M : lctrsData) : Prop := ∀ g, LDefined lctrsRecursor g → M.proj g < 3

/-- The value criterion (Kop 2013, Theorem 10) accepts the dependency pair
`rec♯(b, s, x) → rec♯(b, s, x − 1) [x > 0]`: under the constraint, the projected counter is a
value above the bound that decreases. -/
def lctrsAccepts (M : lctrsData) : Prop := ValueCriterion lctrsRecursor M.proj M.bound

/-- Verdict: escape. -/
def lctrsResult (M : lctrsData) : Prop :=
  lctrsAccepts M ∧ ∀ t : LTerm, RSN (LRoot lctrsRecursor) t

/-- Soundness through the value criterion and the dependency-pair theorem of the constrained
framework. -/
theorem lctrs_sound :
    ∀ M, lctrsLaws M → lctrsAccepts M → ∀ t : LTerm, RSN (LRoot lctrsRecursor) t :=
  fun M _ hA => lctrs_terminating_of_chains lctrsRecursor lctrsRecursor_termRooted
    (wf_lChain_of_valueCriterion lctrsRecursor lctrsRecursor_termRooted M.proj M.bound hA)

/-- The witness: project to the counter, bound `0`. -/
def lctrsWitness : lctrsData := ⟨fun _ => 2, 0⟩

theorem lctrsWitness_laws : lctrsLaws lctrsWitness := fun _ _ => by norm_num [lctrsWitness]

theorem lctrsWitness_accepts : lctrsAccepts lctrsWitness := by
  intro ρ hρ f largs hf g targs hsub hdef γ hresp
  rw [lctrsRecursor_defined_iff] at hdef
  subst hdef
  rcases mem_lctrsRecursor hρ with rfl | rfl
  · simp only [lRecSucc, Term.app.injEq, Sum.inl.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have hm := mem_subtermsT_of_isSubterm hsub
    simp [lRecSucc, subtermsT, subtermsL, llit] at hm
    subst hm
    obtain ⟨n, hn, hpos⟩ := respects_lRecSucc hresp
    refine ⟨n, n - 1, ?_, ?_, by omega, by simpa [lctrsWitness] using hpos⟩
    · simp [lctrsWitness, hn, llit, jeval, jevalL, jop]
    · simp [lctrsWitness, hn, llit, jeval, jevalL, jop]
  · have hm := mem_subtermsT_of_isSubterm hsub
    simp [lRecZero, subtermsT] at hm

theorem lctrsWitness_result : lctrsResult lctrsWitness :=
  ⟨lctrsWitness_accepts, lctrs_sound _ lctrsWitness_laws lctrsWitness_accepts⟩

/-- The same left-hand side under a true and a false constraint (`3 > 0` and `3 ≤ 0`,
`−2 ≤ 0` and `−2 > 0`), and theory evaluation: `3 − 1` is rewritten to `2` by a calculation
step, and no rule applies to `rec(0, 0, 3 − 1)` at the root because `3 − 1` is not a value. -/
theorem lctrsWitness_feature :
    (Respects lRecSucc (lsub3 (llit 0) (llit 0) (llit 3)) ∧
        ¬ Respects lRecZero (lsub3 (llit 0) (llit 0) (llit 3))) ∧
      (Respects lRecZero (lsub3 (llit 0) (llit 0) (llit (-2))) ∧
        ¬ Respects lRecSucc (lsub3 (llit 0) (llit 0) (llit (-2)))) ∧
      CtxStep (LRoot lctrsRecursor) (.app (.inr .sub) [llit 3, llit 1]) (llit 2) ∧
      ∀ ρ ∈ lctrsRecursor, ∀ γ : Subst (LSym LUser) Nat, Respects ρ γ →
        Subst.apply γ ρ.lhs ≠ .app (.inl .lrec) [llit 0, llit 0, .app (.inr .sub) [llit 3, llit 1]] := by
  refine ⟨⟨⟨fun x hx => ?_, ?_⟩, fun h => ?_⟩, ⟨⟨fun x hx => ?_, ?_⟩, fun h => ?_⟩, ?_, ?_⟩
  · have hx2 : x = 2 := by
      simp [LVars, lRecSucc, llit] at hx
      omega
    subst hx2
    exact ⟨.int 3, rfl⟩
  · simp [lRecSucc, lsub3, llit, jeval, jevalL, jop]
  · have := h.2
    simp [lRecZero, lsub3, llit, jeval, jevalL, jop] at this
  · have hx2 : x = 2 := by
      simp [LVars, lRecZero, llit] at hx
      omega
    subst hx2
    exact ⟨.int (-2), rfl⟩
  · simp [lRecZero, lsub3, llit, jeval, jevalL, jop]
  · have := h.2
    simp [lRecSucc, lsub3, llit, jeval, jevalL, jop] at this
  · refine CtxStep.root (Or.inr ⟨.sub, [llit 3, llit 1], .int 2, trivial, rfl, ?_, ?_, rfl⟩)
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      exacts [⟨.int 3, rfl⟩, ⟨.int 1, rfl⟩]
    · simp [llit, jeval, jevalL, jop]
  · intro ρ hρ γ hresp heq
    have hvar : 2 ∈ LVars ρ := by
      rcases mem_lctrsRecursor hρ with rfl | rfl <;> simp [LVars, lRecSucc, lRecZero, llit]
    have hlhs : ρ.lhs = .app (.inl .lrec) [.var 0, .var 1, .var 2] := by
      rcases mem_lctrsRecursor hρ with rfl | rfl <;> rfl
    rw [hlhs] at heq
    simp only [Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil, Subst.apply_var,
      Term.app.injEq, List.cons.injEq, and_true, true_and] at heq
    obtain ⟨v, hv⟩ := hresp.1 2 hvar
    rw [heq.2.2] at hv
    rcases v with n | (_ | _) <;> simp [valT] at hv

/-- The witness with the value bound `1`. -/
def lctrsBound1 : lctrsData := ⟨fun _ => 2, 1⟩

/-- Raising the value bound to `1` keeps the laws and loses the criterion: at `x = 1` the
constraint `x > 0` holds, and `1 ≻ 0` fails for the bound `1`. -/
theorem lctrs_mutation : lctrsLaws lctrsBound1 ∧ ¬ lctrsAccepts lctrsBound1 := by
  refine ⟨fun _ _ => by norm_num [lctrsBound1], fun h => ?_⟩
  have hresp : Respects lRecSucc (lsub3 (llit 0) (llit 0) (llit 1)) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · have hx2 : x = 2 := by
        simp [LVars, lRecSucc, llit] at hx
        omega
      subst hx2
      exact ⟨.int 1, rfl⟩
    · simp [lRecSucc, lsub3, llit, jeval, jevalL, jop]
  obtain ⟨n, m, hn, -, -, hbn⟩ := h lRecSucc (by simp [lctrsRecursor]) .lrec
    [.var 0, .var 1, .var 2] rfl .lrec [.var 0, .var 1, .app (.inr .sub) [.var 2, llit 1]]
    (IsSubterm.arg (.inl .lwrap : LSym LUser) _ (by simp) (IsSubterm.refl _))
    ((lctrsRecursor_defined_iff _).2 rfl) _ hresp
  simp [lsub3, llit, lctrsBound1, Subst.applyList_eq_map, Subst.apply_var, jeval, jevalL, jop] at hn
  simp [lctrsBound1] at hbn
  omega

end OperatorKO7.Methods.OrientationClosure.MethodRowsConditionalConstrained
