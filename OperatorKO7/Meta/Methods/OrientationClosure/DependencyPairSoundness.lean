import OperatorKO7.Meta.Rewriting.Rewrite
import Mathlib.Tactic

/-!
# Dependency-pair soundness for finite first-order rewriting

For a rewrite system `R` over first-order terms whose right-hand sides use only left-hand-side
variables: if the minimal dependency-chain relation is well founded, every term is strongly
normalizing (`terminating_of_minChain_wf`). A minimal chain step goes from a call `(f, args)` with
strongly normalizing arguments, through argument rewriting to an instance `σ • f(largs)` of a
left-hand side, to the call `(g, σ • targs)` of a subterm `g(targs)` of the right-hand side whose
root `g` is defined; the target arguments are strongly normalizing as well.

A reduction pair on calls that decreases weakly on argument steps and strictly on dependency-pair
instances, both only for strongly normalizing arguments, makes the chain relation well founded
(`terminating_of_callReductionPair`). The variable condition is necessary: the one-rule system
`c → x` has no dependency pairs and does not terminate (`fresh_variable_control`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- Strong normalization of a term: no infinite rewrite sequence starts from it. -/
abbrev SN (R : TRS sigma nu) (t : Term sigma nu) : Prop :=
  Acc (fun u t => Step R t u) t

/-- Argument lists related by one rewrite step at one position. -/
def ArgStep (R : TRS sigma nu) (xs ys : List (Term sigma nu)) : Prop :=
  ∃ pre post : List (Term sigma nu), ∃ a b : Term sigma nu,
    xs = pre ++ a :: post ∧ ys = pre ++ b :: post ∧ Step R a b

theorem not_argStep_nil (R : TRS sigma nu) (ys : List (Term sigma nu)) : ¬ ArgStep R [] ys := by
  rintro ⟨pre, post, a, b, h, -, -⟩
  cases pre <;> simp at h

theorem argStep_cons_iff (R : TRS sigma nu) (a : Term sigma nu) (rest ys : List (Term sigma nu)) :
    ArgStep R (a :: rest) ys ↔
      (∃ b, Step R a b ∧ ys = b :: rest) ∨ (∃ rest', ArgStep R rest rest' ∧ ys = a :: rest') := by
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

/-- Rewriting an application is a root contraction or one argument step. -/
theorem step_app_iff (R : TRS sigma nu) (f : sigma) (args : List (Term sigma nu))
    (u : Term sigma nu) :
    Step R (.app f args) u ↔
      rootStep R (.app f args) u ∨ ∃ args', ArgStep R args args' ∧ u = .app f args' := by
  constructor
  · intro h
    cases h with
    | root h => exact Or.inl h
    | arg g pre post hab => exact Or.inr ⟨_, ⟨pre, post, _, _, rfl, rfl, hab⟩, rfl⟩
  · rintro (h | ⟨args', ⟨pre, post, a, b, rfl, rfl, hab⟩, rfl⟩)
    · exact Step.root h
    · exact Step.arg f pre post hab

/-- Every left-hand side is an application. -/
theorem lhs_eq_app (rule : Rule sigma nu) : ∃ g largs, rule.lhs = .app g largs := by
  have h := rule.lhs_isApp
  cases hl : rule.lhs with
  | var x =>
    rw [hl] at h
    simp at h
  | app g largs => exact ⟨g, largs, rfl⟩

/-- Variables do not rewrite. -/
theorem not_step_var (R : TRS sigma nu) (x : nu) (u : Term sigma nu) : ¬ Step R (.var x) u := by
  intro h
  cases h with
  | root h =>
    obtain ⟨rule, -, σ, hl, -⟩ := h
    obtain ⟨g, largs, hg⟩ := lhs_eq_app rule
    rw [hg, Subst.apply_app] at hl
    exact Term.noConfusion hl

theorem sn_of_step {R : TRS sigma nu} {t u : Term sigma nu} (ht : SN R t) (h : Step R t u) :
    SN R u :=
  Acc.inv ht h

/-- Arguments of a strongly normalizing application are strongly normalizing. -/
theorem sn_arg {R : TRS sigma nu} {f : sigma} {args : List (Term sigma nu)}
    (h : SN R (.app f args)) {a : Term sigma nu} (ha : a ∈ args) : SN R a := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
  have key : ∀ t, SN R t → ∀ (pre post : List (Term sigma nu)) (a : Term sigma nu),
      t = .app f (pre ++ a :: post) → SN R a := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro pre post a heq
      refine Acc.intro _ fun b hab => ?_
      exact ih _ (by rw [heq]; exact Step.arg f pre post hab) pre post b rfl
  exact key _ h pre post a rfl

/-- A strongly normalizing substitution instance has strongly normalizing images of the
variables of the instantiated term. -/
theorem sn_subst_var [DecidableEq nu] {R : TRS sigma nu} (σ : Subst sigma nu) :
    ∀ (t : Term sigma nu) (x : nu), x ∈ Term.vars t → SN R (Subst.apply σ t) → SN R (σ x) := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
    intro x hx h
    simp only [Term.vars_var, Finset.mem_singleton] at hx
    subst hx
    simpa using h
  | happ g args ih =>
    intro x hx h
    rw [Term.vars_app, Term.mem_varsList_iff] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    rw [Subst.apply_app, Subst.applyList_eq_map] at h
    exact ih a ha x hxa (sn_arg h (List.mem_map_of_mem ha))

/-- Strongly normalizing arguments make argument rewriting well founded. -/
theorem acc_cons_of {R : TRS sigma nu} :
    ∀ a : Term sigma nu, SN R a → ∀ rest : List (Term sigma nu),
      Acc (fun ys xs => ArgStep R xs ys) rest → Acc (fun ys xs => ArgStep R xs ys) (a :: rest) := by
  intro a ha
  induction ha with
  | intro a _ iha =>
    intro rest hr
    induction hr with
    | intro rest hr' ihr =>
      refine Acc.intro _ fun ys hys => ?_
      rcases (argStep_cons_iff R a rest ys).1 hys with ⟨b, hab, rfl⟩ | ⟨rest', hrr, rfl⟩
      · exact iha b hab rest (Acc.intro rest hr')
      · exact ihr rest' hrr

theorem accArgs {R : TRS sigma nu} :
    ∀ args : List (Term sigma nu), (∀ a ∈ args, SN R a) →
      Acc (fun ys xs => ArgStep R xs ys) args
  | [], _ => Acc.intro _ fun ys h => absurd h (not_argStep_nil R ys)
  | a :: rest, h =>
    acc_cons_of a (h a List.mem_cons_self) rest
      (accArgs rest fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem argStep_sn {R : TRS sigma nu} {xs ys : List (Term sigma nu)}
    (hxs : ∀ a ∈ xs, SN R a) (h : ArgStep R xs ys) : ∀ b ∈ ys, SN R b := by
  obtain ⟨pre, post, a, b, rfl, rfl, hab⟩ := h
  intro c hc
  simp only [List.mem_append, List.mem_cons] at hc
  rcases hc with hc | rfl | hc
  · exact hxs c (by simp [hc])
  · exact sn_of_step (hxs a (by simp)) hab
  · exact hxs c (by simp [hc])

/-- `f` is the root symbol of some left-hand side of `R`. -/
def IsDefined (R : TRS sigma nu) (f : sigma) : Prop :=
  ∃ rule ∈ R, ∃ largs : List (Term sigma nu), rule.lhs = .app f largs

theorem not_rootStep_of_not_defined {R : TRS sigma nu} {f : sigma} (hf : ¬ IsDefined R f)
    (args : List (Term sigma nu)) (u : Term sigma nu) : ¬ rootStep R (.app f args) u := by
  rintro ⟨rule, hrule, σ, hl, -⟩
  obtain ⟨g, largs, hg⟩ := lhs_eq_app rule
  rw [hg, Subst.apply_app] at hl
  simp only [Term.app.injEq] at hl
  exact hf ⟨rule, hrule, largs, by rw [hg, hl.1]⟩

/-- An application with an undefined root and strongly normalizing arguments is strongly
normalizing. -/
theorem sn_app_of_not_defined {R : TRS sigma nu} {f : sigma} (hf : ¬ IsDefined R f) :
    ∀ args : List (Term sigma nu), (∀ a ∈ args, SN R a) → SN R (.app f args) := by
  intro args hargs
  have hacc := accArgs args hargs
  induction hacc with
  | intro xs _ ih =>
    refine Acc.intro _ fun u hu => ?_
    rcases (step_app_iff R f xs u).1 hu with hroot | ⟨ys, hys, rfl⟩
    · exact absurd hroot (not_rootStep_of_not_defined hf xs u)
    · exact ih ys hys (argStep_sn hargs hys)

/-- `w` occurs as a subterm of `t`. -/
inductive IsSubterm : Term sigma nu → Term sigma nu → Prop
  | refl (t : Term sigma nu) : IsSubterm t t
  | arg {w a : Term sigma nu} (f : sigma) (args : List (Term sigma nu)) :
      a ∈ args → IsSubterm w a → IsSubterm w (.app f args)

theorem IsSubterm.of_app_arg_aux : ∀ {w t : Term sigma nu}, IsSubterm w t →
    ∀ {g : sigma} {targs : List (Term sigma nu)} {a : Term sigma nu},
      w = .app g targs → a ∈ targs → IsSubterm a t := by
  intro w t h
  induction h with
  | refl =>
    intro g targs a hw ha
    subst hw
    exact .arg g targs ha (.refl a)
  | arg f args hmem _ ih =>
    intro g targs a hw ha
    exact .arg f args hmem (ih hw ha)

theorem IsSubterm.of_app_arg {g : sigma} {targs : List (Term sigma nu)} {a t : Term sigma nu}
    (h : IsSubterm (.app g targs) t) (ha : a ∈ targs) : IsSubterm a t :=
  IsSubterm.of_app_arg_aux h rfl ha

theorem IsSubterm.vars_subset [DecidableEq nu] {w t : Term sigma nu} (h : IsSubterm w t) :
    Term.vars w ⊆ Term.vars t := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | arg f args hmem _ ih =>
    intro x hx
    rw [Term.vars_app, Term.mem_varsList_iff]
    exact ⟨_, hmem, ih hx⟩

/-! ## Minimal chains -/

/-- A minimal dependency-chain step between calls `(f, args)`. -/
def MinChainStep (R : TRS sigma nu) (c d : sigma × List (Term sigma nu)) : Prop :=
  (∀ a ∈ c.2, SN R a) ∧ (∀ a ∈ d.2, SN R a) ∧
    ∃ args', Relation.ReflTransGen (ArgStep R) c.2 args' ∧
      ∃ rule ∈ R, ∃ σ : Subst sigma nu, Term.app c.1 args' = Subst.apply σ rule.lhs ∧
        ∃ targs, IsSubterm (Term.app d.1 targs) rule.rhs ∧ IsDefined R d.1 ∧
          d.2 = Subst.applyList σ targs

/-- The core of dependency-pair soundness: a call accessible for the minimal chain relation,
with strongly normalizing arguments, gives strongly normalizing applications after any argument
rewriting. -/
theorem sn_of_minChain_acc [DecidableEq nu] (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) :
    ∀ c : sigma × List (Term sigma nu), Acc (fun d c => MinChainStep R c d) c →
      (∀ a ∈ c.2, SN R a) → ∀ xs, Relation.ReflTransGen (ArgStep R) c.2 xs →
        (∀ a ∈ xs, SN R a) → SN R (.app c.1 xs) := by
  intro c hc
  induction hc with
  | intro c _ ihc =>
    intro hcSN xs hreach hxs
    have hacc := accArgs xs hxs
    induction hacc with
    | intro xs _ ihx =>
      refine Acc.intro _ fun u hu => ?_
      rcases (step_app_iff R c.1 xs u).1 hu with hroot | ⟨ys, hys, rfl⟩
      · obtain ⟨rule, hrule, σ, hl, rfl⟩ := hroot
        obtain ⟨g0, largs, hg0⟩ := lhs_eq_app rule
        have hl' := hl
        rw [hg0, Subst.apply_app] at hl'
        simp only [Term.app.injEq] at hl'
        obtain ⟨-, hxsEq⟩ := hl'
        have hvarSN : ∀ x ∈ Term.vars rule.rhs, SN R (σ x) := by
          intro x hx
          have hxl : x ∈ Term.vars rule.lhs := hvars rule hrule hx
          rw [hg0, Term.vars_app, Term.mem_varsList_iff] at hxl
          obtain ⟨a, ha, hxa⟩ := hxl
          have hsa : SN R (Subst.apply σ a) := by
            apply hxs
            rw [hxsEq, Subst.applyList_eq_map]
            exact List.mem_map_of_mem ha
          exact sn_subst_var σ a x hxa hsa
        have key : ∀ w, IsSubterm w rule.rhs → SN R (Subst.apply σ w) := by
          intro w
          induction w using Term.rec' with
          | hvar x =>
            intro hw
            have hx : x ∈ Term.vars rule.rhs := hw.vars_subset (by simp)
            simpa using hvarSN x hx
          | happ g targs ih =>
            intro hw
            have hargs : ∀ a ∈ Subst.applyList σ targs, SN R a := by
              intro a ha
              rw [Subst.applyList_eq_map, List.mem_map] at ha
              obtain ⟨t, ht, rfl⟩ := ha
              exact ih t ht (hw.of_app_arg ht)
            rw [Subst.apply_app]
            by_cases hg : IsDefined R g
            · have hstep : MinChainStep R c (g, Subst.applyList σ targs) :=
                ⟨hcSN, hargs, xs, hreach, rule, hrule, σ, hl, targs, hw, hg, rfl⟩
              exact ihc (g, Subst.applyList σ targs) hstep hargs _ Relation.ReflTransGen.refl
                hargs
            · exact sn_app_of_not_defined hg _ hargs
        exact key rule.rhs (.refl _)
      · exact ihx ys hys (hreach.tail hys) (argStep_sn hxs hys)

/-- Dependency-pair soundness: a well-founded minimal chain relation gives termination. -/
theorem terminating_of_minChain_wf [DecidableEq nu] (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs)
    (hwf : WellFounded (fun d c => MinChainStep R c d)) :
    ∀ t : Term sigma nu, SN R t := by
  intro t
  induction t using Term.rec' with
  | hvar x => exact Acc.intro _ fun u h => absurd h (not_step_var R x u)
  | happ f args ih =>
    exact sn_of_minChain_acc R hvars (f, args) (hwf.apply _) ih args
      Relation.ReflTransGen.refl ih

theorem wellFounded_step_of_minChain_wf [DecidableEq nu] (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs)
    (hwf : WellFounded (fun d c => MinChainStep R c d)) :
    WellFounded (fun u t => Step R t u) :=
  ⟨terminating_of_minChain_wf R hvars hwf⟩

/-! ## Reduction pairs on calls -/

/-- A reduction pair on calls. Both conditions are required only for strongly normalizing
arguments, which is the minimality of the chains. -/
structure CallReductionPair (R : TRS sigma nu) where
  weak : sigma × List (Term sigma nu) → sigma × List (Term sigma nu) → Prop
  strict : sigma × List (Term sigma nu) → sigma × List (Term sigma nu) → Prop
  weak_refl : ∀ c, weak c c
  weak_trans : ∀ {a b c}, weak a b → weak b c → weak a c
  weak_strict : ∀ {a b c}, weak a b → strict b c → strict a c
  strict_wf : WellFounded (fun d c => strict c d)
  arg_weak : ∀ (f : sigma) {xs ys : List (Term sigma nu)}, (∀ a ∈ xs, SN R a) →
    ArgStep R xs ys → weak (f, xs) (f, ys)
  pair_strict : ∀ rule ∈ R, ∀ (σ : Subst sigma nu) (f : sigma) (largs : List (Term sigma nu)),
    rule.lhs = .app f largs → ∀ (g : sigma) (targs : List (Term sigma nu)),
    IsSubterm (.app g targs) rule.rhs → IsDefined R g →
    (∀ a ∈ Subst.applyList σ largs, SN R a) → (∀ a ∈ Subst.applyList σ targs, SN R a) →
    strict (f, Subst.applyList σ largs) (g, Subst.applyList σ targs)

theorem reach_weak {R : TRS sigma nu} (P : CallReductionPair R) (f : sigma)
    {xs ys : List (Term sigma nu)} (h : Relation.ReflTransGen (ArgStep R) xs ys)
    (hxs : ∀ a ∈ xs, SN R a) : P.weak (f, xs) (f, ys) ∧ ∀ a ∈ ys, SN R a := by
  induction h with
  | refl => exact ⟨P.weak_refl _, hxs⟩
  | tail _ hstep ih =>
    obtain ⟨hw, hsn⟩ := ih
    exact ⟨P.weak_trans hw (P.arg_weak f hsn hstep), argStep_sn hsn hstep⟩

theorem minChainStep_strict {R : TRS sigma nu} (P : CallReductionPair R)
    {c d : sigma × List (Term sigma nu)} (h : MinChainStep R c d) : P.strict c d := by
  obtain ⟨hcSN, hdSN, xs, hreach, rule, hrule, σ, hl, targs, hsub, hdef, hd⟩ := h
  obtain ⟨hw, hxs⟩ := reach_weak P c.1 hreach hcSN
  obtain ⟨g0, largs, hg0⟩ := lhs_eq_app rule
  have hl' := hl
  rw [hg0, Subst.apply_app] at hl'
  simp only [Term.app.injEq] at hl'
  obtain ⟨hf, hxsEq⟩ := hl'
  have hstrict := P.pair_strict rule hrule σ g0 largs hg0 d.1 targs hsub hdef
    (by rw [← hxsEq]; exact hxs) (by rw [← hd]; exact hdSN)
  rw [← hf, ← hxsEq, ← hd] at hstrict
  exact P.weak_strict hw hstrict

/-- The reduction-pair criterion for termination. -/
theorem terminating_of_callReductionPair [DecidableEq nu] (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) (P : CallReductionPair R) :
    ∀ t : Term sigma nu, SN R t :=
  terminating_of_minChain_wf R hvars
    (Subrelation.wf (fun {_ _} h => minChainStep_strict P h) P.strict_wf)

/-! ## The variable condition is necessary -/

/-- The rule `c → x` with a right-hand-side variable absent from the left-hand side. -/
def freshRule : Rule Unit Nat where
  lhs := .app () []
  rhs := .var 0
  lhs_isApp := rfl

def freshTRS : TRS Unit Nat := [freshRule]

theorem freshTRS_no_pairs (c d : Unit × List (Term Unit Nat)) : ¬ MinChainStep freshTRS c d := by
  rintro ⟨-, -, -, -, rule, hrule, -, -, targs, hsub, -, -⟩
  simp only [freshTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  subst hrule
  cases hsub

theorem freshTRS_loop : Step freshTRS (.app () []) (.app () []) :=
  Step.root ⟨freshRule, List.mem_cons_self, fun _ => .app () [], rfl, rfl⟩

/-- Without the variable condition, a well-founded (empty) chain relation does not give
termination. -/
theorem fresh_variable_control :
    WellFounded (fun d c => MinChainStep freshTRS c d) ∧
      ¬ SN freshTRS (.app () []) := by
  refine ⟨⟨fun c => Acc.intro _ fun d h => absurd h (freshTRS_no_pairs c d)⟩, fun h => ?_⟩
  have hloop : ∀ t, SN freshTRS t → t ≠ .app () [] := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro heq
      subst heq
      exact ih _ freshTRS_loop rfl
  exact hloop _ h rfl


/-! ## The subterm criterion -/

/-- `u` is an argument of `t`. -/
def ImmSub (u t : Term sigma nu) : Prop := ∃ f args, t = .app f args ∧ u ∈ args

/-- One rewrite step or one passage to an argument; `StepOrSub R u t` places `u` below `t`. -/
def StepOrSub (R : TRS sigma nu) (u t : Term sigma nu) : Prop := Step R t u ∨ ImmSub u t

/-- A rewrite step inside a subterm lifts to the whole term. -/
theorem step_lift_subterm {R : TRS sigma nu} {u t : Term sigma nu} (h : IsSubterm u t) :
    ∀ {v}, Step R u v → ∃ t', Step R t t' ∧ IsSubterm v t' := by
  induction h with
  | refl =>
    intro v hv
    exact ⟨v, hv, .refl v⟩
  | arg f args hmem _ ih =>
    intro v hv
    obtain ⟨a', ha', hsub⟩ := ih hv
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
    exact ⟨.app f (pre ++ a' :: post), Step.arg f pre post ha', .arg f _ (by simp) hsub⟩

/-- Strongly normalizing terms, and all their subterms, are accessible for rewriting combined
with passing to arguments. -/
theorem acc_stepOrSub_of_subterm {R : TRS sigma nu} :
    ∀ t : Term sigma nu, SN R t → ∀ u, IsSubterm u t → Acc (StepOrSub R) u := by
  intro t ht
  induction ht with
  | intro t _ iht =>
    suffices key : ∀ n, ∀ u, Term.size u ≤ n → IsSubterm u t → Acc (StepOrSub R) u from
      fun u hu => key _ u le_rfl hu
    intro n
    induction n with
    | zero =>
      intro u hsz
      exact absurd hsz (by have := Term.one_le_size u; omega)
    | succ n ihn =>
      intro u hsz hu
      refine Acc.intro _ fun v hv => ?_
      rcases hv with hstep | ⟨f, args, rfl, hmem⟩
      · obtain ⟨t', htt', hsub⟩ := step_lift_subterm hu hstep
        exact iht t' htt' v hsub
      · have hlt := Term.size_lt_of_mem (f := f) hmem
        exact ihn v (by omega) (hu.of_app_arg hmem)

theorem acc_stepOrSub_of_sn {R : TRS sigma nu} {t : Term sigma nu} (ht : SN R t) :
    Acc (StepOrSub R) t :=
  acc_stepOrSub_of_subterm t ht t (.refl t)

/-- `w` is a proper subterm of `t`. -/
inductive ProperSubterm : Term sigma nu → Term sigma nu → Prop
  | arg {w a : Term sigma nu} (f : sigma) (args : List (Term sigma nu)) :
      a ∈ args → IsSubterm w a → ProperSubterm w (.app f args)

theorem IsSubterm.subst (σ : Subst sigma nu) {w t : Term sigma nu} (h : IsSubterm w t) :
    IsSubterm (Subst.apply σ w) (Subst.apply σ t) := by
  induction h with
  | refl => exact .refl _
  | arg f args hmem _ ih =>
    rw [Subst.apply_app, Subst.applyList_eq_map]
    exact .arg f _ (List.mem_map_of_mem hmem) ih

theorem ProperSubterm.subst (σ : Subst sigma nu) {w t : Term sigma nu} (h : ProperSubterm w t) :
    ProperSubterm (Subst.apply σ w) (Subst.apply σ t) := by
  cases h with
  | arg f args hmem hsub =>
    rw [Subst.apply_app, Subst.applyList_eq_map]
    exact .arg f _ (List.mem_map_of_mem hmem) (hsub.subst σ)

theorem IsSubterm.reflTransGen {R : TRS sigma nu} {w t : Term sigma nu} (h : IsSubterm w t) :
    Relation.ReflTransGen (StepOrSub R) w t := by
  induction h with
  | refl => exact .refl
  | arg f args hmem _ ih => exact ih.tail (Or.inr ⟨f, args, rfl, hmem⟩)

theorem ProperSubterm.transGen {R : TRS sigma nu} {w t : Term sigma nu} (h : ProperSubterm w t) :
    Relation.TransGen (StepOrSub R) w t := by
  cases h with
  | arg f args hmem hsub => exact Relation.TransGen.tail' hsub.reflTransGen (Or.inr ⟨f, args, rfl, hmem⟩)

theorem steps_reflTransGen {R : TRS sigma nu} {x y : Term sigma nu}
    (h : Relation.ReflTransGen (Step R) x y) : Relation.ReflTransGen (StepOrSub R) y x := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact Relation.ReflTransGen.head (Or.inl hst) ih

/-- Position `i` of an argument list after one argument step comes from position `i` before it by
at most one rewrite step. -/
theorem argStep_getElem? {R : TRS sigma nu} {xs ys : List (Term sigma nu)} (h : ArgStep R xs ys)
    (i : Nat) (y : Term sigma nu) (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ Relation.ReflTransGen (Step R) x y := by
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

theorem argSteps_getElem? {R : TRS sigma nu} {xs ys : List (Term sigma nu)}
    (h : Relation.ReflTransGen (ArgStep R) xs ys) (i : Nat) :
    ∀ y, ys[i]? = some y → ∃ x, xs[i]? = some x ∧ Relation.ReflTransGen (Step R) x y := by
  induction h with
  | refl => exact fun y hy => ⟨y, hy, .refl⟩
  | tail _ hstep ih =>
    intro y hy
    obtain ⟨m, hm, hmy⟩ := argStep_getElem? hstep i y hy
    obtain ⟨x, hx, hxm⟩ := ih m hm
    exact ⟨x, hx, hxm.trans hmy⟩

/-- The projection of a call to its `proj f`-th argument. -/
def projArg (proj : sigma → Nat) (c : sigma × List (Term sigma nu)) : Option (Term sigma nu) :=
  c.2[proj c.1]?

/-- The subterm criterion: every dependency pair strictly decreases the projected argument in the
proper-subterm order. -/
def SubtermCriterion (R : TRS sigma nu) (proj : sigma → Nat) : Prop :=
  ∀ rule ∈ R, ∀ (f : sigma) (largs : List (Term sigma nu)), rule.lhs = .app f largs →
    ∀ (g : sigma) (targs : List (Term sigma nu)), IsSubterm (.app g targs) rule.rhs → IsDefined R g →
      ∃ l0 t0, largs[proj f]? = some l0 ∧ targs[proj g]? = some t0 ∧ ProperSubterm t0 l0

theorem minChainStep_proj {R : TRS sigma nu} {proj : sigma → Nat} (hsc : SubtermCriterion R proj)
    {c d : sigma × List (Term sigma nu)} (h : MinChainStep R c d) :
    ∃ x y, projArg proj c = some x ∧ projArg proj d = some y ∧
      Relation.TransGen (StepOrSub R) y x := by
  obtain ⟨-, -, xs, hreach, rule, hrule, σ, hl, targs, hsub, hdef, hd⟩ := h
  obtain ⟨g0, largs, hg0⟩ := lhs_eq_app rule
  have hl' := hl
  rw [hg0, Subst.apply_app] at hl'
  simp only [Term.app.injEq] at hl'
  obtain ⟨hf, hxsEq⟩ := hl'
  obtain ⟨l0, t0, hl0, ht0, hprop⟩ := hsc rule hrule g0 largs hg0 d.1 targs hsub hdef
  have hx' : xs[proj c.1]? = some (Subst.apply σ l0) := by
    rw [hxsEq, Subst.applyList_eq_map, List.getElem?_map, hf, hl0]
    rfl
  have hy : d.2[proj d.1]? = some (Subst.apply σ t0) := by
    rw [hd, Subst.applyList_eq_map, List.getElem?_map, ht0]
    rfl
  obtain ⟨x, hx, hxx⟩ := argSteps_getElem? hreach (proj c.1) _ hx'
  exact ⟨x, _, hx, hy,
    Relation.TransGen.trans_left (hprop.subst σ).transGen (steps_reflTransGen hxx)⟩

/-- The subterm criterion makes the minimal chain relation well founded. -/
theorem minChain_wf_of_subtermCriterion {R : TRS sigma nu} {proj : sigma → Nat}
    (hsc : SubtermCriterion R proj) : WellFounded (fun d c => MinChainStep R c d) := by
  have key : ∀ x, Acc (Relation.TransGen (StepOrSub R)) x →
      ∀ c, projArg proj c = some x → Acc (fun d c => MinChainStep R c d) c := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro c hc
      refine Acc.intro _ fun d hd => ?_
      obtain ⟨x', y, hx', hy, hyx⟩ := minChainStep_proj hsc hd
      rw [hc] at hx'
      cases hx'
      exact ih y hyx d hy
  constructor
  intro c
  refine Acc.intro _ fun d hd => ?_
  obtain ⟨-, y, -, hy, -⟩ := minChainStep_proj hsc hd
  have hysn : SN R y := hd.2.1 y (List.mem_of_getElem? hy)
  exact key y (acc_stepOrSub_of_sn hysn).transGen d hy

/-- Termination by the subterm criterion. -/
theorem terminating_of_subtermCriterion [DecidableEq nu] (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) {proj : sigma → Nat}
    (hsc : SubtermCriterion R proj) : ∀ t : Term sigma nu, SN R t :=
  terminating_of_minChain_wf R hvars (minChain_wf_of_subtermCriterion hsc)

theorem not_isSubterm_app_var {g : sigma} {targs : List (Term sigma nu)} {x : nu} :
    ¬ IsSubterm (.app g targs) (.var x) := by
  intro h
  cases h

/-! ## The free recursor as a first-order rewrite system -/

/-- The four symbols of the free recursor. -/
inductive FreeSym
  | zero
  | succ
  | wrap
  | recur
  deriving DecidableEq

/-- `recur(b, s, zero) → b`. -/
def zeroRule : Rule FreeSym Nat where
  lhs := .app .recur [.var 0, .var 1, .app .zero []]
  rhs := .var 0
  lhs_isApp := rfl

/-- `recur(b, s, succ(n)) → wrap(s, recur(b, s, n))`. -/
def succRule : Rule FreeSym Nat where
  lhs := .app .recur [.var 0, .var 1, .app .succ [.var 2]]
  rhs := .app .wrap [.var 1, .app .recur [.var 0, .var 1, .var 2]]
  lhs_isApp := rfl

/-- The free recursor. -/
def freeRecursorTRS : TRS FreeSym Nat := [zeroRule, succRule]

theorem freeRecursorTRS_vars :
    ∀ rule ∈ freeRecursorTRS, Term.vars rule.rhs ⊆ Term.vars rule.lhs := by
  intro rule hrule
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · intro x hx
    simp [zeroRule] at hx ⊢
    omega
  · intro x hx
    simp [succRule] at hx ⊢
    omega

theorem freeRecursorTRS_defined_iff (g : FreeSym) : IsDefined freeRecursorTRS g ↔ g = .recur := by
  constructor
  · rintro ⟨rule, hrule, largs, hl⟩
    simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · simp only [zeroRule, Term.app.injEq] at hl
      exact hl.1.symm
    · simp only [succRule, Term.app.injEq] at hl
      exact hl.1.symm
  · rintro rfl
    exact ⟨zeroRule, List.mem_cons_self, _, rfl⟩

/-- The only `recur`-rooted subterm of the successor rule's right-hand side is its recursive call. -/
theorem succRule_rhs_recur_subterm {targs : List (Term FreeSym Nat)}
    (h : IsSubterm (.app .recur targs) succRule.rhs) : targs = [.var 0, .var 1, .var 2] := by
  simp only [succRule] at h
  cases h with
  | arg f args hmem hsub =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact absurd hsub not_isSubterm_app_var
    · cases hsub with
      | refl => rfl
      | arg f' args' hmem' hsub' =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
        rcases hmem' with rfl | rfl | rfl <;> exact absurd hsub' not_isSubterm_app_var

/-- The call projection of the free recursor reads the counter. -/
def freeProj : FreeSym → Nat
  | .recur => 2
  | _ => 0

theorem freeRecursorTRS_subtermCriterion : SubtermCriterion freeRecursorTRS freeProj := by
  intro rule hrule f largs hl g targs hsub hdef
  rw [freeRecursorTRS_defined_iff] at hdef
  subst hdef
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · simp only [zeroRule] at hsub
    exact absurd hsub not_isSubterm_app_var
  · have ht := succRule_rhs_recur_subterm hsub
    subst ht
    simp only [succRule, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨Term.app FreeSym.succ [Term.var 2], Term.var 2, rfl, rfl,
      ProperSubterm.arg FreeSym.succ [Term.var 2] List.mem_cons_self (IsSubterm.refl _)⟩

/-- The free recursor terminates by dependency pairs: the subterm criterion on the counter
argument makes every minimal chain finite. -/
theorem freeRecursorTRS_terminating : ∀ t : Term FreeSym Nat, SN freeRecursorTRS t :=
  terminating_of_subtermCriterion freeRecursorTRS freeRecursorTRS_vars
    freeRecursorTRS_subtermCriterion

theorem freeRecursorTRS_wellFounded : WellFounded (fun u t => Step freeRecursorTRS t u) :=
  ⟨freeRecursorTRS_terminating⟩

/-- The wrapper symbol is not defined in the free recursor. -/
theorem freeRecursorTRS_wrap_not_defined : ¬ IsDefined freeRecursorTRS FreeSym.wrap := by
  rw [freeRecursorTRS_defined_iff]
  exact fun h => FreeSym.noConfusion h

/-- Control C15: a pair whose target is the whole wrapper right-hand side is no chain step, because
the wrapper symbol is not defined; only the recursive call is extracted. -/
theorem freeRecursor_no_wrapper_target (c : FreeSym × List (Term FreeSym Nat))
    (ys : List (Term FreeSym Nat)) : ¬ MinChainStep freeRecursorTRS c (FreeSym.wrap, ys) := by
  rintro ⟨-, -, -, -, -, -, -, -, -, -, hdef, -⟩
  exact freeRecursorTRS_wrap_not_defined hdef

end OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
