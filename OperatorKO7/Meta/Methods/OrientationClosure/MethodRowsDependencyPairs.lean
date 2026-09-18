import OperatorKO7.Meta.Methods.OrientationClosure.ProcessorSemantics
import OperatorKO7.Meta.Methods.OrientationClosure.SizeChangeTermination
import Mathlib.Tactic

/-!
# Dependency-pair method rows

Seven rows of the method universe are processors of the dependency-pair framework applied to the
free recursor `freeRecursorTRS` over the generic first-order library. Each row proves termination
of the free recursor from its own data through the minimal-chain theorem of
`DependencyPairSoundness` and the processor semantics of `ProcessorSemantics`.

The linear interpretations used by the reduction-pair rows are weakly monotone: the wrapper and the
recursor may give the payload coefficient `0`. A direct interpretation must retain the payload in
the wrapper and then fails by the coupling barrier; the weak relation of a reduction pair carries no
such requirement (`counterLinear_rulesWeak`), and a payload-retaining wrapper breaks the weak
rules again (`retainLinear_not_rulesWeak`).

Rows: `dpSubtermCriterion` (projection to the counter), `dpReductionPairProcessor` (linear
reduction pair on calls), `dpArgumentFiltering` (filtered-term size; `size_filterTerm` computes the
filtering), `dpNeutralProcessors` (identity output), `dpReductionTriples` (three relations with
`rulesWeak` strictly inside `pairWeak`), `dpProcessorClassification` (processor sequences with
their applicability conditions and composed soundness), `sizeChangeTerminationEscape` (size-change
graphs computed from the dependency pairs of any rewrite system).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics

/-- Arities of the free symbols. -/
def freeArity : FreeSym → Nat
  | .zero => 0
  | .succ => 1
  | .wrap => 2
  | .recur => 3

/-- First-order terms over the free symbols. -/
abbrev FTerm : Type := Term FreeSym Nat

/-- Calls over the free symbols. -/
abbrev FCall : Type := Call FreeSym Nat

/-- Dependency-pair problems over the free symbols. -/
abbrev FProblem : Type := FCall → FCall → Prop

/-- Termination of the free recursor. -/
def FreeTerminates : Prop := ∀ t : FTerm, SN freeRecursorTRS t

/-- The dependency-pair problem of the free recursor is finite. -/
theorem free_finiteDP : FiniteDP freeRecursorTRS (dpPairs freeRecursorTRS) :=
  Subrelation.wf (fun {_ _} h => (chainP_dpPairs_iff freeRecursorTRS _ _).1 h)
    (minChain_wf_of_subtermCriterion freeRecursorTRS_subtermCriterion)

/-- The recursive call of the successor rule. -/
theorem succRule_rhs_call :
    IsSubterm (.app FreeSym.recur [.var 0, .var 1, .var 2] : FTerm) succRule.rhs := by
  show IsSubterm _ (Term.app FreeSym.wrap
    [Term.var 1, Term.app FreeSym.recur [Term.var 0, Term.var 1, Term.var 2]])
  exact IsSubterm.arg FreeSym.wrap _ (by simp) (IsSubterm.refl _)

/-- Source and target call of the dependency pair of the free recursor. -/
def dpSource : FCall := (.recur, [.var 0, .var 1, .app .succ [.var 2]])

def dpTarget : FCall := (.recur, [.var 0, .var 1, .var 2])

theorem free_dpPair : dpPairs freeRecursorTRS dpSource dpTarget :=
  ⟨succRule, by simp [freeRecursorTRS], Subst.id, by simp [dpSource, succRule, Subst.id],
    [.var 0, .var 1, .var 2], succRule_rhs_call, (freeRecursorTRS_defined_iff _).2 rfl,
    by simp [dpTarget, Subst.id]⟩

/-- An empty problem is finite. -/
theorem finiteDP_empty (P : FProblem) (h : ∀ c d, ¬ P c d) : FiniteDP freeRecursorTRS P :=
  ⟨fun _ => Acc.intro _ fun _ hd => absurd hd.2.2.choose_spec.2 (h _ _)⟩

/-! ## Row: dpSubtermCriterion -/

/-- Native data: a simple projection, one argument position per symbol. -/
abbrev dpSubtermCriterionData : Type := FreeSym → Nat

/-- Hirokawa and Middeldorp (Dependency pairs revisited, RTA 2004): the projection selects an
argument position of every defined symbol. -/
def dpSubtermCriterionLaws (π : dpSubtermCriterionData) : Prop :=
  ∀ g, IsDefined freeRecursorTRS g → π g < freeArity g

/-- Every dependency pair strictly decreases the projected argument in the subterm order. -/
def dpSubtermCriterionAccepts (π : dpSubtermCriterionData) : Prop :=
  SubtermCriterion freeRecursorTRS π

/-- Verdict: escape. -/
def dpSubtermCriterionResult (π : dpSubtermCriterionData) : Prop :=
  dpSubtermCriterionAccepts π ∧ FreeTerminates

theorem dpSubtermCriterion_sound :
    ∀ π, dpSubtermCriterionLaws π → dpSubtermCriterionAccepts π → FreeTerminates :=
  fun _ _ h => terminating_of_subtermCriterion freeRecursorTRS freeRecursorTRS_vars h

def dpSubtermCriterionWitness : dpSubtermCriterionData := freeProj

theorem dpSubtermCriterionWitness_laws : dpSubtermCriterionLaws dpSubtermCriterionWitness := by
  intro g hg
  rw [freeRecursorTRS_defined_iff] at hg
  subst hg
  decide

theorem dpSubtermCriterionWitness_result : dpSubtermCriterionResult dpSubtermCriterionWitness :=
  ⟨freeRecursorTRS_subtermCriterion, freeRecursorTRS_terminating⟩

/-- The projection descends from `succ n` to `n`, and the wrapper call is never a chain target
(control C15). -/
theorem dpSubtermCriterionWitness_feature :
    ProperSubterm (.var 2 : FTerm) (.app FreeSym.succ [.var 2]) ∧
      ∀ (c : FCall) (ys : List FTerm), ¬ MinChainStep freeRecursorTRS c (FreeSym.wrap, ys) :=
  ⟨ProperSubterm.arg FreeSym.succ [Term.var 2] List.mem_cons_self (IsSubterm.refl _),
    freeRecursor_no_wrapper_target⟩

/-- The projection to the payload. -/
def payloadProj : FreeSym → Nat
  | .recur => 1
  | _ => 0

/-- Projecting to the payload keeps the laws and loses the criterion: the payload of the recursive
call equals the payload of the source. -/
theorem dpSubtermCriterion_mutation :
    dpSubtermCriterionLaws payloadProj ∧ ¬ dpSubtermCriterionAccepts payloadProj := by
  refine ⟨?_, fun h => ?_⟩
  · intro g hg
    rw [freeRecursorTRS_defined_iff] at hg
    subst hg
    decide
  · obtain ⟨l0, t0, hl0, ht0, hprop⟩ := h succRule (by simp [freeRecursorTRS]) FreeSym.recur
      [.var 0, .var 1, .app .succ [.var 2]] rfl FreeSym.recur [.var 0, .var 1, .var 2]
      succRule_rhs_call ((freeRecursorTRS_defined_iff _).2 rfl)
    simp [payloadProj] at hl0 ht0
    subst hl0
    subst ht0
    cases hprop

/-! ## Linear interpretations on calls -/

/-- Linear interpretation data: constants and argument coefficients of the free symbols, and of the
marked call symbol. -/
structure LinearData where
  c : FreeSym → Nat
  a : FreeSym → Nat → Nat
  mc : Nat
  ma : Nat → Nat

mutual
/-- Evaluation of a term; variables evaluate to `1`. -/
def linEval (L : LinearData) : FTerm → Nat
  | .var _ => 1
  | .app f args => L.c f + linList L f 0 args
/-- Weighted sum over an argument list from position `i`. -/
def linList (L : LinearData) (f : FreeSym) : Nat → List FTerm → Nat
  | _, [] => 0
  | i, t :: ts => L.a f i * linEval L t + linList L f (i + 1) ts
end

/-- Weighted sum of the arguments of a call from position `i`. -/
def markedList (L : LinearData) : Nat → List FTerm → Nat
  | _, [] => 0
  | i, t :: ts => L.ma i * linEval L t + markedList L (i + 1) ts

/-- Evaluation of a call. -/
def markedEval (L : LinearData) (c : FCall) : Nat := L.mc + markedList L 0 c.2

theorem linList_le (L : LinearData) (f : FreeSym) {x y : FTerm} (h : linEval L y ≤ linEval L x) :
    ∀ (i : Nat) (pre post : List FTerm),
      linList L f i (pre ++ y :: post) ≤ linList L f i (pre ++ x :: post) := by
  intro i pre post
  induction pre generalizing i with
  | nil =>
    simp only [List.nil_append, linList]
    have := Nat.mul_le_mul_left (L.a f i) h
    omega
  | cons z pre ih =>
    simp only [List.cons_append, linList]
    have := ih (i + 1)
    omega

theorem markedList_le (L : LinearData) {x y : FTerm} (h : linEval L y ≤ linEval L x) :
    ∀ (i : Nat) (pre post : List FTerm),
      markedList L i (pre ++ y :: post) ≤ markedList L i (pre ++ x :: post) := by
  intro i pre post
  induction pre generalizing i with
  | nil =>
    simp only [List.nil_append, markedList]
    have := Nat.mul_le_mul_left (L.ma i) h
    omega
  | cons z pre ih =>
    simp only [List.cons_append, markedList]
    have := ih (i + 1)
    omega

/-- The rules of `R` weakly decrease at every instance. -/
def RulesWeak (L : LinearData) (R : TRS FreeSym Nat) : Prop :=
  ∀ rule ∈ R, ∀ σ : Subst FreeSym Nat,
    linEval L (Subst.apply σ rule.rhs) ≤ linEval L (Subst.apply σ rule.lhs)

/-- Every dependency pair of `R` strictly decreases at every instance. -/
def PairsStrict (L : LinearData) (R : TRS FreeSym Nat) : Prop :=
  ∀ rule ∈ R, ∀ (σ : Subst FreeSym Nat) (f : FreeSym) (largs : List FTerm),
    rule.lhs = .app f largs → ∀ (g : FreeSym) (targs : List FTerm),
      IsSubterm (.app g targs) rule.rhs → IsDefined R g →
        markedEval L (g, Subst.applyList σ targs) < markedEval L (f, Subst.applyList σ largs)

theorem linEval_step_le {L : LinearData} {R : TRS FreeSym Nat} (hR : RulesWeak L R)
    {t u : FTerm} (h : Step R t u) : linEval L u ≤ linEval L t := by
  induction h with
  | root h =>
    obtain ⟨rule, hrule, σ, rfl, rfl⟩ := h
    exact hR rule hrule σ
  | arg f pre post _ ih =>
    simp only [linEval]
    have := linList_le L f ih 0 pre post
    omega

theorem markedEval_argStep_le {L : LinearData} {R : TRS FreeSym Nat} (hR : RulesWeak L R)
    (f : FreeSym) {xs ys : List FTerm} (h : ArgStep R xs ys) :
    markedEval L (f, ys) ≤ markedEval L (f, xs) := by
  obtain ⟨pre, post, x, y, rfl, rfl, hxy⟩ := h
  simp only [markedEval]
  have := markedList_le L (linEval_step_le hR hxy) 0 pre post
  omega

/-- The reduction pair on calls induced by linear data. -/
def linearPair (L : LinearData) (R : TRS FreeSym Nat) (hR : RulesWeak L R)
    (hP : PairsStrict L R) : CallReductionPair R where
  weak c d := markedEval L d ≤ markedEval L c
  strict c d := markedEval L d < markedEval L c
  weak_refl _ := le_rfl
  weak_trans h₁ h₂ := le_trans h₂ h₁
  weak_strict h₁ h₂ := lt_of_lt_of_le h₂ h₁
  strict_wf := InvImage.wf (markedEval L) Nat.lt_wfRel.wf
  arg_weak f _ _ _ h := markedEval_argStep_le hR f h
  pair_strict rule hrule σ f largs hl g targs hsub hdef _ _ :=
    hP rule hrule σ f largs hl g targs hsub hdef

/-- Linear data whose rules weakly decrease and whose pairs strictly decrease prove termination of
any rewrite system satisfying the variable condition. -/
theorem linear_terminating (L : LinearData) (R : TRS FreeSym Nat)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) (hR : RulesWeak L R)
    (hP : PairsStrict L R) : ∀ t : FTerm, SN R t :=
  terminating_of_callReductionPair R hvars (linearPair L R hR hP)

theorem pairsStrict_dpPairs {L : LinearData} {R : TRS FreeSym Nat} (hP : PairsStrict L R)
    {c d : FCall} (h : dpPairs R c d) : markedEval L d < markedEval L c := by
  obtain ⟨rule, hrule, σ, hl, targs, hsub, hdef, hd⟩ := h
  obtain ⟨f, largs, hf⟩ := lhs_eq_app rule
  rw [hf, Subst.apply_app] at hl
  simp only [Term.app.injEq] at hl
  obtain ⟨hc1, hc2⟩ := hl
  have key := hP rule hrule σ f largs hf d.1 targs hsub hdef
  have hc : c = (f, Subst.applyList σ largs) := Prod.ext hc1 hc2
  have hd' : d = (d.1, Subst.applyList σ targs) := Prod.ext rfl hd
  rw [hc, hd']
  exact key

/-! ### The counter interpretation -/

/-- Constants `zero = succ = recur = 1`, `wrap = 0`; coefficients `succ: 1`, `wrap: 0, 1`,
`recur: 1, 0, 1`; the marked call reads the counter. -/
def counterLinear : LinearData where
  c := fun
    | .zero => 1
    | .succ => 1
    | .wrap => 0
    | .recur => 1
  a := fun f i => match f, i with
    | .succ, 0 => 1
    | .wrap, 1 => 1
    | .recur, 0 => 1
    | .recur, 2 => 1
    | _, _ => 0
  mc := 0
  ma := fun
    | 2 => 1
    | _ => 0

@[simp] theorem counterLinear_c_zero : counterLinear.c .zero = 1 := rfl
@[simp] theorem counterLinear_c_succ : counterLinear.c .succ = 1 := rfl
@[simp] theorem counterLinear_c_wrap : counterLinear.c .wrap = 0 := rfl
@[simp] theorem counterLinear_c_recur : counterLinear.c .recur = 1 := rfl
@[simp] theorem counterLinear_a_succ0 : counterLinear.a .succ 0 = 1 := rfl
@[simp] theorem counterLinear_a_wrap0 : counterLinear.a .wrap 0 = 0 := rfl
@[simp] theorem counterLinear_a_wrap1 : counterLinear.a .wrap 1 = 1 := rfl
@[simp] theorem counterLinear_a_recur0 : counterLinear.a .recur 0 = 1 := rfl
@[simp] theorem counterLinear_a_recur1 : counterLinear.a .recur 1 = 0 := rfl
@[simp] theorem counterLinear_a_recur2 : counterLinear.a .recur 2 = 1 := rfl
@[simp] theorem counterLinear_mc : counterLinear.mc = 0 := rfl
@[simp] theorem counterLinear_ma0 : counterLinear.ma 0 = 0 := rfl
@[simp] theorem counterLinear_ma1 : counterLinear.ma 1 = 0 := rfl
@[simp] theorem counterLinear_ma2 : counterLinear.ma 2 = 1 := rfl

theorem counterLinear_rulesWeak : RulesWeak counterLinear freeRecursorTRS := by
  intro rule hrule σ
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · simp [zeroRule, linEval, linList]
    omega
  · simp [succRule, linEval, linList]

/-- The only dependency pair of the free recursor, at every instance. -/
theorem free_pair_shape {R : TRS FreeSym Nat} (hRdef : R = freeRecursorTRS) {rule : Rule FreeSym Nat}
    (hrule : rule ∈ R) {f : FreeSym} {largs : List FTerm} (hl : rule.lhs = .app f largs)
    {g : FreeSym} {targs : List FTerm} (hsub : IsSubterm (.app g targs) rule.rhs)
    (hdef : IsDefined R g) :
    rule = succRule ∧ f = .recur ∧ largs = [.var 0, .var 1, .app .succ [.var 2]] ∧
      g = .recur ∧ targs = [.var 0, .var 1, .var 2] := by
  subst hRdef
  rw [freeRecursorTRS_defined_iff] at hdef
  subst hdef
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · exact absurd hsub (by simp only [zeroRule]; exact not_isSubterm_app_var)
  · have ht := succRule_rhs_recur_subterm hsub
    simp only [succRule, Term.app.injEq] at hl
    exact ⟨rfl, hl.1.symm, hl.2.symm, rfl, ht⟩

theorem counterLinear_pairsStrict : PairsStrict counterLinear freeRecursorTRS := by
  intro rule hrule σ f largs hl g targs hsub hdef
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := free_pair_shape rfl hrule hl hsub hdef
  simp [markedEval, markedList, linEval, linList]

/-- A second interpretation that also reads the base argument of the call. -/
def counterBaseLinear : LinearData :=
  { counterLinear with ma := fun | 0 => 1 | 2 => 1 | _ => 0 }

@[simp] theorem counterBaseLinear_c (f : FreeSym) : counterBaseLinear.c f = counterLinear.c f :=
  rfl
@[simp] theorem counterBaseLinear_a (f : FreeSym) (i : Nat) :
    counterBaseLinear.a f i = counterLinear.a f i := rfl
@[simp] theorem counterBaseLinear_mc : counterBaseLinear.mc = 0 := rfl
@[simp] theorem counterBaseLinear_ma0 : counterBaseLinear.ma 0 = 1 := rfl
@[simp] theorem counterBaseLinear_ma1 : counterBaseLinear.ma 1 = 0 := rfl
@[simp] theorem counterBaseLinear_ma2 : counterBaseLinear.ma 2 = 1 := rfl

theorem counterBaseLinear_rulesWeak : RulesWeak counterBaseLinear freeRecursorTRS := by
  intro rule hrule σ
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · simp [zeroRule, linEval, linList]
    omega
  · simp [succRule, linEval, linList]

theorem counterBaseLinear_pairsStrict : PairsStrict counterBaseLinear freeRecursorTRS := by
  intro rule hrule σ f largs hl g targs hsub hdef
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := free_pair_shape rfl hrule hl hsub hdef
  simp [markedEval, markedList, linEval, linList]

/-- A wrapper that retains its payload. -/
def retainLinear : LinearData :=
  { counterLinear with
    a := fun f i => match f, i with
      | .succ, 0 => 1
      | .wrap, 0 => 1
      | .wrap, 1 => 1
      | .recur, 0 => 1
      | .recur, 2 => 1
      | _, _ => 0 }

/-- Retaining the payload in the wrapper breaks the weak rules: the successor rule copies the
payload. -/
theorem retainLinear_not_rulesWeak : ¬ RulesWeak retainLinear freeRecursorTRS := by
  intro h
  have := h succRule (by simp [freeRecursorTRS])
    (fun _ => Term.app FreeSym.succ [Term.app FreeSym.succ [Term.app FreeSym.zero []]])
  simp [succRule, retainLinear, counterLinear, linEval, linList] at this

/-- Coefficient `0` on the counter of the marked call. -/
def blindLinear : LinearData := { counterLinear with ma := fun _ => 0 }

@[simp] theorem blindLinear_c (f : FreeSym) : blindLinear.c f = counterLinear.c f := rfl
@[simp] theorem blindLinear_a (f : FreeSym) (i : Nat) : blindLinear.a f i = counterLinear.a f i :=
  rfl
@[simp] theorem blindLinear_mc : blindLinear.mc = 0 := rfl
@[simp] theorem blindLinear_ma (i : Nat) : blindLinear.ma i = 0 := rfl

theorem blindLinear_markedList (i : Nat) (ts : List FTerm) : markedList blindLinear i ts = 0 := by
  induction ts generalizing i with
  | nil => rfl
  | cons t ts ih => simp [markedList, ih]

theorem blindLinear_markedEval (c : FCall) : markedEval blindLinear c = 0 := by
  simp [markedEval, blindLinear_markedList]

theorem blindLinear_rulesWeak : RulesWeak blindLinear freeRecursorTRS := by
  intro rule hrule σ
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · simp [zeroRule, linEval, linList]
    omega
  · simp [succRule, linEval, linList]

theorem blindLinear_not_pairsStrict : ¬ PairsStrict blindLinear freeRecursorTRS := by
  intro h
  have := h succRule (by simp [freeRecursorTRS]) Subst.id FreeSym.recur
    [.var 0, .var 1, .app .succ [.var 2]] rfl FreeSym.recur [.var 0, .var 1, .var 2]
    succRule_rhs_call ((freeRecursorTRS_defined_iff _).2 rfl)
  simp [blindLinear, counterLinear, markedEval, markedList] at this

/-! ## Row: dpReductionPairProcessor -/

/-- Native data: a linear interpretation over `ℕ` of the free symbols and the marked call. -/
abbrev dpReductionPairProcessorData : Type := LinearData

/-- Arts and Giesl (Termination of term rewriting using dependency pairs, TCS 236, 2000) with
reduction pairs (Kusakari, Nakamura and Toyama 1999): the rules weakly decrease at every instance
under a weakly monotone interpretation. -/
def dpReductionPairProcessorLaws (L : dpReductionPairProcessorData) : Prop :=
  RulesWeak L freeRecursorTRS

/-- Every dependency pair strictly decreases. -/
def dpReductionPairProcessorAccepts (L : dpReductionPairProcessorData) : Prop :=
  PairsStrict L freeRecursorTRS

/-- Verdict: escape. -/
def dpReductionPairProcessorResult (L : dpReductionPairProcessorData) : Prop :=
  dpReductionPairProcessorAccepts L ∧ FreeTerminates

theorem dpReductionPairProcessor_sound :
    ∀ L, dpReductionPairProcessorLaws L → dpReductionPairProcessorAccepts L → FreeTerminates :=
  fun L hR hP => linear_terminating L freeRecursorTRS freeRecursorTRS_vars hR hP

def dpReductionPairProcessorWitness : dpReductionPairProcessorData := counterLinear

theorem dpReductionPairProcessorWitness_laws :
    dpReductionPairProcessorLaws dpReductionPairProcessorWitness :=
  counterLinear_rulesWeak

theorem dpReductionPairProcessorWitness_result :
    dpReductionPairProcessorResult dpReductionPairProcessorWitness :=
  ⟨counterLinear_pairsStrict,
    dpReductionPairProcessor_sound _ counterLinear_rulesWeak counterLinear_pairsStrict⟩

/-- Two calls that separate the strict relations of the two accepted interpretations. -/
def sepSource : FCall :=
  (.recur, [.app .zero [], .app .zero [], .app .succ [.app .zero []]])

def sepTarget : FCall :=
  (.recur, [.app .succ [.app .succ [.app .zero []]], .app .zero [], .app .zero []])

/-- Weak rules with payload coefficient `0`, two accepted interpretations with different strict
relations, and the empty-pair source loop of a rule with a fresh right-hand variable. -/
theorem dpReductionPairProcessorWitness_feature :
    counterLinear.a .wrap 0 = 0 ∧ counterLinear.a .recur 1 = 0 ∧
      dpReductionPairProcessorLaws counterBaseLinear ∧
      dpReductionPairProcessorAccepts counterBaseLinear ∧
      markedEval counterLinear sepTarget < markedEval counterLinear sepSource ∧
      ¬ markedEval counterBaseLinear sepTarget < markedEval counterBaseLinear sepSource ∧
      (WellFounded (fun d c => MinChainStep freshTRS c d) ∧ ¬ SN freshTRS (.app () [])) := by
  refine ⟨rfl, rfl, counterBaseLinear_rulesWeak, counterBaseLinear_pairsStrict, ?_, ?_,
    fresh_variable_control⟩
  · simp [markedEval, markedList, linEval, linList, sepSource, sepTarget]
  · simp [markedEval, markedList, linEval, linList, sepSource, sepTarget]

/-- Setting the counter coefficient of the marked call to `0` keeps the laws and loses the strict
pairs; retaining the payload in the wrapper loses the laws. -/
theorem dpReductionPairProcessor_mutation :
    (dpReductionPairProcessorLaws blindLinear ∧ ¬ dpReductionPairProcessorAccepts blindLinear) ∧
      ¬ dpReductionPairProcessorLaws retainLinear :=
  ⟨⟨blindLinear_rulesWeak, blindLinear_not_pairsStrict⟩, retainLinear_not_rulesWeak⟩

/-! ## Row: dpArgumentFiltering -/

/-- The linear data of a filtering: every symbol costs `1`, kept positions have coefficient `1`, and
erased positions have coefficient `0`. -/
def filterLinear (π : FreeSym → List Nat) : LinearData where
  c := fun _ => 1
  a := fun f i => if i ∈ π f then 1 else 0
  mc := 1
  ma := fun i => if i ∈ π .recur then 1 else 0

theorem filterLinear_c (π : FreeSym → List Nat) (f : FreeSym) : (filterLinear π).c f = 1 := rfl

theorem filterLinear_a (π : FreeSym → List Nat) (f : FreeSym) (i : Nat) :
    (filterLinear π).a f i = if i ∈ π f then 1 else 0 := rfl

mutual
/-- The filtered term: erased argument positions are removed. -/
def filterTerm (π : FreeSym → List Nat) : FTerm → FTerm
  | .var x => .var x
  | .app f args => .app f (filterList π f 0 args)
/-- The filtered argument list from position `i`. -/
def filterList (π : FreeSym → List Nat) (f : FreeSym) : Nat → List FTerm → List FTerm
  | _, [] => []
  | i, t :: ts =>
      if i ∈ π f then filterTerm π t :: filterList π f (i + 1) ts else filterList π f (i + 1) ts
end

/-- The filtering computed on terms: the linear data of a filtering evaluate every term to the size
of its filtered term. -/
theorem size_filterTerm (π : FreeSym → List Nat) :
    ∀ t : FTerm, Term.size (filterTerm π t) = linEval (filterLinear π) t := by
  intro t
  induction t using Term.rec' with
  | hvar x => simp [filterTerm, linEval]
  | happ f args ih =>
    have key : ∀ i, Term.sizeList (filterList π f i args) = linList (filterLinear π) f i args := by
      induction args with
      | nil => intro i; simp [filterList, linList]
      | cons x xs ihl =>
        intro i
        have hx := ih x List.mem_cons_self
        have hxs := ihl (fun b hb => ih b (List.mem_cons_of_mem _ hb))
        by_cases hi : i ∈ π f
        · simp [filterList, linList, hi, filterLinear_a, hx, hxs]
        · simp [filterList, linList, hi, filterLinear_a, hxs]
    simp only [filterTerm, linEval, Term.size_app, filterLinear_c, key 0]

/-- Native data: the kept argument positions of every symbol. -/
abbrev dpArgumentFilteringData : Type := FreeSym → List Nat

/-- Arts and Giesl (2000): an argument filtering keeps positions below the arity of each symbol. -/
def dpArgumentFilteringLaws (π : dpArgumentFilteringData) : Prop :=
  ∀ f, ∀ i ∈ π f, i < freeArity f

/-- The filtered size weakly orients the rules and strictly orients the pairs. -/
def dpArgumentFilteringAccepts (π : dpArgumentFilteringData) : Prop :=
  RulesWeak (filterLinear π) freeRecursorTRS ∧ PairsStrict (filterLinear π) freeRecursorTRS

/-- Verdict: escape. -/
def dpArgumentFilteringResult (π : dpArgumentFilteringData) : Prop :=
  dpArgumentFilteringAccepts π ∧ FreeTerminates

theorem dpArgumentFiltering_sound :
    ∀ π, dpArgumentFilteringLaws π → dpArgumentFilteringAccepts π → FreeTerminates :=
  fun π _ h => linear_terminating (filterLinear π) freeRecursorTRS freeRecursorTRS_vars h.1 h.2

/-- Keep the base and counter of `recur`, the recursive argument of `wrap`, and the argument of
`succ`. -/
def dpArgumentFilteringWitness : dpArgumentFilteringData
  | .zero => []
  | .succ => [0]
  | .wrap => [1]
  | .recur => [0, 2]

theorem dpArgumentFilteringWitness_laws : dpArgumentFilteringLaws dpArgumentFilteringWitness := by
  intro f i hi
  cases f <;> simp [dpArgumentFilteringWitness] at hi <;> simp [freeArity] <;> omega

theorem fw_c (f : FreeSym) : (filterLinear dpArgumentFilteringWitness).c f = 1 := rfl
theorem fw_a_succ0 : (filterLinear dpArgumentFilteringWitness).a .succ 0 = 1 := by decide
theorem fw_a_wrap0 : (filterLinear dpArgumentFilteringWitness).a .wrap 0 = 0 := by decide
theorem fw_a_wrap1 : (filterLinear dpArgumentFilteringWitness).a .wrap 1 = 1 := by decide
theorem fw_a_recur0 : (filterLinear dpArgumentFilteringWitness).a .recur 0 = 1 := by decide
theorem fw_a_recur1 : (filterLinear dpArgumentFilteringWitness).a .recur 1 = 0 := by decide
theorem fw_a_recur2 : (filterLinear dpArgumentFilteringWitness).a .recur 2 = 1 := by decide

theorem dpArgumentFilteringWitness_accepts : dpArgumentFilteringAccepts dpArgumentFilteringWitness := by
  refine ⟨?_, ?_⟩
  · intro rule hrule σ
    simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · simp only [zeroRule, Subst.apply_app, Subst.apply_var, Subst.applyList_cons,
        Subst.applyList_nil, linEval, linList, Nat.reduceAdd, fw_c, fw_a_recur0, fw_a_recur1,
        fw_a_recur2]
      omega
    · simp only [succRule, Subst.apply_app, Subst.apply_var, Subst.applyList_cons,
        Subst.applyList_nil, linEval, linList, Nat.reduceAdd, fw_c, fw_a_succ0, fw_a_wrap0,
        fw_a_wrap1, fw_a_recur0, fw_a_recur1, fw_a_recur2]
      omega
  · intro rule hrule σ f largs hl g targs hsub hdef
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := free_pair_shape rfl hrule hl hsub hdef
    simp [markedEval, markedList, linEval, linList, filterLinear, dpArgumentFilteringWitness]

theorem dpArgumentFilteringWitness_result : dpArgumentFilteringResult dpArgumentFilteringWitness :=
  ⟨dpArgumentFilteringWitness_accepts,
    dpArgumentFiltering_sound _ dpArgumentFilteringWitness_laws dpArgumentFilteringWitness_accepts⟩

/-- The filtering erases the payload of `recur` and `wrap`: the filtered successor rule is
`recur(b, succ(n)) → wrap(recur(b, n))`. -/
theorem dpArgumentFilteringWitness_feature :
    filterTerm dpArgumentFilteringWitness succRule.lhs =
        .app .recur [.var 0, .app .succ [.var 2]] ∧
      filterTerm dpArgumentFilteringWitness succRule.rhs =
        .app .wrap [.app .recur [.var 0, .var 2]] := by
  constructor <;> simp [filterTerm, filterList, succRule, dpArgumentFilteringWitness]

/-- Keep only the counter of `recur`. -/
def counterOnlyFilter : dpArgumentFilteringData
  | .zero => []
  | .succ => [0]
  | .wrap => [1]
  | .recur => [2]

/-- Keep only the base of `recur`. -/
def baseOnlyFilter : dpArgumentFilteringData
  | .zero => []
  | .succ => [0]
  | .wrap => [1]
  | .recur => [0]

/-- Erasing the base of `recur` breaks the weak zero rule; erasing the counter disconnects the pair
rank from the recursion. -/
theorem dpArgumentFiltering_mutation :
    (dpArgumentFilteringLaws counterOnlyFilter ∧ ¬ dpArgumentFilteringAccepts counterOnlyFilter) ∧
      (dpArgumentFilteringLaws baseOnlyFilter ∧ ¬ dpArgumentFilteringAccepts baseOnlyFilter) := by
  refine ⟨⟨?_, fun h => ?_⟩, ⟨?_, fun h => ?_⟩⟩
  · intro f i hi
    cases f <;> simp [counterOnlyFilter] at hi <;> simp [freeArity] <;> omega
  · have := h.1 zeroRule (by simp [freeRecursorTRS])
      (fun _ => Term.app FreeSym.succ [Term.app FreeSym.succ [Term.app FreeSym.zero []]])
    simp [zeroRule, linEval, linList, filterLinear, counterOnlyFilter] at this
  · intro f i hi
    cases f <;> simp [baseOnlyFilter] at hi <;> simp [freeArity] <;> omega
  · have := h.2 succRule (by simp [freeRecursorTRS]) Subst.id FreeSym.recur
      [.var 0, .var 1, .app .succ [.var 2]] rfl FreeSym.recur [.var 0, .var 1, .var 2]
      succRule_rhs_call ((freeRecursorTRS_defined_iff _).2 rfl)
    simp [markedEval, markedList, linEval, linList, filterLinear, baseOnlyFilter] at this

/-! ## Row: dpNeutralProcessors -/

/-- Native data: a processor on dependency-pair problems. -/
abbrev dpNeutralProcessorsData : Type := FProblem → FProblem

/-- Giesl, Thiemann and Schneider-Kamp (The dependency pair framework, LPAR 2004): a neutral
processor returns a problem with the same edges. -/
def dpNeutralProcessorsLaws (M : dpNeutralProcessorsData) : Prop :=
  ∀ P c d, M P c d ↔ P c d

/-- The output problem of the free recursor is finite. -/
def dpNeutralProcessorsAccepts (M : dpNeutralProcessorsData) : Prop :=
  FiniteDP freeRecursorTRS (M (dpPairs freeRecursorTRS))

/-- Verdict: escape. -/
def dpNeutralProcessorsResult (M : dpNeutralProcessorsData) : Prop :=
  dpNeutralProcessorsAccepts M ∧ FreeTerminates

theorem dpNeutralProcessors_sound :
    ∀ M, dpNeutralProcessorsLaws M → dpNeutralProcessorsAccepts M → FreeTerminates := by
  intro M hM h
  have hfin : FiniteDP freeRecursorTRS (dpPairs freeRecursorTRS) :=
    (neutral_processor_iff (fun c d => hM _ c d)).1 h
  exact terminating_of_finiteDP freeRecursorTRS freeRecursorTRS_vars hfin

def dpNeutralProcessorsWitness : dpNeutralProcessorsData := fun P => P

theorem dpNeutralProcessorsWitness_laws : dpNeutralProcessorsLaws dpNeutralProcessorsWitness :=
  fun _ _ _ => Iff.rfl

theorem dpNeutralProcessorsWitness_result : dpNeutralProcessorsResult dpNeutralProcessorsWitness :=
  ⟨free_finiteDP, dpNeutralProcessors_sound _ dpNeutralProcessorsWitness_laws free_finiteDP⟩

/-- Neutral processors compose, and a neutral processor leaves an unsolved problem unsolved. -/
theorem dpNeutralProcessorsWitness_feature :
    (∀ M N : dpNeutralProcessorsData, dpNeutralProcessorsLaws M → dpNeutralProcessorsLaws N →
      dpNeutralProcessorsLaws (fun P => M (N P))) ∧
      ¬ FiniteDP emptyTRS ((fun P : Call Unit Nat → Call Unit Nat → Prop => P) selfLoop) := by
  refine ⟨fun M N hM hN P c d => (hM (N P) c d).trans (hN P c d), ?_⟩
  exact deleting_live_pair_unsound.2

/-- The processor that deletes every edge. -/
def deleteAllProcessor : dpNeutralProcessorsData := fun _ _ _ => False

/-- Deleting every edge is not neutral although its output is finite; on the self-loop problem the
same deletion certifies a problem that is not finite. -/
theorem dpNeutralProcessors_mutation :
    ¬ dpNeutralProcessorsLaws deleteAllProcessor ∧ dpNeutralProcessorsAccepts deleteAllProcessor ∧
      (FiniteDP emptyTRS (fun _ _ => False) ∧ ¬ FiniteDP emptyTRS selfLoop) := by
  refine ⟨fun h => (h _ dpSource dpTarget).2 free_dpPair, finiteDP_empty _ fun _ _ h => h,
    deleting_live_pair_unsound⟩

/-! ## Row: dpReductionTriples -/

/-- The reduction triple of linear data: argument rewriting keeps the call symbol, weak pair edges
may change it, and strict pair edges decrease. -/
def linearTriple (L : LinearData) (R : TRS FreeSym Nat) (hR : RulesWeak L R) :
    CallReductionTriple R where
  rulesWeak c d := c.1 = d.1 ∧ markedEval L d ≤ markedEval L c
  pairWeak c d := markedEval L d ≤ markedEval L c
  pairStrict c d := markedEval L d < markedEval L c
  rules_refl _ := ⟨rfl, le_rfl⟩
  rules_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, le_trans h₂.2 h₁.2⟩
  rules_strict h₁ h₂ := lt_of_lt_of_le h₂ h₁.2
  rules_weak h₁ h₂ := le_trans h₂ h₁.2
  weak_strict h₁ h₂ := lt_of_lt_of_le h₂ h₁
  strict_wf := InvImage.wf (markedEval L) Nat.lt_wfRel.wf
  arg_weak f _ _ _ h := ⟨rfl, markedEval_argStep_le hR f h⟩

theorem triple_finiteDP (L : LinearData) (hR : RulesWeak L freeRecursorTRS)
    (hP : PairsStrict L freeRecursorTRS) : FiniteDP freeRecursorTRS (dpPairs freeRecursorTRS) :=
  reductionTriple_processor_sound (linearTriple L freeRecursorTRS hR) (dpPairs freeRecursorTRS)
    (fun {_ _} _ _ h => Or.inr (pairsStrict_dpPairs hP h))
    (finiteDP_empty _ fun _ _ h => h.2 (pairsStrict_dpPairs hP h.1))

/-- Native data: linear data read as three relations on calls. -/
abbrev dpReductionTriplesData : Type := LinearData

/-- Reduction triples (Kop and van Raamsdonk, Dynamic dependency pairs for algebraic functional
systems, LMCS 2012): the rules weakly decrease under the monotone component. -/
def dpReductionTriplesLaws (L : dpReductionTriplesData) : Prop := RulesWeak L freeRecursorTRS

/-- Every pair edge is strict. -/
def dpReductionTriplesAccepts (L : dpReductionTriplesData) : Prop := PairsStrict L freeRecursorTRS

/-- Verdict: escape. -/
def dpReductionTriplesResult (L : dpReductionTriplesData) : Prop :=
  dpReductionTriplesAccepts L ∧ FreeTerminates

theorem dpReductionTriples_sound :
    ∀ L, dpReductionTriplesLaws L → dpReductionTriplesAccepts L → FreeTerminates :=
  fun L hR hP => terminating_of_finiteDP freeRecursorTRS freeRecursorTRS_vars (triple_finiteDP L hR hP)

def dpReductionTriplesWitness : dpReductionTriplesData := counterLinear

theorem dpReductionTriplesWitness_laws : dpReductionTriplesLaws dpReductionTriplesWitness :=
  counterLinear_rulesWeak

theorem dpReductionTriplesWitness_result : dpReductionTriplesResult dpReductionTriplesWitness :=
  ⟨counterLinear_pairsStrict,
    dpReductionTriples_sound _ counterLinear_rulesWeak counterLinear_pairsStrict⟩

/-- The two weak relations of the triple differ: a weak pair edge may change the call symbol, an
argument-rewriting edge may not. Swapping them breaks the law `rules_weak`. -/
theorem dpReductionTriplesWitness_feature :
    (linearTriple dpReductionTriplesWitness freeRecursorTRS dpReductionTriplesWitness_laws).pairWeak
        (.zero, []) (.recur, []) ∧
      ¬ (linearTriple dpReductionTriplesWitness freeRecursorTRS
          dpReductionTriplesWitness_laws).rulesWeak (.zero, []) (.recur, []) ∧
      ¬ (∀ a b c : FCall, markedEval counterLinear b ≤ markedEval counterLinear a →
          (b.1 = c.1 ∧ markedEval counterLinear c ≤ markedEval counterLinear b) →
            (a.1 = c.1 ∧ markedEval counterLinear c ≤ markedEval counterLinear a)) := by
  refine ⟨le_rfl, fun h => FreeSym.noConfusion h.1, fun h => ?_⟩
  have := h (.zero, []) (.recur, []) (.recur, []) le_rfl ⟨rfl, le_rfl⟩
  exact FreeSym.noConfusion this.1

theorem dpReductionTriples_mutation :
    dpReductionTriplesLaws blindLinear ∧ ¬ dpReductionTriplesAccepts blindLinear :=
  ⟨blindLinear_rulesWeak, blindLinear_not_pairsStrict⟩

/-! ## Row: dpProcessorClassification -/

/-- Processor kinds: the identity processor and the reduction-pair processor of linear data. -/
inductive ProcKind where
  | neutral
  | pair (L : LinearData)

/-- Output problem of a processor. -/
def procOut : ProcKind → FProblem → FProblem
  | .neutral, P => P
  | .pair L, P => fun c d => P c d ∧ ¬ markedEval L d < markedEval L c

/-- Applicability condition of a processor on a problem. -/
def procCond : ProcKind → FProblem → Prop
  | .neutral, _ => True
  | .pair L, P => RulesWeak L freeRecursorTRS ∧ ∀ c d, P c d → markedEval L d ≤ markedEval L c

/-- Every processor kind is sound on every problem that meets its condition. -/
theorem proc_sound (k : ProcKind) (P : FProblem) (hc : procCond k P)
    (hfin : FiniteDP freeRecursorTRS (procOut k P)) : FiniteDP freeRecursorTRS P := by
  cases k with
  | neutral => exact hfin
  | pair L =>
    obtain ⟨hR, hw⟩ := hc
    exact reductionTriple_processor_sound (linearTriple L freeRecursorTRS hR) P
      (fun {c d} _ _ h => Or.inl (hw c d h)) hfin

/-- The output of a processor sequence. -/
def runProcs : List ProcKind → FProblem → FProblem
  | [], P => P
  | k :: ks, P => runProcs ks (procOut k P)

/-- The conditions of a processor sequence on the successive intermediate problems. -/
def chainCond : List ProcKind → FProblem → Prop
  | [], _ => True
  | k :: ks, P => procCond k P ∧ chainCond ks (procOut k P)

/-- Composition: a sequence of sound processors is sound. -/
theorem runProcs_sound : ∀ (ks : List ProcKind) (P : FProblem), chainCond ks P →
    FiniteDP freeRecursorTRS (runProcs ks P) → FiniteDP freeRecursorTRS P
  | [], _, _, h => h
  | k :: ks, P, ⟨hc, hcs⟩, h => proc_sound k P hc (runProcs_sound ks (procOut k P) hcs h)

/-- Native data: a sequence of processors. -/
abbrev dpProcessorClassificationData : Type := List ProcKind

/-- Giesl, Thiemann and Schneider-Kamp (LPAR 2004): a proof in the dependency pair framework is a
sequence of processors whose conditions hold on the intermediate problems. -/
def dpProcessorClassificationLaws (ks : dpProcessorClassificationData) : Prop :=
  chainCond ks (dpPairs freeRecursorTRS)

/-- The sequence leaves no edge. -/
def dpProcessorClassificationAccepts (ks : dpProcessorClassificationData) : Prop :=
  ∀ c d, ¬ runProcs ks (dpPairs freeRecursorTRS) c d

/-- Verdict: escape. -/
def dpProcessorClassificationResult (ks : dpProcessorClassificationData) : Prop :=
  dpProcessorClassificationAccepts ks ∧ FreeTerminates

theorem dpProcessorClassification_sound :
    ∀ ks, dpProcessorClassificationLaws ks → dpProcessorClassificationAccepts ks →
      FreeTerminates :=
  fun ks hl ha => terminating_of_finiteDP freeRecursorTRS freeRecursorTRS_vars
    (runProcs_sound ks _ hl (finiteDP_empty _ ha))

def dpProcessorClassificationWitness : dpProcessorClassificationData :=
  [.neutral, .pair counterLinear]

theorem dpProcessorClassificationWitness_laws :
    dpProcessorClassificationLaws dpProcessorClassificationWitness :=
  ⟨trivial, ⟨counterLinear_rulesWeak, fun _ _ h => (pairsStrict_dpPairs counterLinear_pairsStrict h).le⟩,
    trivial⟩

theorem dpProcessorClassificationWitness_accepts :
    dpProcessorClassificationAccepts dpProcessorClassificationWitness :=
  fun _ _ h => h.2 (pairsStrict_dpPairs counterLinear_pairsStrict h.1)

theorem dpProcessorClassificationWitness_result :
    dpProcessorClassificationResult dpProcessorClassificationWitness :=
  ⟨dpProcessorClassificationWitness_accepts,
    dpProcessorClassification_sound _ dpProcessorClassificationWitness_laws
      dpProcessorClassificationWitness_accepts⟩

/-- Classification: both kinds are sound, sequences compose, and the neutral processor alone leaves
the free recursor unsolved. -/
theorem dpProcessorClassificationWitness_feature :
    (∀ k P, procCond k P → FiniteDP freeRecursorTRS (procOut k P) → FiniteDP freeRecursorTRS P) ∧
      ¬ dpProcessorClassificationAccepts [.neutral] :=
  ⟨proc_sound, fun h => h dpSource dpTarget free_dpPair⟩

/-- A payload-retaining wrapper in the second processor breaks the condition on the intermediate
problem; the blind counter leaves every edge. -/
theorem dpProcessorClassification_mutation :
    ¬ dpProcessorClassificationLaws [.neutral, .pair retainLinear] ∧
      (dpProcessorClassificationLaws [.pair blindLinear] ∧
        ¬ dpProcessorClassificationAccepts [.pair blindLinear]) := by
  refine ⟨fun h => retainLinear_not_rulesWeak h.2.1.1, ⟨⟨⟨blindLinear_rulesWeak, ?_⟩, trivial⟩, ?_⟩⟩
  · intro c d _
    simp [blindLinear_markedEval]
  · intro h
    refine h dpSource dpTarget ⟨free_dpPair, ?_⟩
    simp [blindLinear_markedEval]

/-! ## Row: sizeChangeTerminationEscape -/

/-- The looping rule `recur(b, s, n) → recur(b, s, n)`: its call does not descend. -/
def selfLoopRule : Rule FreeSym Nat where
  lhs := .app .recur [.var 0, .var 1, .var 2]
  rhs := .app .recur [.var 0, .var 1, .var 2]
  lhs_isApp := rfl

/-- The one-rule system of the looping rule. -/
def selfLoopRecTRS : TRS FreeSym Nat := [selfLoopRule]

/-- The argument list of both sides of the looping rule. -/
def selfLoopArgs : List FTerm := [.var 0, .var 1, .var 2]

theorem selfLoopRecTRS_vars :
    ∀ rule ∈ selfLoopRecTRS, Term.vars rule.rhs ⊆ Term.vars rule.lhs := by
  intro rule hrule
  obtain rfl := List.mem_singleton.1 hrule
  exact Finset.Subset.refl _

theorem selfLoopRecTRS_defined : IsDefined selfLoopRecTRS .recur :=
  ⟨selfLoopRule, List.mem_singleton.2 rfl, selfLoopArgs, rfl⟩

theorem selfLoop_depPair :
    SizeChangeTermination.IsDepPair selfLoopRecTRS .recur selfLoopArgs .recur selfLoopArgs :=
  ⟨selfLoopRule, List.mem_singleton.2 rfl, rfl, .refl _, selfLoopRecTRS_defined⟩

theorem not_properSubterm_of_var {t : FTerm} {x : Nat} : ¬ ProperSubterm t (.var x) := by
  intro h
  cases h

theorem mem_selfLoopGraph {i j : Nat} {b : Bool} :
    (i, j, b) ∈ SizeChangeTermination.pairGraph selfLoopArgs selfLoopArgs ↔
      i = j ∧ i < 3 ∧ b = false := by
  rw [SizeChangeTermination.mem_pairGraph]
  constructor
  · rintro ⟨l, t, hl, ht, hlab⟩
    have hi : i < 3 := (List.getElem?_eq_some_iff.1 hl).1
    have hj : j < 3 := (List.getElem?_eq_some_iff.1 ht).1
    have hl' : l = .var i := by
      interval_cases i <;> simp [selfLoopArgs] at hl <;> exact hl.symm
    have ht' : t = .var j := by
      interval_cases j <;> simp [selfLoopArgs] at ht <;> exact ht.symm
    subst hl' ht'
    cases b with
    | true => exact (not_properSubterm_of_var hlab).elim
    | false =>
      have hji : (Term.var j : FTerm) = Term.var i := hlab
      exact ⟨(Term.var.inj hji).symm, hi, rfl⟩
  · rintro ⟨rfl, hi, rfl⟩
    refine ⟨.var i, .var i, ?_, ?_, rfl⟩ <;>
      interval_cases i <;> rfl

theorem selfLoopGraph_idem :
    SizeChangeTermination.SCGraph.comp
        (SizeChangeTermination.pairGraph selfLoopArgs selfLoopArgs)
        (SizeChangeTermination.pairGraph selfLoopArgs selfLoopArgs) =
      SizeChangeTermination.pairGraph selfLoopArgs selfLoopArgs := by
  ext ⟨i, k, b⟩
  rw [SizeChangeTermination.SCGraph.mem_comp, mem_selfLoopGraph]
  constructor
  · rintro ⟨j, b₁, b₂, h₁, h₂, rfl⟩
    obtain ⟨rfl, hi, rfl⟩ := mem_selfLoopGraph.1 h₁
    obtain ⟨rfl, -, rfl⟩ := mem_selfLoopGraph.1 h₂
    exact ⟨rfl, hi, rfl⟩
  · rintro ⟨rfl, hi, rfl⟩
    exact ⟨i, false, false, mem_selfLoopGraph.2 ⟨rfl, hi, rfl⟩,
      mem_selfLoopGraph.2 ⟨rfl, hi, rfl⟩, rfl⟩

theorem selfLoopRecTRS_not_sct : ¬ SizeChangeTermination.SCTCriterion selfLoopRecTRS := by
  intro h
  obtain ⟨i, hi⟩ := h .recur _ (.pair selfLoop_depPair) selfLoopGraph_idem
  cases (mem_selfLoopGraph.1 hi).2.2

theorem selfLoopRecTRS_not_sn :
    ¬ SN selfLoopRecTRS (.app .recur [.app .zero [], .app .zero [], .app .zero []]) := by
  intro hsn
  have hstep : Step selfLoopRecTRS (.app .recur [.app .zero [], .app .zero [], .app .zero []])
      (.app .recur [.app .zero [], .app .zero [], .app .zero []]) :=
    Step.root ⟨selfLoopRule, List.mem_singleton.2 rfl, fun _ => .app .zero [], rfl, rfl⟩
  have key : ∀ t, SN selfLoopRecTRS t → ¬ Step selfLoopRecTRS t t := by
    intro t ht
    induction ht with
    | intro x _ ih => exact fun hxx => ih x hxx hxx
  exact key _ hsn hstep

/-- Native data: the rewrite system to which the size-change principle is applied; its size-change
graphs are computed from its dependency pairs (`SizeChangeTermination.pairGraph`). -/
abbrev sizeChangeTerminationEscapeData : Type := TRS FreeSym Nat

/-- Lee, Jones and Ben-Amram (The size-change principle for program termination, POPL 2001), for
term rewriting through dependency pairs (Thiemann and Giesl, AAECC 16, 2005): the rules satisfy the
variable condition. -/
def sizeChangeTerminationEscapeLaws (R : sizeChangeTerminationEscapeData) : Prop :=
  ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs

/-- Every idempotent graph of the composition closure from a symbol to itself has a strict
self-arc. -/
def sizeChangeTerminationEscapeAccepts (R : sizeChangeTerminationEscapeData) : Prop :=
  SizeChangeTermination.SCTCriterion R

/-- Verdict: escape. -/
def sizeChangeTerminationEscapeResult (R : sizeChangeTerminationEscapeData) : Prop :=
  sizeChangeTerminationEscapeAccepts R ∧ ∀ t : FTerm, SN R t

theorem sizeChangeTerminationEscape_sound :
    ∀ R, sizeChangeTerminationEscapeLaws R → sizeChangeTerminationEscapeAccepts R →
      ∀ t : FTerm, SN R t :=
  fun R hv h => SizeChangeTermination.terminating_of_sct R hv h

def sizeChangeTerminationEscapeWitness : sizeChangeTerminationEscapeData := freeRecursorTRS

theorem sizeChangeTerminationEscapeWitness_laws :
    sizeChangeTerminationEscapeLaws sizeChangeTerminationEscapeWitness :=
  freeRecursorTRS_vars

theorem sizeChangeTerminationEscapeWitness_result :
    sizeChangeTerminationEscapeResult sizeChangeTerminationEscapeWitness :=
  ⟨SizeChangeTermination.freeRecursorTRS_sctCriterion,
    SizeChangeTermination.freeRecursorTRS_terminating_bySCT⟩

/-- The graphs are computed from the calls: the strict arc of the free recursor sits on the counter,
and a strict arc on a position that does not descend is unsound (control C17). -/
theorem sizeChangeTerminationEscapeWitness_feature :
    (2, 2, true) ∈ SizeChangeTermination.pairGraph
        ([.var 0, .var 1, .app .succ [.var 2]] : List FTerm) [.var 0, .var 1, .var 2] ∧
      (MinChainStep SizeChangeTermination.loopTRS SizeChangeTermination.loopCall
          SizeChangeTermination.loopCall ∧
        ¬ SizeChangeTermination.GraphSound SizeChangeTermination.loopTRS {(0, 0, true)}
          SizeChangeTermination.loopCall.2 SizeChangeTermination.loopCall.2 ∧
        (0, 0, true) ∉ SizeChangeTermination.pairGraph SizeChangeTermination.loopArgs
          SizeChangeTermination.loopArgs) :=
  ⟨SizeChangeTermination.mem_pairGraph.2 ⟨.app .succ [.var 2], .var 2, rfl, rfl,
      ProperSubterm.arg FreeSym.succ [Term.var 2] List.mem_cons_self (IsSubterm.refl _)⟩,
    SizeChangeTermination.strictArc_control⟩

/-- Replacing the rules by a recursive call that does not descend keeps the variable condition,
fails the criterion, and does not terminate. -/
theorem sizeChangeTerminationEscape_mutation :
    sizeChangeTerminationEscapeLaws selfLoopRecTRS ∧
      ¬ sizeChangeTerminationEscapeAccepts selfLoopRecTRS ∧
      ¬ SN selfLoopRecTRS (.app .recur [.app .zero [], .app .zero [], .app .zero []]) :=
  ⟨selfLoopRecTRS_vars, selfLoopRecTRS_not_sct, selfLoopRecTRS_not_sn⟩

end OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs
