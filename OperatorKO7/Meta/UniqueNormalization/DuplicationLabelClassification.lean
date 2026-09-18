import OperatorKO7.Meta.UniqueNormalization.DecreasingDiagramCarrier
import OperatorKO7.Meta.UniqueNormalization.HubLinearization
import OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation

/-!
# Rule labels at a duplicating rule: the local repair and the nested obstruction

Campaign: `COMMAND-CENTER/design/RESEARCH-ROADMAP.md`, package DC-4 of the Distinction
certificate closeout.

For every copy count `r`, `R_r` consists of `f(x) → g(x, …, x)` (`r` copies) and `a → b`, with
symbol codes `f = 0`, `g = 1`, `a = 2`, `b = 3`. A constant-per-rule labeling assigns each rewrite
step the label of the rule it fires, in an arbitrary label type with an arbitrary irreflexive
strict relation `lt`; context steps keep the label (`RuleLabelStep`). Erasing the label gives
exactly the rewrite relation (`ruleLabelStep_iff_step`). Write `α` for the label of the duplicating
rule and `β` for the label of `a → b`; the valley shape is the unchanged `DecreasingValley`.

* **Atom peak.** For `r ≥ 2`, the peak `g(a, …, a) ← f(a) → f(b)` has a decreasing valley exactly
when `β` is below `α` (`atom_peak_decreasing_iff`); the rule priority `β = 0 < 1 = α` over `Nat`
repairs it for every `r` (`atom_peak_rule_priority_repair`); for `r = 0` and `r = 1` the valley
exists for every labeling (`atom_peak_small_arity`).
* **Nested peak.** For `r ≥ 2`, the peak `g(f(v), …, f(v)) ← f(f(v)) → f(g(v, …, v))` has both
labels `α`; every later step fires the duplicating rule, because `a` is absent, so irreflexivity
removes every lower-label segment and each arm takes at most one step. The two successor sets are
disjoint (`nested_peak_not_decreasing`). Hence **no constant-per-rule labeling makes every local
peak of `R_r` decreasing** (`no_constant_rule_labeling`), although the peak joins in `r` steps
against one (`nested_peak_ordinary_join`).
* **KLOP-FAIL-005 landed.** The refutation of the universal minimum-level labeling (source
`.agent-tmp/KlopMinimalLevelCheck.lean`, SHA-256
`EDEDAD86E2F3A06E3EE719725C644E08E56177D7C585FDA1D789900AFB7AF0E4`) is reproduced with its
declarations and statements unchanged in namespace `MinimalLevelDuplication`
(`minimum_level_refutation_preserved`); its system is `R_2` (`minimalLevel_rules_eq_dupRules`).

Proves: the label erasure theorem, the two peak classifications, the labeling obstruction for
constant-per-rule labels on `R_r`, the local repair, and the landed minimum-level refutation.
Does not prove: anything about term-dependent labels, parallel labels, or the decreasing-diagrams
method in general; joinability or confluence of `R_r` beyond the displayed join.
Relation: `RuleLabelStep (dupRules r) lab`, whose label erasure is `Step (dupRules r)`.
Closure: one labeled step, its reflexive-transitive closures inside the valley fields.
Strategy: full rewriting.
Trust: kernel checked; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`, `unsafe` or
`opaque`. Axiom footprints are printed by the paired reach file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.DuplicationLabels

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v w

/-! ## Labels from the fired rule -/

section RuleLabels

variable {sigma : Type u} {nu : Type v} {Label : Type w}

/-- **The rule-labeled one-step relation.** A root step fires a rule of `R` and carries that rule's
label; a context step keeps the label of the step inside its argument. -/
inductive RuleLabelStep (R : TRS sigma nu) (lab : Rule sigma nu → Label) :
    Label → Term sigma nu → Term sigma nu → Prop
  | root {rule : Rule sigma nu} {l : Label} {s t : Term sigma nu} (hr : rule ∈ R)
      (σ : Subst sigma nu) (hl : l = lab rule) (hs : s = Subst.apply σ rule.lhs)
      (ht : t = Subst.apply σ rule.rhs) : RuleLabelStep R lab l s t
  | arg (f : sigma) (pre post : List (Term sigma nu)) {l : Label} {a b : Term sigma nu} :
      RuleLabelStep R lab l a b →
      RuleLabelStep R lab l (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

/-- **Label erasure is exact.** Some label labels a step from `s` to `t` exactly when `s` rewrites
to `t`. -/
theorem ruleLabelStep_iff_step {R : TRS sigma nu} {lab : Rule sigma nu → Label}
    {s t : Term sigma nu} : (∃ l, RuleLabelStep R lab l s t) ↔ Step R s t := by
  constructor
  · rintro ⟨l, h⟩
    induction h with
    | root hr σ _ hs ht => exact Step.root ⟨_, hr, σ, hs, ht⟩
    | arg f pre post _ ih => exact Step.arg f pre post ih
  · intro h
    induction h with
    | root hr =>
        obtain ⟨rule, hmem, σ, hs, ht⟩ := hr
        exact ⟨lab rule, RuleLabelStep.root hmem σ rfl hs ht⟩
    | arg f pre post _ ih =>
        obtain ⟨l, hl⟩ := ih
        exact ⟨l, RuleLabelStep.arg f pre post hl⟩

/-- Every label is the label of a rule of `R`. -/
theorem ruleLabelStep_label_of_rule {R : TRS sigma nu} {lab : Rule sigma nu → Label}
    {l : Label} {s t : Term sigma nu} (h : RuleLabelStep R lab l s t) :
    ∃ rule ∈ R, lab rule = l := by
  induction h with
  | root hr _ hl _ _ => exact ⟨_, hr, hl.symm⟩
  | arg _ _ _ _ ih => exact ih

/-- Inversion at an application. -/
theorem RuleLabelStep.app_inv {R : TRS sigma nu} {lab : Rule sigma nu → Label} {l : Label}
    {f : sigma} {xs : List (Term sigma nu)} {u : Term sigma nu}
    (h : RuleLabelStep R lab l (.app f xs) u) :
    (∃ rule ∈ R, ∃ σ : Subst sigma nu, l = lab rule ∧ Term.app f xs = Subst.apply σ rule.lhs ∧
        u = Subst.apply σ rule.rhs) ∨
      ∃ (pre post : List (Term sigma nu)) (a b : Term sigma nu),
        xs = pre ++ a :: post ∧ u = .app f (pre ++ b :: post) ∧ RuleLabelStep R lab l a b := by
  cases h with
  | root hr σ hl hs ht => exact Or.inl ⟨_, hr, σ, hl, hs, ht⟩
  | arg g pre post hab => exact Or.inr ⟨pre, post, _, _, rfl, rfl, hab⟩

/-- A variable takes no labeled step. -/
theorem RuleLabelStep.not_var {R : TRS sigma nu} {lab : Rule sigma nu → Label} {l : Label}
    {x : nu} {u : Term sigma nu} : ¬ RuleLabelStep R lab l (.var x) u :=
  fun h => Step.not_var (ruleLabelStep_iff_step.1 ⟨l, h⟩)

end RuleLabels

/-! ## The systems `R_r` -/

/-- The term `a`. -/
def aT : Term Nat Nat := .app 2 []

/-- The term `b`. -/
def bT : Term Nat Nat := .app 3 []

/-- `f(x) → g(x, …, x)` with `r` copies. -/
def dupRule (r : Nat) : Rule Nat Nat := ⟨.app 0 [.var 0], .app 1 (List.replicate r (.var 0)), rfl⟩

/-- `a → b`. -/
def atomRule : Rule Nat Nat := ⟨.app 2 [], .app 3 [], rfl⟩

/-- The system `R_r`. -/
def dupRules (r : Nat) : TRS Nat Nat := [dupRule r, atomRule]

section Family

variable {Label : Type w} {r : Nat} {lab : Rule Nat Nat → Label}

/-- The duplicating root step `f(t) → g(t, …, t)`. -/
theorem dup_root_step (r : Nat) (lab : Rule Nat Nat → Label) (t : Term Nat Nat) :
    RuleLabelStep (dupRules r) lab (lab (dupRule r)) (.app 0 [t]) (.app 1 (List.replicate r t)) :=
  RuleLabelStep.root (List.Mem.head _) (fun _ => t) rfl rfl
    (by simp [dupRule, Subst.applyList_eq_map, List.map_replicate])

/-- The atom root step `a → b`. -/
theorem atom_root_step (r : Nat) (lab : Rule Nat Nat → Label) :
    RuleLabelStep (dupRules r) lab (lab atomRule) aT bT :=
  RuleLabelStep.root (List.Mem.tail _ (List.Mem.head _)) Subst.id rfl rfl rfl

/-- **Every labeled step of `R_r` from an application.** A root step fires the duplicating rule at
an `f`-headed term or the atom rule at `a`; otherwise the step acts inside one argument. -/
theorem dup_step_cases {l : Label} {f : Nat} {xs : List (Term Nat Nat)} {u : Term Nat Nat}
    (h : RuleLabelStep (dupRules r) lab l (.app f xs) u) :
    (∃ t, f = 0 ∧ xs = [t] ∧ u = .app 1 (List.replicate r t) ∧ l = lab (dupRule r)) ∨
      (f = 2 ∧ xs = [] ∧ u = bT ∧ l = lab atomRule) ∨
      ∃ (pre post : List (Term Nat Nat)) (a b : Term Nat Nat),
        xs = pre ++ a :: post ∧ u = .app f (pre ++ b :: post) ∧ RuleLabelStep (dupRules r) lab l a b := by
  rcases RuleLabelStep.app_inv h with ⟨rule, hmem, σ, hl, hs, ht⟩ | harg
  · simp only [dupRules, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · simp only [dupRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
        Subst.apply_var, Term.app.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine Or.inl ⟨σ 0, rfl, rfl, ?_, hl⟩
      rw [ht]
      simp [dupRule, Subst.applyList_eq_map, List.map_replicate]
    · simp only [atomRule, Subst.apply_app, Subst.applyList_nil, Term.app.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact Or.inr (Or.inl ⟨rfl, rfl, ht, hl⟩)
  · exact Or.inr (Or.inr harg)

/-! ### Symbol absence -/

/-- The symbol `c` heads no subterm of `t`. -/
def NoSym (c : Nat) (t : Term Nat Nat) : Prop :=
  ∀ q, Subterm q t → ∀ xs : List (Term Nat Nat), q ≠ .app c xs

/-- Symbol absence at an application. -/
theorem noSym_app_iff {c g : Nat} {xs : List (Term Nat Nat)} :
    NoSym c (.app g xs) ↔ g ≠ c ∧ ∀ x ∈ xs, NoSym c x := by
  constructor
  · intro h
    refine ⟨fun hg => h _ (Subterm.refl _) xs (by rw [hg]), fun x hx q hq ys => ?_⟩
    exact h q (Subterm.arg hx hq) ys
  · rintro ⟨hg, hxs⟩ q hq ys hqe
    cases hq with
    | refl =>
        simp only [Term.app.injEq] at hqe
        exact hg hqe.1
    | arg ha hsa => exact hxs _ ha q hsa ys hqe

/-- Variables contain no symbol. -/
theorem noSym_var (c x : Nat) : NoSym c (.var x) := by
  intro q hq ys hqe
  rw [hq.eq_of_var] at hqe
  simp at hqe

/-- Symbol absence survives replacing one argument. -/
theorem noSym_replace {c g : Nat} {pre post : List (Term Nat Nat)} {a b : Term Nat Nat}
    (h : NoSym c (.app g (pre ++ a :: post))) (hb : NoSym c b) :
    NoSym c (.app g (pre ++ b :: post)) := by
  rw [noSym_app_iff] at h ⊢
  refine ⟨h.1, fun x hx => ?_⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact h.2 x (List.mem_append_left _ hx)
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact hb
    · exact h.2 x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))

/-- The argument inside a replaced position is free of the symbol. -/
theorem noSym_arg {c g : Nat} {pre post : List (Term Nat Nat)} {a : Term Nat Nat}
    (h : NoSym c (.app g (pre ++ a :: post))) : NoSym c a :=
  (noSym_app_iff.1 h).2 a (List.mem_append_right _ (List.mem_cons_self ..))

/-- **Without `f`, every step fires the atom rule** and keeps `f` absent. -/
theorem step_noF : ∀ {l : Label} {t u : Term Nat Nat}, RuleLabelStep (dupRules r) lab l t u →
    NoSym 0 t → l = lab atomRule ∧ NoSym 0 u := by
  intro l t u h
  induction h with
  | root hr σ hl hs ht =>
      intro hf
      simp only [dupRules, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exfalso
        rw [hs] at hf
        exact hf _ (Subterm.refl _) _ rfl
      · refine ⟨hl, ?_⟩
        rw [ht]
        exact noSym_app_iff.2 ⟨by decide, by simp⟩
  | arg g pre post _ ih =>
      intro hf
      obtain ⟨hl, hb⟩ := ih (noSym_arg hf)
      exact ⟨hl, noSym_replace hf hb⟩

/-- **Without `a`, every step fires the duplicating rule** and keeps `a` absent. -/
theorem step_noA : ∀ {l : Label} {t u : Term Nat Nat}, RuleLabelStep (dupRules r) lab l t u →
    NoSym 2 t → l = lab (dupRule r) ∧ NoSym 2 u := by
  intro l t u h
  induction h with
  | root hr σ hl hs ht =>
      intro ha
      simp only [dupRules, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨hl, ?_⟩
        have hσ : NoSym 2 (σ 0) := by
          rw [hs] at ha
          exact (noSym_app_iff.1 ha).2 (σ 0) (List.Mem.head _)
        rw [ht]
        simp only [dupRule, Subst.apply_app, Subst.applyList_eq_map, List.map_replicate,
          Subst.apply_var]
        refine noSym_app_iff.2 ⟨by decide, fun x hx => ?_⟩
        rw [List.eq_of_mem_replicate hx]
        exact hσ
      · exfalso
        rw [hs] at ha
        exact ha _ (Subterm.refl _) _ rfl
  | arg g pre post _ ih =>
      intro ha
      obtain ⟨hl, hb⟩ := ih (noSym_arg ha)
      exact ⟨hl, noSym_replace ha hb⟩

/-- Any closure of steps keeps `a` absent. -/
theorem star_noSym_two {rel : Term Nat Nat → Term Nat Nat → Prop}
    (hrel : ∀ x y, rel x y → ∃ l, RuleLabelStep (dupRules r) lab l x y)
    {x y : Term Nat Nat} (h : Star rel x y) (hx : NoSym 2 x) : NoSym 2 y := by
  induction h with
  | refl => exact hx
  | tail _ hlast ih =>
      obtain ⟨l, hl⟩ := hrel _ _ hlast
      exact (step_noA hl ih).2

/-- A step of a `g`-headed term keeps all but at most one occurrence of any argument term. -/
theorem g_step_count (c : Term Nat Nat) {l : Label} {xs : List (Term Nat Nat)} {u : Term Nat Nat}
    (h : RuleLabelStep (dupRules r) lab l (.app 1 xs) u) :
    ∃ ys, u = .app 1 ys ∧ xs.count c ≤ ys.count c + 1 := by
  rcases dup_step_cases h with ⟨_, h0, -⟩ | ⟨h2, -⟩ | ⟨pre, post, a, b, hxs, hu, -⟩
  · exact absurd h0 (by decide)
  · exact absurd h2 (by decide)
  · refine ⟨pre ++ b :: post, hu, ?_⟩
    rw [hxs]
    have h1 : (a :: post).count c ≤ post.count c + 1 := by
      rw [List.count_cons]
      split <;> omega
    have h2 : post.count c ≤ (b :: post).count c := by
      rw [List.count_cons]
      split <;> omega
    rw [List.count_append, List.count_append]
    omega

/-- A labeled step of a variable-argument `g` term does not exist. -/
theorem g_vars_no_step {l : Label} {k : Nat} {u : Term Nat Nat} :
    ¬ RuleLabelStep (dupRules r) lab l (.app 1 (List.replicate k (.var 0))) u := by
  intro h
  rcases dup_step_cases h with ⟨_, h0, -⟩ | ⟨h2, -⟩ | ⟨pre, post, a, b, hxs, -, hab⟩
  · exact absurd h0 (by decide)
  · exact absurd h2 (by decide)
  · have ha : a ∈ List.replicate k (Term.var 0) := by
      rw [hxs]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    rw [List.eq_of_mem_replicate ha] at hab
    exact RuleLabelStep.not_var hab

/-! ## The atom peak -/

/-- **The atom peak** `g(a, …, a) ← f(a) → f(b)`. -/
def atomPeak (r : Nat) (lab : Rule Nat Nat → Label) : LocalPeak (RuleLabelStep (dupRules r) lab) where
  source := .app 0 [aT]
  left := .app 1 (List.replicate r aT)
  right := .app 0 [bT]
  leftLabel := lab (dupRule r)
  rightLabel := lab atomRule
  leftStep := dup_root_step r lab aT
  rightStep := RuleLabelStep.arg 0 [] [] (atom_root_step r lab)

/-- The atoms of `g` rewrite one at a time, each step below `α` when `β` is below `α`. -/
theorem star_below_atoms {lt : Label → Label → Prop}
    (hβα : lt (lab atomRule) (lab (dupRule r))) :
    ∀ (k : Nat) (pre : List (Term Nat Nat)),
      Star (StepBelow (RuleLabelStep (dupRules r) lab) lt (lab (dupRule r)))
        (.app 1 (pre ++ List.replicate k aT)) (.app 1 (pre ++ List.replicate k bT))
  | 0, _ => Relation.ReflTransGen.refl
  | k + 1, pre => by
      have hstep : StepBelow (RuleLabelStep (dupRules r) lab) lt (lab (dupRule r))
          (.app 1 (pre ++ aT :: List.replicate k aT)) (.app 1 (pre ++ bT :: List.replicate k aT)) :=
        ⟨lab atomRule, hβα, RuleLabelStep.arg 1 pre _ (atom_root_step r lab)⟩
      have ih := star_below_atoms hβα k (pre ++ [bT])
      simp only [List.append_assoc, List.singleton_append] at ih
      simp only [List.replicate_succ]
      exact Relation.ReflTransGen.head hstep ih

/-- **Sufficiency of the priority.** If `β` is below `α`, the atom peak has a decreasing valley: the
left arm rewrites all `r` atoms with lower-label steps, and the right arm takes the permitted single
duplication step. -/
theorem atom_peak_decreasing_of_lt {lt : Label → Label → Prop}
    (hβα : lt (lab atomRule) (lab (dupRule r))) : (atomPeak r lab).Decreasing lt := by
  refine ⟨{
    leftAfterLow := .app 1 (List.replicate r bT)
    leftAfterPeakLabel := .app 1 (List.replicate r bT)
    join := .app 1 (List.replicate r bT)
    rightAfterLow := .app 0 [bT]
    rightAfterPeakLabel := .app 1 (List.replicate r bT)
    leftLow := by simpa using star_below_atoms hβα r []
    leftPeakLabel := Or.inl rfl
    leftBoth := Relation.ReflTransGen.refl
    rightLow := Relation.ReflTransGen.refl
    rightPeakLabel := Or.inr (dup_root_step r lab bT)
    rightBoth := Relation.ReflTransGen.refl }⟩

/-- **Necessity of the priority for two or more copies.** If `β` is not below `α`, every lower-label
segment on the left is empty and the left arm keeps an atom, while every term on the right arm is
free of `a`. -/
theorem atom_peak_decreasing_imp_lt {lt : Label → Label → Prop} (hirr : ∀ l, ¬ lt l l)
    (hr : 2 ≤ r) (hdec : (atomPeak r lab).Decreasing lt) : lt (lab atomRule) (lab (dupRule r)) := by
  by_contra hβα
  obtain ⟨v⟩ := hdec
  have hleftF : NoSym 0 (.app 1 (List.replicate r aT)) := by
    refine noSym_app_iff.2 ⟨by decide, fun x hx => ?_⟩
    rw [List.eq_of_mem_replicate hx]
    exact noSym_app_iff.2 ⟨by decide, by simp⟩
  -- left: no lower-label step from the left term
  have hlow : (atomPeak r lab).left = v.leftAfterLow := by
    rcases Relation.ReflTransGen.cases_head v.leftLow with h | ⟨c, ⟨c', hlt, hst⟩, -⟩
    · exact h
    · exfalso
      obtain ⟨rfl, -⟩ := step_noF hst hleftF
      exact hβα hlt
  -- left: after the optional `β` step, a `g` term with an atom and no `f`
  have hp : ∃ ys, v.leftAfterPeakLabel = .app 1 ys ∧ 1 ≤ ys.count aT ∧
      NoSym 0 v.leftAfterPeakLabel := by
    rcases v.leftPeakLabel with he | hst
    · refine ⟨List.replicate r aT, he.symm.trans hlow.symm, ?_, ?_⟩
      · rw [List.count_replicate_self]
        omega
      · rw [← he, ← hlow]
        exact hleftF
    · rw [← hlow] at hst
      obtain ⟨ys, hys, hcount⟩ := g_step_count aT hst
      refine ⟨ys, hys, ?_, (step_noF hst hleftF).2⟩
      rw [List.count_replicate_self] at hcount
      omega
  obtain ⟨ys, hys, hcount, hpF⟩ := hp
  have hjoinL : v.leftAfterPeakLabel = v.join := by
    rcases Relation.ReflTransGen.cases_head v.leftBoth with h | ⟨c, ⟨c', hlt, hst⟩, -⟩
    · exact h
    · exfalso
      obtain ⟨rfl, -⟩ := step_noF hst hpF
      rcases hlt with hlt | hlt
      · exact hβα hlt
      · exact hirr _ hlt
  -- right: every term is free of `a`
  have hbA : NoSym 2 bT := noSym_app_iff.2 ⟨by decide, by simp⟩
  have hrightA : NoSym 2 (.app 0 [bT]) := noSym_app_iff.2 ⟨by decide, by simpa using hbA⟩
  have hsub : ∀ x y, StepBelow (RuleLabelStep (dupRules r) lab) lt (lab atomRule) x y →
      ∃ l, RuleLabelStep (dupRules r) lab l x y := fun _ _ ⟨c, _, h⟩ => ⟨c, h⟩
  have hsubE : ∀ x y, StepBelowEither (RuleLabelStep (dupRules r) lab) lt (lab (dupRule r))
      (lab atomRule) x y → ∃ l, RuleLabelStep (dupRules r) lab l x y :=
    fun _ _ ⟨c, _, h⟩ => ⟨c, h⟩
  have h1 : NoSym 2 v.rightAfterLow := star_noSym_two hsub v.rightLow hrightA
  have h2 : NoSym 2 v.rightAfterPeakLabel := by
    rcases v.rightPeakLabel with he | hst
    · rw [← he]
      exact h1
    · exact (step_noA hst h1).2
  have h3 : NoSym 2 v.join := star_noSym_two hsubE v.rightBoth h2
  -- the join both contains and lacks an atom
  rw [← hjoinL, hys] at h3
  have hmem : aT ∈ ys := List.count_pos_iff.1 hcount
  exact h3 aT (Subterm.arg hmem (Subterm.refl _)) [] rfl

/-- **The atom peak classification.** For two or more copies and an irreflexive label relation,
the atom peak has a decreasing valley exactly when the atom label is below the duplication label. -/
theorem atom_peak_decreasing_iff {lt : Label → Label → Prop} (hirr : ∀ l, ¬ lt l l) (hr : 2 ≤ r) :
    (atomPeak r lab).Decreasing lt ↔ lt (lab atomRule) (lab (dupRule r)) :=
  ⟨atom_peak_decreasing_imp_lt hirr hr, atom_peak_decreasing_of_lt⟩

/-- **Zero and one copy.** The atom peak has a decreasing valley for every labeling and every label
relation: at `r = 0` the right arm reaches `g()` by its optional duplication step; at `r = 1` the
left arm takes its optional atom step and the right arm its optional duplication step. -/
theorem atom_peak_small_arity (lab : Rule Nat Nat → Label) (lt : Label → Label → Prop) :
    (atomPeak 0 lab).Decreasing lt ∧ (atomPeak 1 lab).Decreasing lt := by
  refine ⟨⟨{
    leftAfterLow := .app 1 []
    leftAfterPeakLabel := .app 1 []
    join := .app 1 []
    rightAfterLow := .app 0 [bT]
    rightAfterPeakLabel := .app 1 []
    leftLow := Relation.ReflTransGen.refl
    leftPeakLabel := Or.inl rfl
    leftBoth := Relation.ReflTransGen.refl
    rightLow := Relation.ReflTransGen.refl
    rightPeakLabel := Or.inr (dup_root_step 0 lab bT)
    rightBoth := Relation.ReflTransGen.refl }⟩, ⟨{
    leftAfterLow := .app 1 [aT]
    leftAfterPeakLabel := .app 1 [bT]
    join := .app 1 [bT]
    rightAfterLow := .app 0 [bT]
    rightAfterPeakLabel := .app 1 [bT]
    leftLow := Relation.ReflTransGen.refl
    leftPeakLabel := Or.inr (RuleLabelStep.arg 1 [] [] (atom_root_step 1 lab))
    leftBoth := Relation.ReflTransGen.refl
    rightLow := Relation.ReflTransGen.refl
    rightPeakLabel := Or.inr (dup_root_step 1 lab bT)
    rightBoth := Relation.ReflTransGen.refl }⟩⟩

end Family

/-- The rule priority: the atom rule gets `0`, every other rule `1`. -/
def priorityLabel (rule : Rule Nat Nat) : Nat :=
  match rule.lhs with
  | .app 2 _ => 0
  | _ => 1

/-- The priority labels of the two rules. -/
theorem priorityLabel_values (r : Nat) :
    priorityLabel atomRule = 0 ∧ priorityLabel (dupRule r) = 1 :=
  ⟨rfl, rfl⟩

/-- **The rule-priority repair.** With `β = 0` and `α = 1` over `Nat`, the atom peak has a decreasing
valley for every copy count. -/
theorem atom_peak_rule_priority_repair (r : Nat) :
    (atomPeak r priorityLabel).Decreasing (fun m n : Nat => m < n) :=
  atom_peak_decreasing_of_lt (lab := priorityLabel) (lt := fun m n : Nat => m < n) Nat.zero_lt_one

/-! ## The nested peak -/

section Nested

variable {Label : Type w} {r : Nat} {lab : Rule Nat Nat → Label}

/-- The term `f(v)`, with `v` the variable `0`. -/
def fv : Term Nat Nat := .app 0 [.var 0]

/-- The term `g(v, …, v)` with `r` copies. -/
def gv (r : Nat) : Term Nat Nat := .app 1 (List.replicate r (.var 0))

/-- **The nested peak** `g(f(v), …, f(v)) ← f(f(v)) → f(g(v, …, v))`; both labels are `α`. -/
def nestedPeak (r : Nat) (lab : Rule Nat Nat → Label) :
    LocalPeak (RuleLabelStep (dupRules r) lab) where
  source := .app 0 [fv]
  left := .app 1 (List.replicate r fv)
  right := .app 0 [gv r]
  leftLabel := lab (dupRule r)
  rightLabel := lab (dupRule r)
  leftStep := dup_root_step r lab fv
  rightStep := RuleLabelStep.arg 0 [] [] (dup_root_step r lab (.var 0))

/-- `f(v)` is free of `a`. -/
theorem fv_noA : NoSym 2 fv := noSym_app_iff.2 ⟨by decide, by simp [noSym_var]⟩

/-- `g(v, …, v)` is free of `a`. -/
theorem gv_noA (r : Nat) : NoSym 2 (gv r) := by
  refine noSym_app_iff.2 ⟨by decide, fun x hx => ?_⟩
  rw [List.eq_of_mem_replicate hx]
  exact noSym_var 2 0

/-- **The right arm has exactly two optional endpoints**: `f(g(v, …, v))` and
`g(g(v, …, v), …, g(v, …, v))`. -/
theorem nested_right_step {l : Label} {u : Term Nat Nat}
    (h : RuleLabelStep (dupRules r) lab l (.app 0 [gv r]) u) :
    u = .app 1 (List.replicate r (gv r)) := by
  rcases dup_step_cases h with ⟨t, -, ht, hu, -⟩ | ⟨h2, -⟩ | ⟨pre, post, a, b, hxs, -, hab⟩
  · simp only [List.cons.injEq, and_true] at ht
    rw [hu, ← ht]
  · exact absurd h2 (by decide)
  · exfalso
    cases pre with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hxs
        rw [← hxs.1] at hab
        exact g_vars_no_step hab
    | cons p ps =>
        have hlen : (1 : Nat) = ps.length + 1 + (post.length + 1) := by
          simpa using congrArg List.length hxs
        omega

/-- Lower-label segments are empty when every step carries the label `α` and `lt` is irreflexive. -/
theorem nested_no_low_step {lt : Label → Label → Prop} (hirr : ∀ l, ¬ lt l l)
    {x y : Term Nat Nat} (hx : NoSym 2 x)
    (h : Star (StepBelow (RuleLabelStep (dupRules r) lab) lt (lab (dupRule r))) x y) : x = y := by
  rcases Relation.ReflTransGen.cases_head h with he | ⟨c, ⟨c', hlt, hst⟩, -⟩
  · exact he
  · exfalso
    obtain ⟨rfl, -⟩ := step_noA hst hx
    exact hirr _ hlt

/-- The joining segments are empty for the same reason. -/
theorem nested_no_either_step {lt : Label → Label → Prop} (hirr : ∀ l, ¬ lt l l)
    {x y : Term Nat Nat} (hx : NoSym 2 x)
    (h : Star (StepBelowEither (RuleLabelStep (dupRules r) lab) lt (lab (dupRule r))
      (lab (dupRule r))) x y) : x = y := by
  rcases Relation.ReflTransGen.cases_head h with he | ⟨c, ⟨c', hlt, hst⟩, -⟩
  · exact he
  · exfalso
    obtain ⟨rfl, -⟩ := step_noA hst hx
    rcases hlt with hlt | hlt <;> exact hirr _ hlt

/-- **The nested peak has no decreasing valley** for two or more copies, for every constant-per-rule
labeling and every irreflexive label relation. -/
theorem nested_peak_not_decreasing {lt : Label → Label → Prop} (hirr : ∀ l, ¬ lt l l)
    (hr : 2 ≤ r) : ¬ (nestedPeak r lab).Decreasing lt := by
  rintro ⟨v⟩
  have hleftA : NoSym 2 (.app 1 (List.replicate r fv)) := by
    refine noSym_app_iff.2 ⟨by decide, fun x hx => ?_⟩
    rw [List.eq_of_mem_replicate hx]
    exact fv_noA
  have hrightA : NoSym 2 (.app 0 [gv r]) :=
    noSym_app_iff.2 ⟨by decide, by simpa using gv_noA r⟩
  -- left arm: the join is a `g` term keeping a copy of `f(v)`
  have hlow := nested_no_low_step hirr hleftA v.leftLow
  have hp : ∃ ys, v.leftAfterPeakLabel = .app 1 ys ∧ 1 ≤ ys.count fv ∧
      NoSym 2 v.leftAfterPeakLabel := by
    rcases v.leftPeakLabel with he | hst
    · refine ⟨List.replicate r fv, he.symm.trans hlow.symm, ?_, ?_⟩
      · rw [List.count_replicate_self]
        omega
      · rw [← he, ← hlow]
        exact hleftA
    · rw [← hlow] at hst
      obtain ⟨ys, hys, hcount⟩ := g_step_count fv hst
      refine ⟨ys, hys, ?_, (step_noA hst hleftA).2⟩
      rw [List.count_replicate_self] at hcount
      omega
  obtain ⟨ys, hys, hcount, hpA⟩ := hp
  have hjoinL := nested_no_either_step hirr hpA v.leftBoth
  -- right arm: the join is `f(g(v, …, v))` or `g(g(v, …, v), …)`
  have hrlow := nested_no_low_step hirr hrightA v.rightLow
  have hq : v.rightAfterPeakLabel = .app 0 [gv r] ∨
      v.rightAfterPeakLabel = .app 1 (List.replicate r (gv r)) := by
    rcases v.rightPeakLabel with he | hst
    · exact Or.inl (he.symm.trans hrlow.symm)
    · rw [← hrlow] at hst
      exact Or.inr (nested_right_step hst)
  have hqA : NoSym 2 v.rightAfterPeakLabel := by
    rcases hq with h | h
    · rw [h]
      exact hrightA
    · rw [h]
      refine noSym_app_iff.2 ⟨by decide, fun x hx => ?_⟩
      rw [List.eq_of_mem_replicate hx]
      exact gv_noA r
  have hjoinR := nested_no_either_step hirr hqA v.rightBoth
  -- the two endpoints of the join disagree
  have hmeet : v.leftAfterPeakLabel = v.rightAfterPeakLabel := hjoinL.trans hjoinR.symm
  rw [hys] at hmeet
  rcases hq with h | h
  · rw [h] at hmeet
    simp at hmeet
  · rw [h] at hmeet
    simp only [Term.app.injEq, true_and] at hmeet
    rw [hmeet, List.count_replicate] at hcount
    simp [fv, gv] at hcount

/-- **No constant-per-rule labeling makes every local peak of `R_r` decreasing** when `r ≥ 2`, for
every label type and every irreflexive label relation. -/
theorem no_constant_rule_labeling (hr : 2 ≤ r) (lt : Label → Label → Prop) (hirr : ∀ l, ¬ lt l l)
    (lab : Rule Nat Nat → Label) : ¬ AllLocalPeaksDecreasing (RuleLabelStep (dupRules r) lab) lt :=
  fun h => nested_peak_not_decreasing hirr hr (h (nestedPeak r lab))

/-- The rule priority repairs the atom peak and still fails the nested peak for `r ≥ 2`. -/
theorem priority_repairs_atom_peak_only (hr : 2 ≤ r) :
    (atomPeak r priorityLabel).Decreasing (fun m n : Nat => m < n) ∧
      ¬ AllLocalPeaksDecreasing (RuleLabelStep (dupRules r) priorityLabel) (fun m n : Nat => m < n) :=
  ⟨atom_peak_rule_priority_repair r,
    no_constant_rule_labeling hr (fun m n : Nat => m < n) (fun l => Nat.lt_irrefl l) priorityLabel⟩

/-- The copies of `f(v)` rewrite one at a time. -/
theorem stepStar_rewrite_copies :
    ∀ (k : Nat) (pre : List (Term Nat Nat)),
      StepStar (dupRules r) (.app 1 (pre ++ List.replicate k fv))
        (.app 1 (pre ++ List.replicate k (gv r)))
  | 0, _ => StepStar.refl _ _
  | k + 1, pre => by
      have hstep : Step (dupRules r) (.app 1 (pre ++ fv :: List.replicate k fv))
          (.app 1 (pre ++ gv r :: List.replicate k fv)) :=
        Step.arg 1 pre _ (ruleLabelStep_iff_step.1
          ⟨_, dup_root_step r (fun _ : Rule Nat Nat => ()) (.var 0)⟩)
      have ih := stepStar_rewrite_copies k (pre ++ [gv r])
      simp only [List.append_assoc, List.singleton_append] at ih
      simp only [List.replicate_succ]
      exact StepStar.head hstep ih

/-- **The nested peak joins ordinarily**: the left arm reaches `g(g(v, …, v), …)` in `r` steps and
the right arm in one step. Failure of the label discipline is compatible with joinability. -/
theorem nested_peak_ordinary_join (r : Nat) :
    StepStar (dupRules r) (.app 1 (List.replicate r fv)) (.app 1 (List.replicate r (gv r))) ∧
      Step (dupRules r) (.app 0 [gv r]) (.app 1 (List.replicate r (gv r))) ∧
      joinable (dupRules r) (.app 1 (List.replicate r fv)) (.app 0 [gv r]) := by
  have hl : StepStar (dupRules r) (.app 1 (List.replicate r fv))
      (.app 1 (List.replicate r (gv r))) := by
    simpa using stepStar_rewrite_copies (r := r) r []
  have hs : Step (dupRules r) (.app 0 [gv r]) (.app 1 (List.replicate r (gv r))) :=
    ruleLabelStep_iff_step.1 ⟨_, dup_root_step r (fun _ => ()) (gv r)⟩
  exact ⟨hl, hs, ⟨_, hl, StepStar.single hs⟩⟩

end Nested

end OperatorKO7.Meta.UniqueNormalization.DuplicationLabels

/-! ## KLOP-FAIL-005, landed

The declarations below reproduce `.agent-tmp/KlopMinimalLevelCheck.lean` (SHA-256
`EDEDAD86E2F3A06E3EE719725C644E08E56177D7C585FDA1D789900AFB7AF0E4`) with unchanged names and
statements. -/

namespace OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication

open OperatorKO7.Meta.Rewriting

/-- Terms over `Nat` symbols and variables. -/
abbrev T := Term Nat Nat
/-- `f(x)`. -/
def f (x : T) : T := .app 0 [x]
/-- `g(x, y)`. -/
def g (x y : T) : T := .app 1 [x, y]
/-- `a`. -/
def a : T := .app 2 []
/-- `b`. -/
def b : T := .app 3 []
/-- `f(x) → g(x, x)`. -/
def duplicate : Rule Nat Nat := ⟨f (.var 0), g (.var 0) (.var 0), rfl⟩
/-- `a → b`. -/
def atom : Rule Nat Nat := ⟨a, b, rfl⟩
/-- The two rules. -/
def rules : TRS Nat Nat := [duplicate, atom]
/-- The minimum label `(0, 0)`. -/
def zeroLabel : LevelLabel := ⟨0, 0⟩

theorem no_label_below_zero (l : LevelLabel) : ¬ LevelLabelLt l zeroLabel := by
  simp [levelLabelLt_iff, zeroLabel]

theorem star_eq_of_no_edges {X : Type*} {r : X → X → Prop}
    (hn : ∀ x y, ¬ r x y) {x y : X} (h : Star r x y) : x = y := by
  induction h with
  | refl => rfl
  | tail _ hs _ => exact False.elim (hn _ _ hs)

theorem zero_valley_has_optional_join
    {X : Type*} {s : LabelledStep X LevelLabel} (p : LocalPeak s)
    (hl : p.leftLabel = zeroLabel) (hr : p.rightLabel = zeroLabel)
    (hv : p.Decreasing LevelLabelLt) :
    ∃ m, OptionalLabelStep s zeroLabel p.left m ∧
      OptionalLabelStep s zeroLabel p.right m := by
  obtain ⟨v⟩ := hv
  have hleft : p.left = v.leftAfterLow :=
    star_eq_of_no_edges (by
      intro x y h
      obtain ⟨l, hlt, _⟩ := h
      rw [hl] at hlt
      exact no_label_below_zero l hlt) v.leftLow
  have hright : p.right = v.rightAfterLow :=
    star_eq_of_no_edges (by
      intro x y h
      obtain ⟨l, hlt, _⟩ := h
      rw [hr] at hlt
      exact no_label_below_zero l hlt) v.rightLow
  have hnone : ∀ x y, ¬ StepBelowEither s LevelLabelLt
      p.leftLabel p.rightLabel x y := by
    intro x y h
    obtain ⟨l, hlt, _⟩ := h
    rw [hl, hr] at hlt
    exact hlt.elim (no_label_below_zero l) (no_label_below_zero l)
  have hlj := star_eq_of_no_edges hnone v.leftBoth
  have hrj := star_eq_of_no_edges hnone v.rightBoth
  refine ⟨v.join, ?_, ?_⟩
  · simpa only [hr, ← hleft, hlj] using v.leftPeakLabel
  · simpa only [hl, ← hright, hrj] using v.rightPeakLabel

theorem hub_rules : linHub rules =
    [⟨f (.var 0), g (.var 0) (.var 0), [], rfl⟩,
     ⟨a, b, [], rfl⟩] := by
  simp [linHub, rules, hubCRule, duplicate, atom, f, g, a, b,
    hubSplitTerm, hubSplitConditions, hubSplitTermAux, hubSplitListAux]

theorem root_iff (E : T → T → Prop) (x y : T) :
    crootStepE (linHub rules) E x y ↔
      (∃ u, x = f u ∧ y = g u u) ∨ (x = a ∧ y = b) := by
  rw [hub_rules]
  constructor
  · rintro ⟨rule, hmem, σ, hs, ht, _⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl ⟨σ 0, hs, ht⟩
    · exact Or.inr ⟨hs, ht⟩
  · rintro (⟨u, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨f (.var 0), g (.var 0) (.var 0), [], rfl⟩,
        by simp, (fun _ => u), rfl, rfl, by simp⟩
    · exact ⟨⟨a, b, [], rfl⟩, by simp, Subst.id, rfl, rfl, by simp⟩

theorem app_step_inv (E : T → T → Prop) {h : Nat} {xs : List T} {y : T}
    (hs : CStepE (linHub rules) E (.app h xs) y) :
    ((∃ u, .app h xs = f u ∧ y = g u u) ∨ (.app h xs = a ∧ y = b)) ∨
      ∃ pre post x z, xs = pre ++ x :: post ∧
        y = .app h (pre ++ z :: post) ∧ CStepE (linHub rules) E x z := by
  rcases hs.app_inv with hr | hc
  · exact Or.inl ((root_iff E _ _).mp hr)
  · exact Or.inr hc

theorem step_a (E : T → T → Prop) {y : T}
    (h : CStepE (linHub rules) E a y) : y = b := by
  rcases app_step_inv E h with hr | ⟨pre, post, x, z, he, _, _⟩
  · simpa [f, a, Term.app.injEq] using hr
  · have : (0 : Nat) = pre.length + (post.length + 1) := by
      simpa using congrArg List.length he
    omega

theorem no_step_b (E : T → T → Prop) {y : T} :
    ¬ CStepE (linHub rules) E b y := by
  intro h
  rcases app_step_inv E h with hr | ⟨pre, post, x, z, he, _, _⟩
  · simp [f, a, b, Term.app.injEq] at hr
  · have : (0 : Nat) = pre.length + (post.length + 1) := by
      simpa using congrArg List.length he
    omega

theorem singleton_split {X : Type*} {u x : X} {pre post : List X}
    (h : [u] = pre ++ x :: post) : pre = [] ∧ x = u ∧ post = [] := by
  cases pre with
  | nil => simpa using h.symm
  | cons v vs =>
      have : 1 = vs.length + 1 + (post.length + 1) := by
        simpa using congrArg List.length h
      omega

theorem pair_split {X : Type*} {u v x : X} {pre post : List X}
    (h : [u, v] = pre ++ x :: post) :
    (pre = [] ∧ x = u ∧ post = [v]) ∨
    (pre = [u] ∧ x = v ∧ post = []) := by
  cases pre with
  | nil => exact Or.inl (by simpa using h.symm)
  | cons w ws =>
      have h' : u = w ∧ [v] = ws ++ x :: post := List.cons.inj h
      obtain ⟨rfl, rfl, rfl⟩ := singleton_split h'.2
      exact Or.inr ⟨by simp [h'.1], rfl, rfl⟩

theorem step_gaa (E : T → T → Prop) {y : T}
    (h : CStepE (linHub rules) E (g a a) y) :
    y = g b a ∨ y = g a b := by
  rcases app_step_inv E h with hr | ⟨pre, post, x, z, he, hy, hxz⟩
  · simp [f, g, a, Term.app.injEq] at hr
  · rcases pair_split he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl (hy.trans (by simp [step_a E hxz, g]))
    · exact Or.inr (hy.trans (by simp [step_a E hxz, g]))

theorem step_fb (E : T → T → Prop) {y : T}
    (h : CStepE (linHub rules) E (f b) y) : y = g b b := by
  rcases app_step_inv E h with hr | ⟨pre, post, x, z, he, _, hxz⟩
  · simpa [f, a, Term.app.injEq] using hr
  · obtain ⟨rfl, rfl, rfl⟩ := singleton_split he
    exact False.elim (no_step_b E hxz)

theorem level_one_minimal {x y : T}
    (h : CStepLevel (linHub rules) 1 x y) :
    minimalLevelStep (linHub rules) zeroLabel x y := by
  refine ⟨rfl, h, ?_⟩
  intro m hm hh
  change m < 1 at hm
  have : m = 0 := by omega
  subst m
  exact hh

/-- The failing peak `g(a, a) ← f(a) → f(b)`, both labels `(0, 0)`. -/
def peak : LocalPeak (minimalLevelStep (linHub rules)) where
  source := f a
  left := g a a
  right := f b
  leftLabel := zeroLabel
  rightLabel := zeroLabel
  leftStep := level_one_minimal (CStepE.root
    ((root_iff _ _ _).mpr (Or.inl ⟨a, rfl, rfl⟩)))
  rightStep := level_one_minimal (CStepE.arg 0 [] [] (CStepE.root
    ((root_iff _ _ _).mpr (Or.inr ⟨rfl, rfl⟩))))

theorem peak_not_decreasing : ¬ peak.Decreasing LevelLabelLt := by
  intro h
  obtain ⟨m, hl, hr⟩ := zero_valley_has_optional_join peak rfl rfl h
  have hl' : m = g a a ∨ m = g b a ∨ m = g a b := by
    rcases hl with he | hs
    · exact Or.inl he.symm
    · exact Or.inr (step_gaa _ hs.2.1)
  have hr' : m = f b ∨ m = g b b := by
    rcases hr with he | hs
    · exact Or.inl he.symm
    · exact Or.inr (step_fb _ hs.2.1)
  rcases hl' with rfl | rfl | rfl <;>
    simp [f, g, a, b, Term.app.injEq] at hr'

theorem minimalLevel_not_allLocalPeaksDecreasing :
    ¬ AllLocalPeaksDecreasing (minimalLevelStep (linHub rules)) LevelLabelLt :=
  fun h => peak_not_decreasing (h peak)

theorem app_subterm_unary_var {s : T} {h x : Nat}
    (hs : Subterm s (.app h [.var x])) (ha : s.isApp = true) :
    s = .app h [.var x] := by
  cases hs with
  | refl => rfl
  | arg hm hsub =>
      simp only [List.mem_singleton] at hm
      subst hm
      have hh := hsub.eq_of_var
      simp [hh] at ha

theorem app_subterm_constant {s : T} {h : Nat}
    (hs : Subterm s (.app h [])) : s = .app h [] := by
  cases hs with
  | refl => rfl
  | arg hm _ => simp at hm

theorem omega_heads {i j : Nat} {xs ys : List T}
    (h : OmegaUnifiable (.app i xs) (.app j ys)) : i = j := by
  obtain ⟨E, hE, he⟩ := h
  exact hE.symbol_eq he

theorem rules_nonOmegaOverlapping : NonOmegaOverlapping rules := by
  intro r hr q hq s hs ha hu
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr hq
  rcases hr with rfl | rfl
  · have hh := app_subterm_unary_var hs ha
    subst s
    rcases hq with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · have hbad : (0 : Nat) = 2 := omega_heads hu
      omega
  · have hh := app_subterm_constant hs
    subst s
    rcases hq with rfl | rfl
    · have hbad : (2 : Nat) = 0 := omega_heads hu
      omega
    · exact ⟨rfl, rfl⟩

theorem rules_rhsDetermined : TRS.RhsDetermined rules := by
  intro r hr
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · intro σ τ he
    have hv : σ 0 = τ 0 := by
      simpa [duplicate, f, Subst.apply, Subst.applyList, Term.app.injEq] using he
    simp [duplicate, g, Subst.apply, Subst.applyList, hv]
  · intro σ τ _
    rfl

/-- **The minimum-level refutation** (KLOP-FAIL-005): the universal minimum-level decreasingness
statement is false for the class. -/
theorem no_universal_minimalLevel_closeout :
    ¬ (∀ R : TRS Nat Nat, NonOmegaOverlapping R → TRS.RhsDetermined R →
      AllLocalPeaksDecreasing (minimalLevelStep (linHub R)) LevelLabelLt) := by
  intro h
  exact minimalLevel_not_allLocalPeaksDecreasing
    (h rules rules_nonOmegaOverlapping rules_rhsDetermined)

end OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication

namespace OperatorKO7.Meta.UniqueNormalization.DuplicationLabels

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

/-- **The landed KLOP-FAIL-005 statement**, unchanged. -/
theorem minimum_level_refutation_preserved :
    ¬ (∀ R : TRS Nat Nat, NonOmegaOverlapping R → TRS.RhsDetermined R →
      AllLocalPeaksDecreasing (minimalLevelStep (linHub R)) LevelLabelLt) :=
  MinimalLevelDuplication.no_universal_minimalLevel_closeout

/-- The KLOP-FAIL-005 system is `R_2`. -/
theorem minimalLevel_rules_eq_dupRules : MinimalLevelDuplication.rules = dupRules 2 := rfl

end OperatorKO7.Meta.UniqueNormalization.DuplicationLabels
