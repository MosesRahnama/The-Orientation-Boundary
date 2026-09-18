import OperatorKO7.Meta.UniqueNormalization.UNStatement

/-!
# Semi-equational conditional rewriting, stratified by levels

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K2, route R2.

A conditional rule fires only when its conditions hold, and in the
semi-equational reading a condition holds when its two instances are
**convertible in the conditional system itself**. That self-reference is
resolved the standard way, by levels: a level `n+1` step discharges its
conditions with conversions built from level `n` steps, and level `0` has no
steps at all, so level `1` steps are those whose condition instances are
syntactically equal.

The module also provides a small abstract-rewriting layer over an arbitrary
relation (`relStar`, `relConv`, `relJoinable`, `relConfluent`), because the
conditional system needs the same conversion-to-joinability lemma that
`UNStatement.lean` proves for unconditional systems, and one generic proof
serves both.

Named error class for this campaign (roadmap, binding rules): in this file and
`Linearization.lean`, the transformed rule's target is the original rule's
right-hand side under the substitution, never a recursive call and never a
freshly invented contractum. The in-file example exhibits a level-1 firing whose
target agrees with the unconditional rule it came from.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

/-! ## Abstract rewriting over one relation -/

section AbstractRewriting

variable {alpha : Type u} (r : alpha → alpha → Prop)

/-- Reflexive-transitive closure. -/
def relStar : alpha → alpha → Prop := Relation.ReflTransGen r

/-- Conversion: the equivalence closure, as the reflexive-transitive closure of
the symmetric closure. -/
def relConv : alpha → alpha → Prop :=
  Relation.ReflTransGen (fun a b => r a b ∨ r b a)

/-- Joinability. -/
def relJoinable (a b : alpha) : Prop := ∃ c, relStar r a c ∧ relStar r b c

/-- Confluence. -/
def relConfluent : Prop :=
  ∀ a b c, relStar r a b → relStar r a c → relJoinable r b c

variable {r}

theorem relConv.refl (a : alpha) : relConv r a a := Relation.ReflTransGen.refl

theorem relConv.single {a b : alpha} (h : r a b) : relConv r a b :=
  Relation.ReflTransGen.single (Or.inl h)

theorem relConv.trans {a b c : alpha} (hab : relConv r a b) (hbc : relConv r b c) :
    relConv r a c :=
  Relation.ReflTransGen.trans hab hbc

theorem relConv.symm {a b : alpha} (h : relConv r a b) : relConv r b a := by
  induction h with
  | refl => exact relConv.refl a
  | tail _ hlast ih =>
      exact relConv.trans (Relation.ReflTransGen.single (Or.symm hlast)) ih

/-- Conversion is monotone in its generating relation. -/
theorem relConv.mono {q : alpha → alpha → Prop}
    (hrq : ∀ a b, r a b → q a b) {a b : alpha} (h : relConv r a b) : relConv q a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases hlast with hab | hba
      · exact Or.inl (hrq _ _ hab)
      · exact Or.inr (hrq _ _ hba)

/-- A conversion built from a subrelation of `conv R` is itself a `conv R`
conversion. Stated against the concrete `conv` of `UNStatement.lean`, which is
where it is consumed. -/
theorem conv_of_relConv {sigma : Type u} {nu : Type v} {R : TRS sigma nu}
    {q : Term sigma nu → Term sigma nu → Prop}
    (hq : ∀ a b, q a b → conv R a b) {s t : Term sigma nu}
    (h : relConv q s t) : conv R s t := by
  induction h with
  | refl => exact conv.refl R s
  | tail _ hlast ih =>
      rcases hlast with hstep | hstep
      · exact conv.trans ih (hq _ _ hstep)
      · exact conv.trans ih (conv.symm (hq _ _ hstep))

/-- Under confluence, every conversion is a joinability. The same induction as
`joinable_of_conv` in `UNStatement.lean`, over an arbitrary relation. -/
theorem relJoinable_of_relConv (hc : relConfluent r) {a b : alpha}
    (h : relConv r a b) : relJoinable r a b := by
  induction h with
  | refl => exact ⟨a, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @tail m n _ hmn ih =>
      obtain ⟨w, haw, hmw⟩ := ih
      rcases hmn with hstep | hstep
      · obtain ⟨z, hwz, hnz⟩ := hc m w n hmw (Relation.ReflTransGen.single hstep)
        exact ⟨z, Relation.ReflTransGen.trans haw hwz, hnz⟩
      · exact ⟨w, haw, Relation.ReflTransGen.head hstep hmw⟩

end AbstractRewriting

variable {sigma : Type u} {nu : Type v}

/-! ## Conditional rules and the oracle-indexed step -/

/-- A conditional rewrite rule: left-hand side, right-hand side, and a list of
condition pairs. The left-hand side is an application, as for `Rule`. -/
structure CRule (sigma : Type u) (nu : Type v) where
  /-- The left-hand side. -/
  lhs : Term sigma nu
  /-- The right-hand side. -/
  rhs : Term sigma nu
  /-- The conditions: each pair must instantiate to related terms. -/
  conds : List (Term sigma nu × Term sigma nu)
  /-- The left-hand side is an application. -/
  lhs_isApp : lhs.isApp = true

/-- A conditional term rewriting system. -/
abbrev CTRS (sigma : Type u) (nu : Type v) := List (CRule sigma nu)

/-- Root contraction of a conditional rule, with every condition instance
discharged by the oracle relation `E`. -/
def crootStepE (C : CTRS sigma nu) (E : Term sigma nu → Term sigma nu → Prop)
    (s t : Term sigma nu) : Prop :=
  ∃ crule ∈ C, ∃ σ : Subst sigma nu,
    s = Subst.apply σ crule.lhs ∧ t = Subst.apply σ crule.rhs ∧
    ∀ p ∈ crule.conds, E (Subst.apply σ p.1) (Subst.apply σ p.2)

/-- Context closure of the conditional root step, with oracle `E`: the same two
constructors as the unconditional `Step`. -/
inductive CStepE (C : CTRS sigma nu) (E : Term sigma nu → Term sigma nu → Prop) :
    Term sigma nu → Term sigma nu → Prop
  | root {s t : Term sigma nu} (h : crootStepE C E s t) : CStepE C E s t
  | arg (f : sigma) (pre post : List (Term sigma nu)) {a b : Term sigma nu} :
      CStepE C E a b →
      CStepE C E (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

/-- Inversion at an application, mirroring `Step.app_inv`. -/
theorem CStepE.app_inv {C : CTRS sigma nu}
    {E : Term sigma nu → Term sigma nu → Prop} {f : sigma}
    {args : List (Term sigma nu)} {u : Term sigma nu}
    (h : CStepE C E (.app f args) u) :
    crootStepE C E (.app f args) u ∨
      ∃ (pre post : List (Term sigma nu)) (a b : Term sigma nu),
        args = pre ++ a :: post ∧ u = .app f (pre ++ b :: post) ∧ CStepE C E a b := by
  cases h with
  | root hr => exact Or.inl hr
  | arg g pre post hab => exact Or.inr ⟨pre, post, _, _, rfl, rfl, hab⟩

/-- The oracle-indexed step is monotone in the oracle. -/
theorem CStepE.mono {C : CTRS sigma nu}
    {E E' : Term sigma nu → Term sigma nu → Prop}
    (hEE : ∀ a b, E a b → E' a b) :
    ∀ {s t : Term sigma nu}, CStepE C E s t → CStepE C E' s t := by
  intro s t h
  induction h with
  | root hr =>
      obtain ⟨crule, hmem, σ, hs, ht, hconds⟩ := hr
      exact CStepE.root ⟨crule, hmem, σ, hs, ht, fun p hp => hEE _ _ (hconds p hp)⟩
  | arg f pre post _ ih => exact CStepE.arg f pre post ih

/-! ## The level stratification -/

/-- The level-`n` conditional step relation. Level `0` is empty; a level `n+1`
step discharges its conditions with conversions of level-`n` steps. Level `1`
steps therefore have syntactically equal condition instances, because the
conversion generated by the empty relation is equality. -/
def CStepLevel (C : CTRS sigma nu) : Nat → Term sigma nu → Term sigma nu → Prop
  | 0 => fun _ _ => False
  | n + 1 => CStepE C (relConv (CStepLevel C n))

@[simp] theorem CStepLevel_zero (C : CTRS sigma nu) (s t : Term sigma nu) :
    CStepLevel C 0 s t ↔ False := Iff.rfl

theorem CStepLevel_succ (C : CTRS sigma nu) (n : Nat) (s t : Term sigma nu) :
    CStepLevel C (n + 1) s t ↔ CStepE C (relConv (CStepLevel C n)) s t := Iff.rfl

/-- **Level monotonicity.** Every level-`n` step remains available at level `n+1`.
Thus the stratification is an increasing chain rather than merely a family of
approximants. -/
theorem CStepLevel.mono (C : CTRS sigma nu) :
    ∀ n {s t : Term sigma nu}, CStepLevel C n s t → CStepLevel C (n + 1) s t := by
  intro n
  induction n with
  | zero =>
      intro s t h
      exact h.elim
  | succ n ih =>
      intro s t h
      change CStepE C (relConv (CStepLevel C (n + 1))) s t
      change CStepE C (relConv (CStepLevel C n)) s t at h
      exact CStepE.mono
        (fun a b hab => relConv.mono (fun x y hxy => ih hxy) hab) h

/-- Level monotonicity at arbitrary later stages. -/
theorem CStepLevel.mono_of_le (C : CTRS sigma nu) {m n : Nat} (hmn : m ≤ n)
    {s t : Term sigma nu} (h : CStepLevel C m s t) : CStepLevel C n s t := by
  induction hmn with
  | refl => exact h
  | @step n _ ih => exact CStepLevel.mono C n ih

/-- The conditional step relation: a step at some level. -/
def CStep (C : CTRS sigma nu) (s t : Term sigma nu) : Prop :=
  ∃ n, CStepLevel C n s t

/-- Reduction, conversion, and confluence of the conditional system. -/
def CStepStar (C : CTRS sigma nu) : Term sigma nu → Term sigma nu → Prop :=
  relStar (CStep C)

/-- Conversion of the conditional system. -/
def cconv (C : CTRS sigma nu) : Term sigma nu → Term sigma nu → Prop :=
  relConv (CStep C)

/-- Confluence of the conditional system. -/
def cconfluent (C : CTRS sigma nu) : Prop :=
  relConfluent (CStep C)

/-- A step at any positive level is a step of the system. -/
theorem CStep.of_level {C : CTRS sigma nu} {n : Nat} {s t : Term sigma nu}
    (h : CStepLevel C n s t) : CStep C s t := ⟨n, h⟩

/-- The step relation is closed under one argument position, at the same level. -/
theorem CStep.arg (C : CTRS sigma nu) (f : sigma) (pre post : List (Term sigma nu))
    {a b : Term sigma nu} (h : CStep C a b) :
    CStep C (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact hn.elim
  | succ m => exact ⟨m + 1, CStepE.arg f pre post hn⟩

/-! ## Non-vacuity: a genuine level-2 step

The system has the unconditional rule `b -> c` and the conditional rule
`f(x, y) -> a` under the condition `x ~ y`. The term `f(b, c)` is a level-2
redex: its condition instance is the pair `(b, c)`, equal only after the level-1
step `b -> c`, so the conditional machinery is exercised beyond the equal-
arguments case. Symbols: `b = 0`, `c = 1`, `f = 2`, `a = 3`. -/

namespace CondExample

/-- `b -> c`, unconditional. -/
def crB : CRule Nat Nat := ⟨.app 0 [], .app 1 [], [], rfl⟩

/-- `f(x, y) -> a` under the condition `x ~ y`. Its target is the rule's own
right-hand side `a`; per the campaign's named error class, the target of a
transformed rule is never a recursive call and never the condition's terms. -/
def crF : CRule Nat Nat := ⟨.app 2 [.var 0, .var 1], .app 3 [], [(.var 0, .var 1)], rfl⟩

/-- The demonstration system. -/
def demoCTRS : CTRS Nat Nat := [crB, crF]

/-- The substitution sending `x` to `b` and every other variable to `c`. -/
def subBC : Subst Nat Nat := fun v => if v = 0 then .app 0 [] else .app 1 []

/-- Level 1: `b -> c`, conditions vacuous. -/
theorem step_b_c : CStepLevel demoCTRS 1 (.app 0 []) (.app 1 []) :=
  CStepE.root ⟨crB, List.Mem.head _, subBC, rfl, rfl, fun p hp => by cases hp⟩

/-- Level 2: `f(b, c) -> a`, the condition `(b, c)` discharged by the level-1
conversion through `b -> c`. -/
theorem step_fbc_a :
    CStepLevel demoCTRS 2 (.app 2 [.app 0 [], .app 1 []]) (.app 3 []) := by
  refine CStepE.root ⟨crF, List.Mem.tail _ (List.Mem.head _), subBC, rfl, rfl, ?_⟩
  intro p hp
  simp only [crF, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact Relation.ReflTransGen.single (Or.inl step_b_c)

/-- The two steps package into system steps, so `f(b, c)` reduces to `a`. -/
theorem cstepStar_fbc_a :
    CStepStar demoCTRS (.app 2 [.app 0 [], .app 1 []]) (.app 3 []) :=
  Relation.ReflTransGen.single (CStep.of_level step_fbc_a)

/-- The equal-arguments firing at level 1: `f(b, b) -> a` with the condition
instance `(b, b)` discharged by reflexivity. The target agrees with the target
of the diagonal unconditional rule `f(x, x) -> a` on the same term, which is the
in-file exhibit for the campaign's named error class. -/
theorem step_fbb_a :
    CStepLevel demoCTRS 1 (.app 2 [.app 0 [], .app 0 []]) (.app 3 []) := by
  refine CStepE.root ⟨crF, List.Mem.tail _ (List.Mem.head _),
    (fun _ => .app 0 []), rfl, rfl, ?_⟩
  intro p hp
  simp only [crF, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact Relation.ReflTransGen.refl

end CondExample

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.relStar
#check @OperatorKO7.Meta.UniqueNormalization.relConv
#check @OperatorKO7.Meta.UniqueNormalization.relJoinable
#check @OperatorKO7.Meta.UniqueNormalization.relConfluent
#check @OperatorKO7.Meta.UniqueNormalization.CRule
#check @OperatorKO7.Meta.UniqueNormalization.CTRS
#check @OperatorKO7.Meta.UniqueNormalization.crootStepE
#check @OperatorKO7.Meta.UniqueNormalization.CStepE
#check @OperatorKO7.Meta.UniqueNormalization.CStepLevel
#check @OperatorKO7.Meta.UniqueNormalization.CStepLevel.mono
#check @OperatorKO7.Meta.UniqueNormalization.CStepLevel.mono_of_le
#check @OperatorKO7.Meta.UniqueNormalization.CStep
#check @OperatorKO7.Meta.UniqueNormalization.CStepStar
#check @OperatorKO7.Meta.UniqueNormalization.cconv
#check @OperatorKO7.Meta.UniqueNormalization.cconfluent

#print axioms OperatorKO7.Meta.UniqueNormalization.relConv.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_of_relConv
#print axioms OperatorKO7.Meta.UniqueNormalization.relJoinable_of_relConv
#print axioms OperatorKO7.Meta.UniqueNormalization.CStepE.app_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.CStepE.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.relConv.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.CStepLevel.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.CStepLevel.mono_of_le
#print axioms OperatorKO7.Meta.UniqueNormalization.CStep.arg
#print axioms OperatorKO7.Meta.UniqueNormalization.CondExample.step_b_c
#print axioms OperatorKO7.Meta.UniqueNormalization.CondExample.step_fbc_a
#print axioms OperatorKO7.Meta.UniqueNormalization.CondExample.step_fbb_a
