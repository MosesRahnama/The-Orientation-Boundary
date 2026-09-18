import OperatorKO7.Meta.UniqueNormalization.OverlapClasses
import OperatorKO7.Meta.UniqueNormalization.ConditionalTRS

/-!
# Conditional linearization: the hub specification

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K2, route R2; design record in
Section 11.3 of that roadmap.

A rule with a repeated left-hand-side variable internalizes an equality test.
Linearization moves that test into an explicit condition: the first occurrence
of each repeated variable keeps its name (the hub), later occurrences become
fresh variables, each fresh variable gets the condition that it converts to its
hub, and the right-hand side is kept verbatim. The collapse map `rho` sends each
fresh variable back to its hub and fixes everything else.

The transfer proof consumes this construction relationally, so the specification
is a `Prop` between one unconditional rule and one conditional rule, with the
collapse map existentially bound: `LinearizesRule`. Left-linearity of the
conditional left-hand side is deliberately absent from the specification: the
transfer proof never uses it, and it is a property the concrete hub transform
has, never an input the theorem needs.

Named error class (roadmap, binding rules): the conditional rule's target is the
original rule's right-hand side, kept verbatim; it is never a recursive call and
never a condition term. The specification pins this with `crule.rhs = rule.rhs`,
and the in-file example exhibits it.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Variable occurrence -/

/-- `x` occurs in `t`. The occurrence-based twin of `Term.vars`, free of any
`DecidableEq` requirement. -/
inductive VarOccurs (x : nu) : Term sigma nu → Prop
  | here : VarOccurs x (.var x)
  | arg {f : sigma} {args : List (Term sigma nu)} {a : Term sigma nu} :
      a ∈ args → VarOccurs x a → VarOccurs x (.app f args)

/-- An occurrence in an application is an occurrence in one of its arguments. -/
theorem VarOccurs.app_inv {x : nu} {f : sigma} {args : List (Term sigma nu)}
    (h : VarOccurs x (.app f args)) : ∃ a ∈ args, VarOccurs x a := by
  cases h with
  | arg ha hx => exact ⟨_, ha, hx⟩

/-- The instance of an occurring variable is at most as large as the whole
instance. -/
theorem VarOccurs.size_apply_le {x : nu} {t : Term sigma nu}
    (h : VarOccurs x t) (s : Subst sigma nu) :
    (s x).size ≤ (Subst.apply s t).size := by
  induction h with
  | here => exact Nat.le_refl _
  | @arg f args a ha _ ih =>
      refine le_of_lt (lt_of_le_of_lt ih ?_)
      have hmem : Subst.apply s a ∈ Subst.applyList s args := by
        rw [Subst.applyList_eq_map]
        exact List.mem_map_of_mem ha
      simpa using Term.size_lt_of_mem (f := f) hmem

/-- The instance of a variable occurring in an application is strictly smaller
than the whole instance. This carries the size induction of the transfer
theorem. -/
theorem VarOccurs.size_apply_lt_of_isApp {x : nu} {t : Term sigma nu}
    (h : VarOccurs x t) (happ : t.isApp = true) (s : Subst sigma nu) :
    (s x).size < (Subst.apply s t).size := by
  cases t with
  | var y => simp at happ
  | app f args =>
      obtain ⟨a, ha, hx⟩ := h.app_inv
      refine lt_of_le_of_lt (hx.size_apply_le s) ?_
      have hmem : Subst.apply s a ∈ Subst.applyList s args := by
        rw [Subst.applyList_eq_map]
        exact List.mem_map_of_mem ha
      simpa using Term.size_lt_of_mem (f := f) hmem

/-- The instance of an occurring variable is a subterm of the whole instance. -/
theorem VarOccurs.subterm_apply {x : nu} {t : Term sigma nu}
    (h : VarOccurs x t) (s : Subst sigma nu) :
    Subterm (s x) (Subst.apply s t) := by
  induction h with
  | here => exact Subterm.refl _
  | @arg f args a ha _ ih =>
      have hmem : Subst.apply s a ∈ Subst.applyList s args := by
        rw [Subst.applyList_eq_map]
        exact List.mem_map_of_mem ha
      exact Subterm.arg hmem ih

/-- Substitutions agreeing on every occurring variable agree on the term. The
occurrence-based twin of `apply_eq_of_agree`. -/
theorem apply_eq_of_occurs_agree {s s' : Subst sigma nu} :
    ∀ (t : Term sigma nu), (∀ x, VarOccurs x t → s x = s' x) →
      Subst.apply s t = Subst.apply s' t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro h; exact h x VarOccurs.here
  | happ f args ih =>
      intro h
      simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq, true_and]
      exact List.map_congr_left
        (fun a ha => ih a ha (fun x hx => h x (VarOccurs.arg ha hx)))

/-! ## Renaming lemmas -/

/-- Renaming along the identity is the identity. -/
theorem mapVar_id : ∀ t : Term sigma nu, Term.mapVar (fun v => v) t = t := by
  intro t
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      simp only [Term.mapVar_app, Term.mapVarList_eq_map]
      congr 1
      exact (List.map_congr_left ih).trans (List.map_id'' (fun _ => rfl) ..)

/-- Substitution after renaming is substitution along the composite. -/
theorem apply_mapVar (s : Subst sigma nu) (rho : nu → nu) :
    ∀ t : Term sigma nu,
      Subst.apply s (Term.mapVar rho t) = Subst.apply (fun v => s (rho v)) t := by
  intro t
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      simp only [Term.mapVar_app, Subst.apply_app, Subst.applyList_eq_map,
        Term.mapVarList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-- A renaming fixing every occurring variable fixes the term. -/
theorem mapVar_id_on {rho : nu → nu} :
    ∀ t : Term sigma nu, (∀ x, VarOccurs x t → rho x = x) →
      Term.mapVar rho t = t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro h; simp [h x VarOccurs.here]
  | happ f args ih =>
      intro h
      simp only [Term.mapVar_app, Term.mapVarList_eq_map]
      congr 1
      refine (List.map_congr_left
        (fun a ha => ih a ha (fun x hx => h x (VarOccurs.arg ha hx)))).trans
        (List.map_id'' (fun _ => rfl) ..)

/-! ## The specification -/

/-- **The hub linearization specification.** `crule` linearizes `rule` when the
right-hand side is kept verbatim and a collapse map `rho` exists with: the
conditional left-hand side collapses to the original one; every condition is a
hub pair of variables occurring in the conditional left-hand side; every
variable occurring in that left-hand side is fixed by `rho` or has its hub pair
among the conditions; and `rho` fixes every variable of the right-hand side.

Section 11.3 of the roadmap records which clause each part of the transfer
proof consumes. -/
def LinearizesRule (rule : Rule sigma nu) (crule : CRule sigma nu) : Prop :=
  crule.rhs = rule.rhs ∧
  ∃ rho : nu → nu,
    Term.mapVar rho crule.lhs = rule.lhs ∧
    (∀ p ∈ crule.conds, ∃ x y : nu,
        p = (Term.var x, Term.var y) ∧ rho x = x ∧ rho y = x ∧
        VarOccurs x crule.lhs ∧ VarOccurs y crule.lhs) ∧
    (∀ v : nu, VarOccurs v crule.lhs →
        rho v = v ∨ (Term.var (rho v), Term.var v) ∈ crule.conds) ∧
    (∀ v : nu, VarOccurs v crule.rhs → rho v = v)

/-- `C` is a conditional linearization of `R`: the two rule lists correspond
rule by rule in both directions. -/
def IsLinearization (R : TRS sigma nu) (C : CTRS sigma nu) : Prop :=
  (∀ crule ∈ C, ∃ rule ∈ R, LinearizesRule rule crule) ∧
  (∀ rule ∈ R, ∃ crule ∈ C, LinearizesRule rule crule)

/-- Variable occurrences listed with multiplicity. Unlike `Term.vars`, this list
retains repeated occurrences and can therefore state genuine left-linearity. -/
def Term.varOccurrences : Term sigma nu → List nu
  | .var x => [x]
  | .app _ args => args.flatMap Term.varOccurrences

/-- A finite first-order term is left-linear when no variable occurs twice. -/
def Term.LeftLinear (t : Term sigma nu) : Prop :=
  (OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences t).Nodup

/-- Method-faithful linearization witness. `LinearizesRule` is the transfer
specification consumed by the proof; this structure adds the defining
left-linearity requirement of the named conditional-linearization method. -/
structure MethodLinearizesRule (rule : Rule sigma nu) (crule : CRule sigma nu) : Prop where
  transfer : LinearizesRule rule crule
  leftLinear : OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear crule.lhs

/-- Exact named-method layer: every conditional rule is a left-linearized image
of an original rule and every original rule has such an image. -/
def IsMethodLinearization (R : TRS sigma nu) (C : CTRS sigma nu) : Prop :=
  (∀ crule ∈ C, ∃ rule ∈ R, MethodLinearizesRule rule crule) ∧
  (∀ rule ∈ R, ∃ crule ∈ C, MethodLinearizesRule rule crule)

/-- Forgetting method identity gives the weaker transfer specification used by
the transfer proof. -/
theorem IsMethodLinearization.toIsLinearization
    {R : TRS sigma nu} {C : CTRS sigma nu}
    (h : IsMethodLinearization R C) : IsLinearization R C := by
  constructor
  · intro crule hc
    rcases h.1 crule hc with ⟨rule, hr, hw⟩
    exact ⟨rule, hr, hw.transfer⟩
  · intro rule hr
    rcases h.2 rule hr with ⟨crule, hc, hw⟩
    exact ⟨crule, hc, hw.transfer⟩

/-! ## The two instance helpers -/

/-- A rule is its own linearization with empty conditions, through the identity
collapse. Sound for every rule, useful only for rules whose left-hand side is
genuinely linear: on a non-linear rule this pairing produces a conditional
system whose steps are the original steps, which defeats the transform's
purpose. -/
theorem linearizesRule_self (rule : Rule sigma nu) :
    LinearizesRule rule ⟨rule.lhs, rule.rhs, [], rule.lhs_isApp⟩ := by
  refine ⟨rfl, fun v => v, mapVar_id _, ?_, ?_, ?_⟩
  · intro p hp; cases hp
  · intro v _; exact Or.inl rfl
  · intro v _; rfl

/-- The binary diagonal `f(x, x) -> rhs` linearizes to
`f(x, y) -> rhs` under the condition `x ~ y`, through the collapse sending `y`
to `x`. The only hypothesis is that `y` misses the right-hand side; `x ≠ y` is
never needed, because `if x = y then x else x` is `x` either way. -/
theorem linearizesRule_binaryDiagonal [DecidableEq nu] (f : sigma) (x y : nu)
    (rhs : Term sigma nu) (hy : ¬ VarOccurs y rhs) :
    LinearizesRule
      ⟨.app f [.var x, .var x], rhs, rfl⟩
      ⟨.app f [.var x, .var y], rhs, [(.var x, .var y)], rfl⟩ := by
  refine ⟨rfl, fun v => if v = y then x else v, ?_, ?_, ?_, ?_⟩
  · -- collapse: the renamed left-hand side is the diagonal one
    simp only [Term.mapVar_app, Term.mapVarList_cons, Term.mapVarList_nil,
      Term.mapVar_var, Term.app.injEq, List.cons.injEq, and_true, true_and]
    constructor
    · by_cases hxy : x = y <;> simp [hxy]
    · simp
  · -- the single condition is the hub pair, both variables occurring
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    refine ⟨x, y, rfl, ?_, by simp, ?_, ?_⟩
    · by_cases hxy : x = y <;> simp [hxy]
    · exact VarOccurs.arg (List.Mem.head _) VarOccurs.here
    · exact VarOccurs.arg (List.Mem.tail _ (List.Mem.head _)) VarOccurs.here
  · -- every occurring variable is fixed or has its hub pair listed
    intro v hv
    rcases hv.app_inv with ⟨a, ha, hva⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · cases hva
      left
      by_cases hxy : x = y <;> simp [hxy]
    · cases hva
      by_cases hxy : y = x
      · left; simp [hxy]
      · right
        simp
  · -- the collapse fixes the right-hand side
    intro v hv
    have : v ≠ y := fun h => hy (h ▸ hv)
    simp [this]

/-! ## Non-vacuity: the diagonal rule of the conditional example

The rule `f(x, x) -> a` linearizes to the conditional rule `crF` of
`ConditionalTRS.lean`, whose target is the verbatim right-hand side `a`. This is
the in-file exhibit for the campaign's named error class: the transform changes
the left-hand side and adds a condition, and the target stays the original
right-hand side. -/

namespace CondExample

/-- `f(x, x) -> a` over the example signature (`f = 2`, `a = 3`). -/
def diagRule : Rule Nat Nat := ⟨.app 2 [.var 0, .var 0], .app 3 [], rfl⟩

/-- The diagonal rule linearizes to the conditional rule `crF`. -/
theorem diagRule_linearizes : LinearizesRule diagRule crF :=
  linearizesRule_binaryDiagonal 2 0 1 (.app 3 []) (fun h => by cases h.app_inv.choose_spec.1)

end CondExample

/-- A genuinely linear rule is a method-faithful trivial linearization of itself. -/
theorem methodLinearizesRule_self (rule : Rule sigma nu)
    (hlin : OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear rule.lhs) :
    MethodLinearizesRule rule ⟨rule.lhs, rule.rhs, [], rule.lhs_isApp⟩ :=
  ⟨linearizesRule_self rule, hlin⟩

/-- The split binary diagonal left-hand side is left-linear exactly when the two
variable names are distinct. -/
theorem leftLinear_binarySplit [DecidableEq nu] (f : sigma) (x y : nu)
    (hxy : x ≠ y) :
    OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear
      (Term.app f [Term.var x, Term.var y]) := by
  simp [OperatorKO7.Meta.UniqueNormalization.Term.LeftLinear,
    OperatorKO7.Meta.UniqueNormalization.Term.varOccurrences, hxy]

/-- Method-faithful binary-diagonal linearization. The extra `x ≠ y` premise is
not cosmetic: without it the transformed LHS still repeats one variable and is
not left-linear. -/
theorem methodLinearizesRule_binaryDiagonal [DecidableEq nu]
    (f : sigma) (x y : nu) (rhs : Term sigma nu)
    (hxy : x ≠ y) (hy : ¬ VarOccurs y rhs) :
    MethodLinearizesRule
      ⟨Term.app f [Term.var x, Term.var x], rhs, rfl⟩
      ⟨Term.app f [Term.var x, Term.var y], rhs,
        [(Term.var x, Term.var y)], rfl⟩ :=
  ⟨linearizesRule_binaryDiagonal f x y rhs hy,
    leftLinear_binarySplit f x y hxy⟩

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.VarOccurs
#check @OperatorKO7.Meta.UniqueNormalization.LinearizesRule
#check @OperatorKO7.Meta.UniqueNormalization.IsLinearization

#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs.size_apply_le
#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs.size_apply_lt_of_isApp
#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs.subterm_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.apply_eq_of_occurs_agree
#print axioms OperatorKO7.Meta.UniqueNormalization.mapVar_id
#print axioms OperatorKO7.Meta.UniqueNormalization.apply_mapVar
#print axioms OperatorKO7.Meta.UniqueNormalization.mapVar_id_on
#print axioms OperatorKO7.Meta.UniqueNormalization.linearizesRule_self
#print axioms OperatorKO7.Meta.UniqueNormalization.linearizesRule_binaryDiagonal
#print axioms OperatorKO7.Meta.UniqueNormalization.CondExample.diagRule_linearizes

#check @OperatorKO7.Meta.UniqueNormalization.VarOccurs.app_inv
#check @OperatorKO7.Meta.UniqueNormalization.CondExample.diagRule
#check @OperatorKO7.Meta.UniqueNormalization.CondExample.diagRule_linearizes

#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs
#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs.app_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.LinearizesRule
#print axioms OperatorKO7.Meta.UniqueNormalization.IsLinearization
#print axioms OperatorKO7.Meta.UniqueNormalization.CondExample.diagRule
