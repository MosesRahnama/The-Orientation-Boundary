import OperatorKO7.Meta.UniqueNormalization.OverlapClasses

/-!
# Common generalisation, the variable condition, and Proposition 21

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K1.
Definition freeze: `Roadmaps\klop\definitions.md` (D8, and the Q5 row).

## Fidelity block (frozen `definitions.md`, D8, Definition 18)

> "Two rewrite rules l_1 -> r_1, l_1, r_1 in Ter(Sigma, X), and l_2 -> r_2,
> l_2, r_2 in Ter(Sigma, Y), have a common generalisation l_3 -> r_3 iff there
> are substitutions sigma_1 : Z -> Ter(Sigma, X), sigma_2 : Z -> Ter(Sigma, Y)
> such that: sigma_1(l_3) = l_1 and sigma_2(l_3) = l_2, and sigma_1(r_3) = r_1
> and sigma_2(r_3) = r_2, all variables in r_3 occur in l_3."

The final clause, "all variables in `r_3` occur in `l_3`", is carried here by
`Term.DeterminedBy`: two substitutions that agree on `l_3` agree on `r_3`. For
first-order terms the two formulations coincide, and the substitution form is
exactly the content Proposition 21's proof uses, so the Lean statement is the
operative one and needs no `DecidableEq` on variables.
`Term.determinedBy_of_vars_subset` proves the frozen wording implies it.

## The scope correction this file establishes

Frozen definition D15 states Theorem 69 as "Non-omega-overlapping TRSs have
unique normal forms", and Q5 records that Kahrs and Smith impose no condition
relating a rule's right-hand side variables to its left-hand side ones. On the
carrier of `Meta\Rewriting\Rewrite.lean`, which also imposes none, that reading
of the theorem is **false**: `FreshRhs` below is a one-rule system, non-omega-
overlapping under convention CC1, whose equational theory identifies every pair
of variables. The rule is `F(x) -> y` with `y` fresh.

The gap is the standard term-rewriting convention Kahrs and Smith defer to when
they write "We assume familiarity with the standard notions of term rewriting":
a rule's right-hand side uses only left-hand side variables. Under that
condition, restated here as `TRS.RhsDetermined`, Proposition 21 goes through and
is proved below. The counterexample shows the condition cannot be dropped, so it
is a genuine hypothesis of Theorem 69 and not a presentational convenience.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Substitution agreement -/

/-- Two substitutions agreeing on every variable of `t` agree on `t`. -/
theorem apply_eq_of_agree [DecidableEq nu] {a b : Subst sigma nu} :
    ∀ (t : Term sigma nu), (∀ x ∈ Term.vars t, a x = b x) →
      Subst.apply a t = Subst.apply b t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro h; exact h x (by simp)
  | happ f args ih =>
      intro h
      simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq, true_and]
      refine List.map_congr_left (fun c hc => ih c hc ?_)
      intro x hx
      exact h x (by simp only [Term.vars_app]; exact Term.mem_varsList_iff.2 ⟨c, hc, hx⟩)

/-- Conversely, substitutions that agree on `t` agree on every variable of `t`. -/
theorem agree_of_apply_eq [DecidableEq nu] {a b : Subst sigma nu} :
    ∀ (t : Term sigma nu), Subst.apply a t = Subst.apply b t →
      ∀ x ∈ Term.vars t, a x = b x := by
  have hmap : ∀ (as : List (Term sigma nu)),
      as.map (Subst.apply a) = as.map (Subst.apply b) →
      ∀ c ∈ as, Subst.apply a c = Subst.apply b c := by
    intro as
    induction as with
    | nil => intro _ c hc; simp at hc
    | cons d ds ih =>
        intro h c hc
        simp only [List.map_cons, List.cons.injEq] at h
        rcases List.mem_cons.1 hc with rfl | hc
        · exact h.1
        · exact ih h.2 c hc
  intro t
  induction t using Term.rec' with
  | hvar x => intro h y hy; simp only [Term.vars_var, Finset.mem_singleton] at hy; subst hy; exact h
  | happ f args ih =>
      intro h x hx
      simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq, true_and] at h
      simp only [Term.vars_app] at hx
      obtain ⟨c, hc, hxc⟩ := Term.mem_varsList_iff.1 hx
      exact ih c hc (hmap args h c hc) x hxc

/-! ## The variable condition -/

/-- `r` is **determined by** `l`: any two substitutions agreeing on `l` agree on
`r`. For first-order terms this is exactly "every variable of `r` occurs in
`l`", and it is the form Proposition 21 consumes. -/
def Term.DeterminedBy (r l : Term sigma nu) : Prop :=
  ∀ a b : Subst sigma nu, Subst.apply a l = Subst.apply b l →
    Subst.apply a r = Subst.apply b r

/-- The frozen wording, "all variables in `r_3` occur in `l_3`", implies
`DeterminedBy`. -/
theorem Term.determinedBy_of_vars_subset [DecidableEq nu] {r l : Term sigma nu}
    (h : ∀ x ∈ Term.vars r, x ∈ Term.vars l) : Term.DeterminedBy r l :=
  fun _a _b hab => apply_eq_of_agree r (fun x hx => agree_of_apply_eq l hab x (h x hx))

/-- On the paper's infinite variable carrier, `DeterminedBy` forces exactly the
usual first-order variable inclusion. If `x` occurred in `r` but not `l`, two
substitutions could agree on `l` and disagree at `x`, contradicting
`DeterminedBy`. -/
theorem Term.vars_subset_of_determinedBy [Infinite nu] [DecidableEq nu]
    {r l : Term sigma nu} (hdet : Term.DeterminedBy r l) :
    ∀ x ∈ Term.vars r, x ∈ Term.vars l := by
  intro x hxr
  by_contra hxl
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({x} : Finset nu)
  have hyx : y ≠ x := by
    simpa only [Finset.mem_singleton, not_false_eq_true] using hy
  let a : Subst sigma nu := Subst.id
  let b : Subst sigma nu := fun z => if z = x then .var y else .var z
  have hl : Subst.apply a l = Subst.apply b l := by
    apply apply_eq_of_agree
    intro z hzl
    have hzx : z ≠ x := by
      intro hzx
      subst z
      exact hxl hzl
    simp [a, b, Subst.id, hzx]
  have hr := hdet a b hl
  have hx := agree_of_apply_eq r hr x hxr
  simp [a, b, Subst.id] at hx
  exact hyx hx.symm

/-- Exact equivalence between the operational `DeterminedBy` formulation and
the source's variable-inclusion wording. -/
theorem Term.determinedBy_iff_vars_subset [Infinite nu] [DecidableEq nu]
    {r l : Term sigma nu} :
    Term.DeterminedBy r l ↔ ∀ x ∈ Term.vars r, x ∈ Term.vars l :=
  ⟨Term.vars_subset_of_determinedBy, Term.determinedBy_of_vars_subset⟩

/-- A rule satisfies the variable condition when its right-hand side is
determined by its left-hand side. -/
def Rule.RhsDetermined (rule : Rule sigma nu) : Prop :=
  Term.DeterminedBy rule.rhs rule.lhs

/-- On an infinite variable carrier, `Rule.RhsDetermined` is literally the
standard first-order side condition `vars(rhs) ⊆ vars(lhs)`. -/
theorem Rule.rhsDetermined_iff_vars_subset [Infinite nu] [DecidableEq nu]
    {rule : Rule sigma nu} :
    Rule.RhsDetermined rule ↔
      ∀ x ∈ Term.vars rule.rhs, x ∈ Term.vars rule.lhs :=
  Term.determinedBy_iff_vars_subset

/-- A TRS satisfies the variable condition when every rule does. This is the
standard convention Kahrs and Smith defer to, and the counterexample at the end
of this file shows Theorem 69 needs it. -/
def TRS.RhsDetermined (R : TRS sigma nu) : Prop :=
  ∀ rule ∈ R, Rule.RhsDetermined rule

/-- The system-level variable condition is exactly RHS-variable inclusion for
every rule. -/
theorem TRS.rhsDetermined_iff_vars_subset [Infinite nu] [DecidableEq nu]
    {R : TRS sigma nu} :
    TRS.RhsDetermined R ↔
      ∀ rule ∈ R, ∀ x ∈ Term.vars rule.rhs, x ∈ Term.vars rule.lhs := by
  constructor
  · intro h rule hr
    exact Rule.rhsDetermined_iff_vars_subset.mp (h rule hr)
  · intro h rule hr
    exact Rule.rhsDetermined_iff_vars_subset.mpr (h rule hr)

/-! ## Common generalisation -/

/-- Frozen definition D8: a common generalisation of two rules. -/
structure CommonGeneralisation (rule₁ rule₂ : Rule sigma nu) where
  /-- The generalised left-hand side. -/
  gl : Term sigma nu
  /-- The generalised right-hand side. -/
  gr : Term sigma nu
  /-- The substitution specialising to the first rule. -/
  s₁ : Subst sigma nu
  /-- The substitution specialising to the second rule. -/
  s₂ : Subst sigma nu
  /-- `s₁` sends the generalised left-hand side to the first rule's. -/
  apply_gl₁ : Subst.apply s₁ gl = rule₁.lhs
  /-- `s₂` sends the generalised left-hand side to the second rule's. -/
  apply_gl₂ : Subst.apply s₂ gl = rule₂.lhs
  /-- `s₁` sends the generalised right-hand side to the first rule's. -/
  apply_gr₁ : Subst.apply s₁ gr = rule₁.rhs
  /-- `s₂` sends the generalised right-hand side to the second rule's. -/
  apply_gr₂ : Subst.apply s₂ gr = rule₂.rhs
  /-- The variable condition of D8: `gr` uses only variables of `gl`. -/
  determined : Term.DeterminedBy gr gl

/-- Every rule satisfying the variable condition is a common generalisation of
itself, with both substitutions the identity. -/
def CommonGeneralisation.self (rule : Rule sigma nu) (h : Rule.RhsDetermined rule) :
    CommonGeneralisation rule rule where
  gl := rule.lhs
  gr := rule.rhs
  s₁ := Subst.id
  s₂ := Subst.id
  apply_gl₁ := Subst.id_apply _
  apply_gl₂ := Subst.id_apply _
  apply_gr₁ := Subst.id_apply _
  apply_gr₂ := Subst.id_apply _
  determined := h

/-- **Two root steps around a common generalisation give the same contractum.**

This is the finitary content of Proposition 21's second half: the paper argues
that a common generalisation turns an omega-unifier of the left-hand sides into
an omega-unifier of the right-hand sides, and for two root steps on one concrete
term the matching substitutions are finite, so the two contracta are equal. -/
theorem rootStep_eq_of_commonGeneralisation {rule₁ rule₂ : Rule sigma nu}
    (cg : CommonGeneralisation rule₁ rule₂) {s t₁ t₂ : Term sigma nu}
    (a b : Subst sigma nu)
    (ha : s = Subst.apply a rule₁.lhs) (hb : s = Subst.apply b rule₂.lhs)
    (ht₁ : t₁ = Subst.apply a rule₁.rhs) (ht₂ : t₂ = Subst.apply b rule₂.rhs) :
    t₁ = t₂ := by
  -- The two composite substitutions agree on the generalised left-hand side.
  have hgl : Subst.apply (Subst.comp a cg.s₁) cg.gl
      = Subst.apply (Subst.comp b cg.s₂) cg.gl := by
    rw [Subst.apply_comp, Subst.apply_comp, cg.apply_gl₁, cg.apply_gl₂, ← ha, ← hb]
  -- Hence, by the variable condition, on the generalised right-hand side.
  have hgr := cg.determined _ _ hgl
  rw [Subst.apply_comp, Subst.apply_comp, cg.apply_gr₁, cg.apply_gr₂] at hgr
  rw [ht₁, ht₂, hgr]

/-! ## Proposition 21 -/

/-- Under the variable condition, a non-omega-overlapping TRS has a
deterministic root step. Two root contractions of one term unify the two
left-hand sides, so convention CC1 forces the same rule, and the variable
condition then forces the same contractum. -/
theorem Deterministic.of_nonOmegaOverlapping {R : TRS sigma nu}
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) : Deterministic R := by
  rintro s t u ⟨rule₁, hmem₁, a, hsa, hta⟩ ⟨rule₂, hmem₂, b, hsb, hub⟩
  have hunif : Unifiable rule₁.lhs rule₂.lhs := ⟨a, b, hsa ▸ hsb ▸ rfl⟩
  obtain ⟨hrule, -⟩ :=
    hno rule₁ hmem₁ rule₂ hmem₂ rule₁.lhs (Subterm.refl _) rule₁.lhs_isApp
      (OmegaUnifiable.of_unifiable hunif)
  subst hrule
  exact rootStep_eq_of_commonGeneralisation
    (CommonGeneralisation.self rule₁ (hvar rule₁ hmem₁)) a b hsa hsb hta hub

/-- **Proposition 21** in the form Theorem 68 consumes: under the variable
condition, every non-omega-overlapping TRS is almost non-omega-overlapping. -/
theorem AlmostNonOmegaOverlapping.of_nonOmegaOverlapping {R : TRS sigma nu}
    (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R) :
    AlmostNonOmegaOverlapping R :=
  ⟨properSubterm_clause_of_nonOmegaOverlapping hno,
    Deterministic.of_nonOmegaOverlapping hno hvar⟩

/-! ## The variable condition is necessary

`F(x) -> y`, one rule, with `y` not occurring in the left-hand side. Symbol `F`
is `0`, the left-hand side variable is `0`, the fresh right-hand side variable is
`1`. -/

namespace FreshRhs

/-- The rule `F(x) -> y`. -/
def rule : Rule Nat Nat where
  lhs := .app 0 [.var 0]
  rhs := .var 1
  lhs_isApp := rfl

/-- The one-rule system. -/
def trs : TRS Nat Nat := [rule]

/-- The only non-variable subterm of `F(x)` is `F(x)` itself. -/
theorem subterm_app_eq {s : Term Nat Nat} (hsub : Subterm s rule.lhs)
    (happ : s.isApp = true) : s = rule.lhs := by
  rcases hsub with _ | ⟨hmem, hsa⟩
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    rw [hsa.eq_of_var] at happ
    simp at happ

/-- The system is non-omega-overlapping under convention CC1: there is one rule,
and the only non-variable subterm of its left-hand side is that left-hand side,
which is the exempt root self-overlap. No unification reasoning is needed. -/
theorem nonOmegaOverlapping : NonOmegaOverlapping trs := by
  intro r₁ h₁ r₂ h₂ s hsub happ _
  simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  subst h₁; subst h₂
  exact ⟨rfl, subterm_app_eq hsub happ⟩

/-- The substitution sending the pattern variable to `F(z)`'s argument slot and
the fresh right-hand side variable to `var k`. -/
def sub (k : Nat) : Subst Nat Nat := fun v => if v = 1 then .var k else .var 7

/-- Each choice of `k` gives a root contraction of one and the same term. -/
theorem step_to_var (k : Nat) : Step trs (.app 0 [.var 7]) (.var k) :=
  Step.root ⟨rule, List.Mem.head _, sub k, rfl, rfl⟩

/-- The system identifies every pair of variables, so it is inconsistent. -/
theorem not_consistent : ¬ Consistent trs := by
  intro hcon
  have h01 : (0 : Nat) = 1 :=
    hcon 0 1 (conv.trans (conv.symm (conv.of_step (step_to_var 0)))
      (conv.of_step (step_to_var 1)))
  omega

/-- The system fails UN=, although it is non-omega-overlapping. -/
theorem not_UNconv : ¬ UNconv trs :=
  not_UNconv_of_not_Consistent not_consistent

/-- What fails is precisely the variable condition. -/
theorem not_rhsDetermined : ¬ TRS.RhsDetermined trs := by
  intro hvar
  have h := hvar rule (List.Mem.head _) (sub 0) (sub 1) rfl
  simp [rule, sub] at h

/-- **The scope correction, in one statement.** Non-omega-overlap alone does not
give UN= on a rule syntax that permits fresh right-hand side variables. The
variable condition of `TRS.RhsDetermined` is therefore a hypothesis of RTA open
problem #79 as much as non-omega-overlap is. -/
theorem variable_condition_necessary :
    NonOmegaOverlapping trs ∧ ¬ TRS.RhsDetermined trs ∧ ¬ UNconv trs ∧ ¬ Consistent trs :=
  ⟨nonOmegaOverlapping, not_rhsDetermined, not_UNconv, not_consistent⟩

end FreshRhs

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.Term.DeterminedBy
#check @OperatorKO7.Meta.UniqueNormalization.Rule.RhsDetermined
#check @OperatorKO7.Meta.UniqueNormalization.TRS.RhsDetermined
#check @OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation
#check @OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation.self

#print axioms OperatorKO7.Meta.UniqueNormalization.apply_eq_of_agree
#print axioms OperatorKO7.Meta.UniqueNormalization.agree_of_apply_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Term.determinedBy_of_vars_subset
#print axioms OperatorKO7.Meta.UniqueNormalization.rootStep_eq_of_commonGeneralisation
#print axioms OperatorKO7.Meta.UniqueNormalization.Deterministic.of_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.AlmostNonOmegaOverlapping.of_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.not_consistent
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.not_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.not_rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.FreshRhs.variable_condition_necessary
