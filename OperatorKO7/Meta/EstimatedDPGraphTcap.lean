import OperatorKO7.Meta.DependencyPairs_FirstOrderExtraction

/-!
# Estimated Dependency-Pair Graph via TCAP (over-approximation soundness)

Roadmap source: the estimated-DP-graph-TCAP row of
`OperatorKO7/Expansion/RDRS_Termination_Methods_Roadmap.md`, the
first-order DP-extraction term model in
`Meta/DependencyPairs_FirstOrderExtraction.lean`
(`OperatorKO7.DependencyPairsFragment.FOTerm` / `FORule`), Paper A's DP
treatment, and the standard TCAP (top-symbol cap) approximation.

`tcap` replaces every variable and every defined-rooted subterm (a position that
could be contracted at its root) by a hole; a hole matches anything. The
estimated DP-graph edge `s -> t` holds iff `tcap (rhs s)` is matchable with
`lhs t` (they have a common instance). The **real** edge holds iff some instance
of `rhs s` rewrites to some instance of `lhs t`.

The headline `estimated_dp_graph_tcap_unconditional` proves, **unconditionally**,
that the estimate **over-approximates** the real graph: every real edge is an
estimated edge. So the absence of an estimated edge is a genuine certificate
that no real chain step connects the two pairs.

The proof reduces to the core lemma `capMatches_tcap_of_rstar` (`tcap p` matches
every reduct of every instance of `p`), by induction on `->*`, using the
invariant that every non-hole `tcap` node carries a non-defined head, so any
redex contracted during the reduction sits under a hole.

This is a self-contained first-order term model (`FOTm`, the List-based
first-order syntax mirroring the DP-extraction `FOTerm`), with a custom
induction principle `FOTm.rec'`. Trust: kernel-only; baseline-only under
`#print axioms`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.EstimatedDPGraphTcap

/-! ## 1. First-order terms (List-based), substitution, custom induction -/

/-- First-order term: a variable (`Nat` index) or a symbol (`Nat`) applied to a
list of argument terms. Mirrors the DP-extraction `FOTerm` syntax. -/
inductive FOTm where
  | var (x : Nat)
  | app (f : Nat) (args : List FOTm)

namespace FOTm

/-- Custom induction principle giving, in the `app` case, the hypothesis on every
argument in the list. -/
@[elab_as_elim]
def rec' {motive : FOTm → Prop}
    (hvar : ∀ x, motive (.var x))
    (happ : ∀ f args, (∀ a ∈ args, motive a) → motive (.app f args)) :
    ∀ t, motive t
  | .var x => hvar x
  | .app f args => happ f args (fun a ha =>
      have _hmem : a ∈ args := ha
      rec' hvar happ a)
  termination_by t => sizeOf t
  decreasing_by
    · exact List.sizeOf_lt_of_mem ha |>.trans_le (by
        simp only [FOTm.app.sizeOf_spec]; omega)

/-- Root symbol of a term, when it is an application. -/
def head : FOTm → Option Nat
  | .var _ => none
  | .app f _ => some f

end FOTm

mutual
/-- Apply a substitution. -/
def applySubst (θ : Nat → FOTm) : FOTm → FOTm
  | .var x => θ x
  | .app f args => .app f (applySubstList θ args)
/-- Substitution lifted over an argument list. -/
def applySubstList (θ : Nat → FOTm) : List FOTm → List FOTm
  | [] => []
  | a :: as => applySubst θ a :: applySubstList θ as
end

@[simp] theorem applySubst_var (θ x) : applySubst θ (.var x) = θ x := rfl
@[simp] theorem applySubst_app (θ f args) :
    applySubst θ (.app f args) = .app f (applySubstList θ args) := rfl
@[simp] theorem applySubstList_nil (θ) : applySubstList θ [] = [] := rfl
@[simp] theorem applySubstList_cons (θ a as) :
    applySubstList θ (a :: as) = applySubst θ a :: applySubstList θ as := rfl

/-! ## 2. Rewriting -/

/-- First-order rewrite rule. -/
structure Rule where
  lhs : FOTm
  rhs : FOTm

/-- Defined symbols: the left-hand-side root symbols of the rule list. -/
def definedB (R : List Rule) (f : Nat) : Bool :=
  R.any (fun r => FOTm.head r.lhs == some f)

/-- One congruence-closed rewrite step: a root contraction of a rule instance, or
a step in exactly one argument position. -/
inductive Rstep (R : List Rule) : FOTm → FOTm → Prop
  | root (r : Rule) (hr : r ∈ R) (θ : Nat → FOTm) :
      Rstep R (applySubst θ r.lhs) (applySubst θ r.rhs)
  | arg (f : Nat) (pre post : List FOTm) (a b : FOTm) :
      Rstep R a b →
      Rstep R (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

/-- Reflexive-transitive closure, extended at the tail (source fixed). -/
inductive Rstar (R : List Rule) : FOTm → FOTm → Prop
  | refl (t : FOTm) : Rstar R t t
  | tail {t u v : FOTm} : Rstar R t u → Rstep R u v → Rstar R t v

/-! ## 3. Cap terms, TCAP, matching, invariant -/

/-- A cap term: hole (matches anything) or a node over cap terms. -/
inductive Cap where
  | hole
  | node (f : Nat) (args : List Cap)

mutual
/-- TCAP: cap variables and defined-rooted applications with a hole; keep
non-defined-rooted structure. -/
def tcap (R : List Rule) : FOTm → Cap
  | .var _ => .hole
  | .app f args => if definedB R f then .hole else .node f (tcapList R args)
/-- TCAP over an argument list. -/
def tcapList (R : List Rule) : List FOTm → List Cap
  | [] => []
  | a :: as => tcap R a :: tcapList R as
end

@[simp] theorem tcap_var (R x) : tcap R (.var x) = .hole := rfl
@[simp] theorem tcap_app (R f args) :
    tcap R (.app f args) =
      (if definedB R f then .hole else .node f (tcapList R args)) := rfl
@[simp] theorem tcapList_nil (R) : tcapList R [] = [] := rfl
@[simp] theorem tcapList_cons (R a as) :
    tcapList R (a :: as) = tcap R a :: tcapList R as := rfl

/-- Cap matching: holes match anything; nodes match same-head applications
argument-wise. -/
inductive CapMatches : Cap → FOTm → Prop
  | hole (t : FOTm) : CapMatches Cap.hole t
  | node (f : Nat) (cargs : List Cap) (targs : List FOTm) :
      List.Forall₂ CapMatches cargs targs →
      CapMatches (Cap.node f cargs) (FOTm.app f targs)

/-- Invariant of `tcap` outputs: every non-hole node carries a non-defined head. -/
inductive CapInv (R : List Rule) : Cap → Prop
  | hole : CapInv R Cap.hole
  | node (f : Nat) (cargs : List Cap) :
      definedB R f = false → (∀ c ∈ cargs, CapInv R c) →
      CapInv R (Cap.node f cargs)

/-! ## 4. Core lemmas -/

/-- `tcap` outputs satisfy the non-defined-head invariant. -/
theorem capInv_tcap (R : List Rule) (t : FOTm) : CapInv R (tcap R t) := by
  induction t using FOTm.rec' with
  | hvar x => simpa using CapInv.hole
  | happ f args ih =>
      simp only [tcap_app]
      by_cases hf : definedB R f = true
      · simp [hf]
        exact CapInv.hole
      · simp only [hf, Bool.false_eq_true, if_false]
        refine CapInv.node f _ (by simpa using hf) ?_
        intro c hc
        -- c ∈ tcapList R args  ->  c = tcap R a for some a ∈ args
        have : ∃ a ∈ args, c = tcap R a := by
          clear ih hf
          induction args with
          | nil => simp [tcapList] at hc
          | cons a as iha =>
              simp only [tcapList_cons, List.mem_cons] at hc
              rcases hc with h | h
              · exact ⟨a, by simp, h⟩
              · obtain ⟨a', ha', hc'⟩ := iha h
                exact ⟨a', by simp [ha'], hc'⟩
        obtain ⟨a, ha, rfl⟩ := this
        exact ih a ha

/-- A hole matches every term. -/
theorem capMatches_hole (t : FOTm) : CapMatches Cap.hole t := CapMatches.hole t

/-- `tcap p` matches every instance `applySubst θ p`. -/
theorem capMatches_tcap_applySubst (R : List Rule) (θ : Nat → FOTm) (p : FOTm) :
    CapMatches (tcap R p) (applySubst θ p) := by
  induction p using FOTm.rec' with
  | hvar x => simp [tcap, applySubst]; exact CapMatches.hole _
  | happ f args ih =>
      simp only [tcap_app, applySubst_app]
      by_cases hf : definedB R f = true
      · simp [hf]; exact CapMatches.hole _
      · simp only [hf, Bool.false_eq_true, if_false]
        refine CapMatches.node f _ _ ?_
        clear hf
        induction args with
        | nil => simp [tcapList, applySubstList]
        | cons a as iha =>
            simp only [tcapList_cons, applySubstList_cons]
            exact List.Forall₂.cons (ih a (by simp)) (iha (fun x hx => ih x (by simp [hx])))

/-- A `CapInv` cap matching a defined-rooted application must be a hole. -/
theorem capInv_match_defined_hole (R : List Rule)
    {c : Cap} {f : Nat} {args : List FOTm}
    (hinv : CapInv R c) (hm : CapMatches c (FOTm.app f args))
    (hdef : definedB R f = true) : c = Cap.hole := by
  cases hm with
  | hole _ => rfl
  | node g cargs targs _ =>
      cases hinv with
      | node _ _ hg _ =>
          -- node head g = f, but definedB g = false and definedB f = true
          rw [hg] at hdef
          exact absurd hdef (by simp)

/-- Append for `Forall₂`. -/
theorem forall₂_append {α β : Type} {Rel : α → β → Prop}
    {l1 l3 : List α} {l2 l4 : List β}
    (h1 : List.Forall₂ Rel l1 l2) (h2 : List.Forall₂ Rel l3 l4) :
    List.Forall₂ Rel (l1 ++ l3) (l2 ++ l4) := by
  induction h1 with
  | nil => simpa using h2
  | cons hx _ ih => exact List.Forall₂.cons hx ih

/-- Split a `Forall₂` over a list with a distinguished inserted element. -/
theorem forall₂_split {α β : Type} {Rel : α → β → Prop} :
    ∀ {cs : List α} {pre post : List β} {a : β},
      List.Forall₂ Rel cs (pre ++ a :: post) →
      ∃ cpre ca cpost, cs = cpre ++ ca :: cpost ∧
        List.Forall₂ Rel cpre pre ∧ Rel ca a ∧ List.Forall₂ Rel cpost post := by
  intro cs pre
  induction pre generalizing cs with
  | nil =>
      intro post a h
      cases cs with
      | nil => nomatch h
      | cons c cs' =>
          rw [List.nil_append] at h
          cases h with
          | cons hca hrest =>
              exact ⟨[], c, cs', by simp, List.Forall₂.nil, hca, hrest⟩
  | cons p ps ih =>
      intro post a h
      cases cs with
      | nil => nomatch h
      | cons c cs' =>
          rw [List.cons_append] at h
          cases h with
          | cons hcp hrest =>
              obtain ⟨cpre, ca, cpost, hcs, hpre, hca, hpost⟩ := ih hrest
              exact ⟨c :: cpre, ca, cpost, by simp [hcs], List.Forall₂.cons hcp hpre, hca, hpost⟩

/-- **Step closure.** Over a TRS (rules with non-variable left-hand sides), if a
`tcap`-invariant cap matches a term, it also matches every one-step reduct. -/
theorem capMatches_step_closed (R : List Rule)
    (hwf : ∀ r ∈ R, ∃ f args, r.lhs = FOTm.app f args)
    {c : Cap} {u v : FOTm}
    (hinv : CapInv R c) (hm : CapMatches c u) (hstep : Rstep R u v) :
    CapMatches c v := by
  induction hstep generalizing c with
  | root r hr θ =>
      obtain ⟨f, rargs, hlhs⟩ := hwf r hr
      have hu : applySubst θ r.lhs = FOTm.app f (applySubstList θ rargs) := by
        rw [hlhs, applySubst_app]
      have hdef : definedB R f = true := by
        simp only [definedB, List.any_eq_true]
        exact ⟨r, hr, by simp [hlhs, FOTm.head]⟩
      have hc : c = Cap.hole :=
        capInv_match_defined_hole R hinv (hu ▸ hm) hdef
      subst hc
      exact CapMatches.hole _
  | arg f pre post a b hab ih =>
      cases hm with
      | hole _ => exact CapMatches.hole _
      | node f' cargs targs hforall =>
          cases hinv with
          | node _ _ _ hcinv =>
              obtain ⟨cpre, ca, cpost, hcs, hpre, hca, hpost⟩ := forall₂_split hforall
              have hca_inv : CapInv R ca := by
                apply hcinv; rw [hcs]; simp
              have hcb : CapMatches ca b := ih hca_inv hca
              have hff : List.Forall₂ CapMatches cargs (pre ++ b :: post) := by
                rw [hcs]
                exact forall₂_append hpre (List.Forall₂.cons hcb hpost)
              exact CapMatches.node _ _ _ hff

/-- **Core over-approximation.** `tcap p` matches every reduct of every instance
of `p`. -/
theorem capMatches_tcap_of_rstar (R : List Rule)
    (hwf : ∀ r ∈ R, ∃ f args, r.lhs = FOTm.app f args)
    {p u : FOTm} {θ : Nat → FOTm}
    (h : Rstar R (applySubst θ p) u) : CapMatches (tcap R p) u := by
  induction h with
  | refl => exact capMatches_tcap_applySubst R θ p
  | tail _ hstep ih =>
      exact capMatches_step_closed R hwf (capInv_tcap R p) ih hstep

/-! ## 5. The estimated DP graph and its over-approximation soundness -/

/-- A term rewriting system: a finite rule list whose every left-hand side is a
non-variable application (the standard TRS well-formedness condition). -/
structure TRS where
  rules : List Rule
  lhs_app : ∀ r ∈ rules, ∃ f args, r.lhs = FOTm.app f args

/-- The **estimated** DP-graph edge `s -> t`: `tcap (rhs s)` has a common instance
with `lhs t` (i.e. they are matchable / unifiable after capping). -/
def EstEdge (T : TRS) (s t : Rule) : Prop :=
  ∃ u : FOTm, CapMatches (tcap T.rules s.rhs) u ∧ ∃ τ : Nat → FOTm, applySubst τ t.lhs = u

/-- The **real** DP-graph edge `s -> t`: some instance of `rhs s` rewrites to some
instance of `lhs t` (the chain-connectability the DP graph approximates). -/
def RealEdge (T : TRS) (s t : Rule) : Prop :=
  ∃ θ τ : Nat → FOTm, Rstar T.rules (applySubst θ s.rhs) (applySubst τ t.lhs)

/-- **Headline (unconditional over-approximation soundness).** For every TRS, the
TCAP-estimated DP graph over-approximates the real DP graph: every real edge is an
estimated edge. -/
theorem estimated_dp_graph_tcap_unconditional (T : TRS) (s t : Rule)
    (h : RealEdge T s t) : EstEdge T s t := by
  obtain ⟨θ, τ, hred⟩ := h
  exact ⟨applySubst τ t.lhs,
    capMatches_tcap_of_rstar T.rules T.lhs_app hred, τ, rfl⟩

/-- **Termination certificate (contrapositive).** If the estimate has no edge
`s -> t`, then there is genuinely no real chain step connecting them. -/
theorem no_real_edge_of_no_estimated (T : TRS) (s t : Rule)
    (h : ¬ EstEdge T s t) : ¬ RealEdge T s t :=
  fun hreal => h (estimated_dp_graph_tcap_unconditional T s t hreal)

/-- Audit anchor for the estimated-DP-graph TCAP module. -/
def audit_theory_expansion_estimated_dp_graph_tcap_module_anchor : String :=
  "OperatorKO7.Meta.EstimatedDPGraphTcap.estimated_dp_graph_tcap_unconditional"

end OperatorKO7.Meta.EstimatedDPGraphTcap
