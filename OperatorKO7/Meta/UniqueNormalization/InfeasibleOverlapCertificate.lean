import OperatorKO7.Meta.UniqueNormalization.SemiEquationalConfluence

/-!
# Certified Infeasible Overlaps via Invariant Models

Campaign: RTA open problem #79, route R2 (conditional linearization).
Reference: Audit/worktree-lean-publication-audit/klop-status-assessment.md (Roadmap 2026-09-12).

An equational interpretation into an algebra M in which every rule of R is an identity
preserves conversion:
  s conv R t ==> eval M s = eval M t
Through the transfer theorem cconv_iff_conv, this invariant transfers to conditional
linearizations:
  s cconv C t ==> eval M s = eval M t
When an overlap between two conditional rules forces equality of condition terms whose
evaluations in M are distinct, the overlap is infeasible. This provides an exact,
compositional certificate format that refutes impossible overlaps without requiring
global transitivity or well-founded proof-tree measures.

Trust: kernel checked; no sorry, admit, axiom, native_decide, partial, unsafe or opaque.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v w

variable {sigma : Type u} {nu : Type v}

/-- An algebraic interpretation of a signature sigma on carrier M. -/
structure Model (sigma : Type u) (M : Type w) where
  app : sigma → List M → M

/-- Evaluation of a term in an algebraic model under a variable assignment. -/
def evalInModel {sigma : Type u} {nu : Type v} {M : Type w}
    (model : Model sigma M) (assign : nu → M) : Term sigma nu → M
  | .var x => assign x
  | .app f args => model.app f (args.map (evalInModel model assign))

@[simp] theorem evalInModel_var {sigma : Type u} {nu : Type v} {M : Type w}
    (model : Model sigma M) (assign : nu → M) (x : nu) :
    evalInModel model assign (.var x) = assign x := by
  rw [evalInModel]

@[simp] theorem evalInModel_app {sigma : Type u} {nu : Type v} {M : Type w}
    (model : Model sigma M) (assign : nu → M) (f : sigma) (args : List (Term sigma nu)) :
    evalInModel model assign (.app f args) =
      model.app f (args.map (evalInModel model assign)) := by
  rw [evalInModel]

/-- An assignment after substitution is evaluation of the substitution terms. -/
theorem evalInModel_apply {sigma : Type u} {nu : Type v} {M : Type w}
    (model : Model sigma M) (assign : nu → M) (σ : Subst sigma nu) (t : Term sigma nu) :
    evalInModel model assign (Subst.apply σ t) =
      evalInModel model (fun x => evalInModel model assign (σ x)) t := by
  induction t using Term.rec' with
  | hvar x => simp only [Subst.apply_var, evalInModel_var]
  | happ f args ih =>
      simp only [Subst.apply_app, evalInModel_app, Subst.applyList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-- A rule is valid in a model if its left and right sides evaluate identically
under all variable assignments. -/
def RuleValidInModel {sigma : Type u} {nu : Type v} {M : Type w}
    (model : Model sigma M) (r : Rule sigma nu) : Prop :=
  ∀ assign : nu → M, evalInModel model assign r.lhs = evalInModel model assign r.rhs

/-- A TRS is valid in a model if every rule is valid. -/
def TRSValidInModel {sigma : Type u} {nu : Type v} {M : Type w}
    (model : Model sigma M) (R : TRS sigma nu) : Prop :=
  ∀ r ∈ R, RuleValidInModel model r

/-- Validity in a model is preserved under reduction steps. -/
theorem evalInModel_step {sigma : Type u} {nu : Type v} {M : Type w}
    {model : Model sigma M} {R : TRS sigma nu} (hvalid : TRSValidInModel model R)
    {s t : Term sigma nu} (hstep : Step R s t) :
    ∀ assign : nu → M, evalInModel model assign s = evalInModel model assign t := by
  intro assign
  induction hstep with
  | root hr =>
      obtain ⟨rule, hmem, σ, hs, ht⟩ := hr
      subst hs; subst ht
      rw [evalInModel_apply, evalInModel_apply]
      exact hvalid rule hmem (fun x => evalInModel model assign (σ x))
  | arg f pre post _ ih =>
      simp only [evalInModel_app, List.map_append, List.map_cons]
      rw [ih]

/-- Validity in a model is preserved under conversion. -/
theorem evalInModel_conv {sigma : Type u} {nu : Type v} {M : Type w}
    {model : Model sigma M} {R : TRS sigma nu} (hvalid : TRSValidInModel model R)
    {s t : Term sigma nu} (hconv : conv R s t) :
    ∀ assign : nu → M, evalInModel model assign s = evalInModel model assign t := by
  intro assign
  induction hconv with
  | refl => rfl
  | tail _ hlast ih =>
      rcases hlast with hstep | hstep
      · exact ih.trans (evalInModel_step hvalid hstep assign)
      · exact ih.trans (evalInModel_step hvalid hstep assign).symm

/-- An invariant model for a system R transfers to any conditional linearization C. -/
theorem evalInModel_cconv {sigma : Type u} {nu : Type v} {M : Type w}
    {model : Model sigma M} {R : TRS sigma nu} {C : CTRS sigma nu}
    (hlin : IsLinearization R C) (hvalid : TRSValidInModel model R)
    {s t : Term sigma nu} (hcconv : cconv C s t) :
    ∀ assign : nu → M, evalInModel model assign s = evalInModel model assign t := by
  intro assign
  have hconv : conv R s t := (cconv_iff_conv hlin s t).mp hcconv
  exact evalInModel_conv hvalid hconv assign

/-- **The General Infeasible Overlap Certificate.** If an overlap between two rules of a
linearization C forces conditions whose evaluations in an invariant model are distinct,
that overlap cannot be feasible in the conversion of C. -/
theorem no_feasible_overlap_of_model {sigma : Type u} {nu : Type v} {M : Type w}
    (model : Model sigma M) (R : TRS sigma nu) (C : CTRS sigma nu)
    (hlin : IsLinearization R C) (hvalid : TRSValidInModel model R)
    (hcert : ∀ r₁ ∈ C, ∀ r₂ ∈ C, ∀ q : Term sigma nu, Subterm q r₁.lhs → q.isApp = true →
      ∀ σ₁ σ₂ : Subst sigma nu, Subst.apply σ₁ q = Subst.apply σ₂ r₂.lhs →
        (∀ p ∈ r₁.conds, ∀ assign, evalInModel model assign (Subst.apply σ₁ p.1) =
          evalInModel model assign (Subst.apply σ₁ p.2)) →
        (∀ p ∈ r₂.conds, ∀ assign, evalInModel model assign (Subst.apply σ₂ p.1) =
          evalInModel model assign (Subst.apply σ₂ p.2)) →
        r₁ = r₂ ∧ q = r₁.lhs) :
    NoFeasibleOverlap C (cconv C) := by
  intro r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq hc₁ hc₂
  refine hcert r₁ h₁ r₂ h₂ q hq happ σ₁ σ₂ heq ?_ ?_
  · intro p hp assign
    exact evalInModel_cconv hlin hvalid (hc₁ p hp) assign
  · intro p hp assign
    exact evalInModel_cconv hlin hvalid (hc₂ p hp) assign

end OperatorKO7.Meta.UniqueNormalization
