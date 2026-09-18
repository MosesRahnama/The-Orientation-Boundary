import OperatorKO7.Meta.Rewriting.Rewrite

/-!
# Unique normal forms: the statement layer for RTA open problem #79

Campaign: `KO7-LLM-Benchmark\Distinction_Boundary\Roadmaps\klop\ROADMAP.md`, WP-K1.
Definition freeze: `Roadmaps\klop\definitions.md` (D2, D3, D15).

This module fixes the vocabulary in which RTA open problem #79 is stated, over
the generic first-order carrier of `Meta\Rewriting\Rewrite.lean`:

* `conv`, conversion (the equivalence closure of one-step rewriting);
* `NormalForm`, and the three uniqueness properties `UNconv` (UN=), `UNred`
  (UN->), and `NFP` (the normal form property);
* `Consistent`, the CON property;
* the implications between them, each direction proved. No non-implication is
  claimed here.

## Fidelity block (frozen `definitions.md`, D2)

> "We say that a relation R on Ter(Sigma, X) is consistent if for all x, y in X,
> x R y implies x = y. We say that a TRS is consistent (has the CON property) if
> the congruence closure of root-step is consistent on Ter(Sigma, Y), for an
> infinite set Y."

`Consistent` below quantifies over **variables only**, matching the source
relation once the variable carrier is infinite. This base module deliberately
keeps `nu` arbitrary so its elementary conversion lemmas can be reused on
finite fixtures; the RTA #79 summit supplies `[Infinite nu]` where the paper's
open-term CON theorem needs the infinite variable set. A version quantifying
over all terms would be a different and strictly stronger property, and would
fail for every system with a rewrite step. The congruence closure of the root
step is `conv` here, because `Step` is already the context closure of `rootStep`
(see `Meta\Rewriting\Rewrite.lean`) and `conv` closes it under reflexivity,
symmetry and transitivity.

## Fidelity block (frozen `definitions.md`, D3)

> "Both uniqueness of normal forms (UN) and consistency (CON) can be looked at
> as properties of open terms or ground terms. We stick in this paper to the
> versions on open terms, as these notions are unaffected by signature
> extensions."

Every definition here is parameterized by the open-term carrier `Term sigma nu`.
The generic layer permits any `nu`; source-faithful RTA statements instantiate
an infinite `nu` rather than silently treating a finite or empty variable type
as the paper's open-term universe.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`,
`@[csimp]`, `partial`, `unsafe`, or `opaque`. Axiom footprint reported per
declaration at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting
open scoped Subst

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Inversion for the one-step relation

`Step` is an inductive family whose `arg` constructor writes the argument list
as `pre ++ a :: post`. Because `List.append` is not a constructor, `cases` on a
concrete argument list cannot solve that equation by unification. This lemma
turns the constructor split into a plain disjunction with the list equation
exposed, and every normal-form proof below goes through it. -/
theorem Step.app_inv {R : TRS sigma nu} {f : sigma} {args : List (Term sigma nu)}
    {u : Term sigma nu} (h : Step R (.app f args) u) :
    rootStep R (.app f args) u ∨
      ∃ (pre post : List (Term sigma nu)) (a b : Term sigma nu),
        args = pre ++ a :: post ∧ u = .app f (pre ++ b :: post) ∧ Step R a b := by
  cases h with
  | root hr => exact Or.inl hr
  | arg g pre post hab => exact Or.inr ⟨pre, post, _, _, rfl, rfl, hab⟩

/-- A variable admits no rewrite step: every rule has an application as its
left-hand side, so no substitution instance of a left-hand side is a variable,
and the `arg` constructor needs an application as its source. -/
theorem Step.not_var {R : TRS sigma nu} {x : nu} {u : Term sigma nu} :
    ¬ Step R (.var x) u := by
  intro h
  cases h with
  | root hr =>
      obtain ⟨rule, _, σ, hsrc, _⟩ := hr
      have hApp := rule.lhs_isApp
      cases hlhs : rule.lhs with
      | var w => rw [hlhs] at hApp; simp at hApp
      | app g gargs =>
          rw [hlhs] at hsrc
          simp only [Subst.apply_app] at hsrc
          exact absurd hsrc (by simp)

/-! ## Conversion -/

/-- One symmetric rewrite step: `s` rewrites to `t` or `t` rewrites to `s`. -/
def convStep (R : TRS sigma nu) (s t : Term sigma nu) : Prop :=
  Step R s t ∨ Step R t s

/-- Conversion: the reflexive-transitive closure of the symmetric one-step
relation, that is the equivalence closure of rewriting. This is the relation
written `=_R` in the literature, and the one RTA open problem #79 is about. -/
def conv (R : TRS sigma nu) : Term sigma nu → Term sigma nu → Prop :=
  Relation.ReflTransGen (convStep R)

theorem convStep_symm {R : TRS sigma nu} {s t : Term sigma nu} (h : convStep R s t) :
    convStep R t s :=
  Or.symm h

@[refl] theorem conv.refl (R : TRS sigma nu) (t : Term sigma nu) : conv R t t :=
  Relation.ReflTransGen.refl

theorem conv.single {R : TRS sigma nu} {s t : Term sigma nu} (h : convStep R s t) :
    conv R s t :=
  Relation.ReflTransGen.single h

/-- A single rewrite step is a conversion. -/
theorem conv.of_step {R : TRS sigma nu} {s t : Term sigma nu} (h : Step R s t) :
    conv R s t :=
  conv.single (Or.inl h)

theorem conv.trans {R : TRS sigma nu} {s t u : Term sigma nu}
    (hst : conv R s t) (htu : conv R t u) : conv R s u :=
  Relation.ReflTransGen.trans hst htu

theorem conv.symm {R : TRS sigma nu} {s t : Term sigma nu} (h : conv R s t) :
    conv R t s := by
  induction h with
  | refl => exact conv.refl R s
  | tail _ hlast ih => exact conv.trans (conv.single (convStep_symm hlast)) ih

/-- A rewrite sequence is a conversion. -/
theorem conv.of_stepStar {R : TRS sigma nu} {s t : Term sigma nu}
    (h : StepStar R s t) : conv R s t := by
  induction h with
  | refl => exact conv.refl R s
  | tail _ hlast ih => exact conv.trans ih (conv.of_step hlast)

/-- Joinable terms are convertible. -/
theorem conv.of_joinable {R : TRS sigma nu} {s t : Term sigma nu}
    (h : joinable R s t) : conv R s t :=
  let ⟨_, hsu, htu⟩ := h
  conv.trans (conv.of_stepStar hsu) (conv.symm (conv.of_stepStar htu))

/-- Conversion lifts through one argument position. -/
theorem conv.arg_congr (R : TRS sigma nu) (f : sigma) (pre post : List (Term sigma nu))
    {a b : Term sigma nu} (h : conv R a b) :
    conv R (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)) := by
  induction h with
  | refl => exact conv.refl R _
  | tail _ hlast ih =>
      refine conv.trans ih (conv.single ?_)
      rcases hlast with hstep | hstep
      · exact Or.inl (Step.arg f pre post hstep)
      · exact Or.inr (Step.arg f pre post hstep)

/-! ## Normal forms -/

/-- A term is a normal form when no rewrite step applies to it. -/
def NormalForm (R : TRS sigma nu) (t : Term sigma nu) : Prop :=
  ∀ u, ¬ Step R t u

/-- Every variable is a normal form. -/
theorem NormalForm.var (R : TRS sigma nu) (x : nu) :
    NormalForm R (Term.var (sigma := sigma) x) :=
  fun _ h => Step.not_var h

/-- A rewrite sequence out of a normal form is trivial. -/
theorem NormalForm.eq_of_stepStar {R : TRS sigma nu} {t u : Term sigma nu}
    (ht : NormalForm R t) (h : StepStar R t u) : t = u := by
  rcases h.cases_head with heq | ⟨c, hstep, _⟩
  · exact heq
  · exact absurd hstep (ht c)

/-! ## The uniqueness properties -/

/-- **UN=**: distinct normal forms are never convertible. This is the property
in RTA open problem #79. -/
def UNconv (R : TRS sigma nu) : Prop :=
  ∀ s t, NormalForm R s → NormalForm R t → conv R s t → s = t

/-- **UN->**: a term has at most one normal form reachable from it. -/
def UNred (R : TRS sigma nu) : Prop :=
  ∀ s t u, NormalForm R t → NormalForm R u → StepStar R s t → StepStar R s u → t = u

/-- **NFP**, the normal form property: a term convertible with a normal form
rewrites to it. -/
def NFP (R : TRS sigma nu) : Prop :=
  ∀ s t, NormalForm R t → conv R s t → StepStar R s t

/-- Confluence: two rewrite sequences out of one term can be brought back
together. -/
def confluent (R : TRS sigma nu) : Prop :=
  ∀ s t₁ t₂, StepStar R s t₁ → StepStar R s t₂ → joinable R t₁ t₂

/-- **CON**: the equational theory is consistent, that is conversion never
relates two distinct variables. Frozen definition D2: consistency constrains
variables only. -/
def Consistent (R : TRS sigma nu) : Prop :=
  ∀ x y : nu, conv R (.var x) (.var y) → x = y

/-! ## The implications -/

/-- UN= implies UN->: a common source makes two normal forms convertible. -/
theorem UNred_of_UNconv {R : TRS sigma nu} (h : UNconv R) : UNred R := by
  intro s t u ht hu hst hsu
  exact h t u ht hu (conv.trans (conv.symm (conv.of_stepStar hst)) (conv.of_stepStar hsu))

/-- The normal form property implies UN=. -/
theorem UNconv_of_NFP {R : TRS sigma nu} (h : NFP R) : UNconv R := by
  intro s t hs ht hconv
  exact hs.eq_of_stepStar (h s t ht hconv)

/-- Under confluence every conversion is a joinability: induction along the
conversion, closing each backward step by confluence. -/
theorem joinable_of_conv {R : TRS sigma nu} (h : confluent R) {a b : Term sigma nu}
    (hab : conv R a b) : joinable R a b := by
  induction hab with
  | refl => exact joinable.refl R a
  | @tail m n _ hmn ih =>
      obtain ⟨w, haw, hmw⟩ := ih
      rcases hmn with hstep | hstep
      · obtain ⟨z, hwz, hnz⟩ := h m w n hmw (StepStar.single hstep)
        exact ⟨z, StepStar.trans haw hwz, hnz⟩
      · exact ⟨w, haw, StepStar.head hstep hmw⟩

/-- Confluence implies the normal form property. -/
theorem NFP_of_confluent {R : TRS sigma nu} (h : confluent R) : NFP R := by
  intro s t ht hconv
  obtain ⟨w, hsw, htw⟩ := joinable_of_conv h hconv
  rw [ht.eq_of_stepStar htw]
  exact hsw

/-- Confluence implies UN=. -/
theorem UNconv_of_confluent {R : TRS sigma nu} (h : confluent R) : UNconv R :=
  UNconv_of_NFP (NFP_of_confluent h)

/-- UN= implies CON. Frozen definition D3: "on open terms UN implies CON". -/
theorem Consistent_of_UNconv {R : TRS sigma nu} (h : UNconv R) : Consistent R := by
  intro x y hxy
  have := h _ _ (NormalForm.var R x) (NormalForm.var R y) hxy
  simpa using this

/-- The contrapositive, in the form the summit argument uses: a system that
relates two distinct variables by conversion fails UN=. -/
theorem not_UNconv_of_not_Consistent {R : TRS sigma nu} (h : ¬ Consistent R) :
    ¬ UNconv R :=
  fun hun => h (Consistent_of_UNconv hun)

/-! ## Non-vacuity: an executable worked example

The one-rule system `f(x) -> g(x)` of `Meta\Rewriting\Rewrite.lean`. Its target
`g(c)` is exhibited as a genuine normal form and the two terms are convertible,
so none of the predicates above is inhabited only vacuously. -/

namespace Example

open OperatorKO7.Meta.Rewriting.Example

/-- No root contraction applies to an application whose root symbol is not `0`,
because the single rule of `demoTRS` has left-hand side `f(x) = app 0 [var 0]`. -/
theorem no_rootStep_of_head_ne {g : Nat} (hg : g ≠ 0) (args : List (Term Nat Nat))
    (u : Term Nat Nat) : ¬ rootStep demoTRS (.app g args) u := by
  rintro ⟨rule, hmem, σ, hsrc, -⟩
  rw [List.mem_singleton.mp hmem] at hsrc
  simp only [demoRule, lhsTerm, Subst.apply_app] at hsrc
  exact hg (by simpa using congrArg (fun t => match t with
    | Term.app s _ => s
    | Term.var _ => 0) hsrc)

/-- The constant `c = app 2 []` is a normal form: no root step applies, and it
has no argument positions. -/
theorem const_normalForm : NormalForm demoTRS (.app 2 []) := by
  intro u hstep
  rcases Step.app_inv hstep with hroot | ⟨pre, post, a, b, hargs, -, -⟩
  · exact no_rootStep_of_head_ne (by decide) [] u hroot
  · exact absurd hargs.symm (by simp)

/-- `g(c)` is a normal form: no root step applies, and its one argument `c` is
itself a normal form. -/
theorem tgt_normalForm : NormalForm demoTRS tgtTerm := by
  intro u hstep
  rcases Step.app_inv hstep with hroot | ⟨pre, post, a, b, hargs, -, hab⟩
  · exact no_rootStep_of_head_ne (by decide) _ u hroot
  · cases pre with
    | cons c cs => simp at hargs
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hargs
        exact const_normalForm b (hargs.1 ▸ hab)

/-- `f(c)` and `g(c)` are convertible. -/
theorem demo_conv : conv demoTRS srcTerm tgtTerm :=
  conv.of_step demo_step

/-- The convertible pair really does reach a normal form: `f(c)` rewrites to the
normal form `g(c)`. -/
theorem demo_normalizes : StepStar demoTRS srcTerm tgtTerm ∧ NormalForm demoTRS tgtTerm :=
  ⟨demo_stepStar, tgt_normalForm⟩

end Example

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.Step.app_inv
#check @OperatorKO7.Meta.UniqueNormalization.Step.not_var
#check @OperatorKO7.Meta.UniqueNormalization.convStep
#check @OperatorKO7.Meta.UniqueNormalization.conv
#check @OperatorKO7.Meta.UniqueNormalization.NormalForm
#check @OperatorKO7.Meta.UniqueNormalization.UNconv
#check @OperatorKO7.Meta.UniqueNormalization.UNred
#check @OperatorKO7.Meta.UniqueNormalization.NFP
#check @OperatorKO7.Meta.UniqueNormalization.confluent
#check @OperatorKO7.Meta.UniqueNormalization.Consistent

#print axioms OperatorKO7.Meta.UniqueNormalization.Step.app_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.Step.not_var
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.arg_congr
#print axioms OperatorKO7.Meta.UniqueNormalization.NormalForm.eq_of_stepStar
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_NFP
#print axioms OperatorKO7.Meta.UniqueNormalization.joinable_of_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.NFP_of_confluent
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_confluent
#print axioms OperatorKO7.Meta.UniqueNormalization.Consistent_of_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.not_UNconv_of_not_Consistent
#print axioms OperatorKO7.Meta.UniqueNormalization.Example.const_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.Example.tgt_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.Example.demo_conv
#print axioms OperatorKO7.Meta.UniqueNormalization.Example.demo_normalizes
