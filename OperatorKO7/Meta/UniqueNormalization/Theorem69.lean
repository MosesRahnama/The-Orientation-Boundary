import OperatorKO7.Meta.UniqueNormalization.ConstructorTranslation
import OperatorKO7.Meta.UniqueNormalization.OverlapClasses
import OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation

/-!
# Theorem 69: reducing UN= to consistency

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K1 and WP-K4.
Definition freeze: `Roadmaps\klop\definitions.md` (D15).

## Fidelity block (frozen `definitions.md`, D15, Theorem 69, proof quoted in full)

> "By contradiction. Suppose T = (Sigma, R) were a non-omega-overlapping TRS,
> t, u in Ter(Sigma, X) were normal forms with t =_R u and t /= u. Then they
> remain normal forms in the TRS
> U = (Sigma + X + {F}, R union F(t, x, y) -> x, F(u, x, y) -> y).
> The system U is also non-omega-overlapping, as the new rules do not
> omega-overlap with each other or any old rule. But
> x =_U F(t, x, y) =_U F(u, x, y) =_U y, i.e. U is inconsistent which
> contradicts Theorem 68."

Two separate things happen in that proof, and this module keeps them apart.

**The extension is inconsistent**, proved here outright as
`not_consistent_extended`: the two new rules send the chosen variables to a
common term, so the extension identifies them. This half needs no hypothesis at
all beyond the conversion between `t` and `u`.

**The extension stays inside the class** is the other half, and it carries the
whole content of the theorem. It is where the `Sigma + X` part of the extended
signature does its work. Freezing the variables of `t` and `u` into constants
makes them ground, and only then does "a subterm of `t` unifies with a left-hand
side" collapse into "`t` contains a redex", which the normal-form assumption
forbids. `FreezingNeeded` below is a three-line system showing the claim fails
without that step: `g(x)` is a normal form of `{g(a) -> b}` whose own root
unifies with the rule's left-hand side, so adding `F(g(x), x, y) -> x` produces a
genuine omega-overlap. The freezing is therefore required, and it is a hypothesis
rather than a presentational step.

`UNconv_of_consistency_of_extensions` combines the two, and the section heading
before it records two shapes of statement this reduction must avoid, both of
which are empty.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Monotonicity in the rule set -/

/-- A rewrite step survives adding rules. -/
theorem Step.mono {R R' : TRS sigma nu} (hsub : ∀ r ∈ R, r ∈ R') :
    ∀ {s t : Term sigma nu}, Step R s t → Step R' s t := by
  intro s t h
  induction h with
  | root hr =>
      obtain ⟨rule, hmem, sb, hs, ht⟩ := hr
      exact Step.root ⟨rule, hsub rule hmem, sb, hs, ht⟩
  | arg f pre post _ ih => exact Step.arg f pre post ih

/-- A conversion survives adding rules. -/
theorem conv.mono {R R' : TRS sigma nu} (hsub : ∀ r ∈ R, r ∈ R')
    {s t : Term sigma nu} (h : conv R s t) : conv R' s t := by
  induction h with
  | refl => exact conv.refl _ _
  | tail _ hlast ih =>
      refine conv.trans ih (conv.single ?_)
      rcases hlast with hstep | hstep
      · exact Or.inl (Step.mono hsub hstep)
      · exact Or.inr (Step.mono hsub hstep)

/-! ## The two extension rules -/

/-- `F(t, x, y) -> x`. -/
def extRuleL (F : sigma) (t : Term sigma nu) (x y : nu) : Rule sigma nu where
  lhs := .app F [t, .var x, .var y]
  rhs := .var x
  lhs_isApp := rfl

/-- `F(u, x, y) -> y`. -/
def extRuleR (F : sigma) (u : Term sigma nu) (x y : nu) : Rule sigma nu where
  lhs := .app F [u, .var x, .var y]
  rhs := .var y
  lhs_isApp := rfl

/-- The extended system `U` of Theorem 69, over the same signature: freshness of
`F` is carried as a hypothesis instead of by enlarging the signature. -/
def extendedTRS (R : TRS sigma nu) (F : sigma) (t u : Term sigma nu) (x y : nu) :
    TRS sigma nu :=
  R ++ [extRuleL F t x y, extRuleR F u x y]

theorem mem_extendedTRS {R : TRS sigma nu} {F : sigma} {t u : Term sigma nu} {x y : nu}
    {r : Rule sigma nu} (h : r ∈ R) : r ∈ extendedTRS R F t u x y :=
  List.mem_append_left _ h

/-- `F` heads no application node of `s`. This is the freshness the reduction
needs, and it is exactly what the extended signature of the paper provides. -/
def SymbolAbsent (F : sigma) (s : Term sigma nu) : Prop :=
  ∀ n ∈ appNodes s, n.1 ≠ F

theorem SymbolAbsent.arg {F : sigma} {f : sigma} {args : List (Term sigma nu)}
    (h : SymbolAbsent F (.app f args)) {a : Term sigma nu} (ha : a ∈ args) :
    SymbolAbsent F a := by
  intro n hn
  exact h n (by
    simp only [appNodes_app, List.mem_cons]
    exact Or.inr (mem_appNodesList_of_mem ha hn))

/-! ## Normal forms survive the extension -/

/-- Inside a term that `F` does not head anywhere, the extension has no new
steps: every step of `U` is already a step of `R`. -/
theorem step_of_step_extended (R : TRS sigma nu) (F : sigma) (t u : Term sigma nu)
    (x y : nu) :
    ∀ {s w : Term sigma nu}, Step (extendedTRS R F t u x y) s w →
      SymbolAbsent F s → Step R s w := by
  intro s w h
  induction h with
  | @root s' w' hr =>
      intro hfresh
      obtain ⟨rule, hmem, sb, hs, hw⟩ := hr
      rcases List.mem_append.1 hmem with hold | hnew
      · exact Step.root ⟨rule, hold, sb, hs, hw⟩
      · -- A new rule has root symbol `F`, so `s'` would be headed by `F`.
        exfalso
        have hhead : ∃ args : List (Term sigma nu), s' = .app F args := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
          rcases hnew with rfl | rfl <;>
            exact ⟨_, by rw [hs]; rfl⟩
        obtain ⟨args, rfl⟩ := hhead
        exact hfresh (F, args) (by simp) rfl
  | arg f pre post _ ih =>
      intro hfresh
      exact Step.arg f pre post (ih (hfresh.arg (by simp)))

/-- A normal form of `R` that `F` does not head anywhere stays a normal form in
the extension. This is the paper's "they remain normal forms in the TRS U". -/
theorem normalForm_extended {R : TRS sigma nu} {F : sigma} {t u : Term sigma nu}
    {x y : nu} {s : Term sigma nu} (hnf : NormalForm R s) (hfresh : SymbolAbsent F s) :
    NormalForm (extendedTRS R F t u x y) s :=
  fun w hstep => hnf w (step_of_step_extended R F t u x y hstep hfresh)

/-! ## The extension is inconsistent -/

/-- `F(t, x, y) -> x` in the extension. -/
theorem step_extL (R : TRS sigma nu) (F : sigma) (t u : Term sigma nu) (x y : nu) :
    Step (extendedTRS R F t u x y) (.app F [t, .var x, .var y]) (.var x) :=
  Step.root ⟨extRuleL F t x y,
    List.mem_append_right _ (List.Mem.head _), Subst.id,
    (Subst.id_apply _).symm, (Subst.id_apply _).symm⟩

/-- `F(u, x, y) -> y` in the extension. -/
theorem step_extR (R : TRS sigma nu) (F : sigma) (t u : Term sigma nu) (x y : nu) :
    Step (extendedTRS R F t u x y) (.app F [u, .var x, .var y]) (.var y) :=
  Step.root ⟨extRuleR F u x y,
    List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _)), Subst.id,
    (Subst.id_apply _).symm, (Subst.id_apply _).symm⟩

/-- **The extension identifies the two chosen variables.** Frozen source:
"x =_U F(t, x, y) =_U F(u, x, y) =_U y". -/
theorem conv_var_var (R : TRS sigma nu) (F : sigma) {t u : Term sigma nu}
    (x y : nu) (htu : conv R t u) :
    conv (extendedTRS R F t u x y) (.var x) (.var y) :=
  conv.trans
    (conv.symm (conv.of_step (step_extL R F t u x y)))
    (conv.trans
      (conv.arg_congr _ F [] [.var x, .var y]
        (conv.mono (fun _ h => mem_extendedTRS h) htu))
      (conv.of_step (step_extR R F t u x y)))

/-- The extension is inconsistent whenever the two variables are distinct. -/
theorem not_consistent_extended (R : TRS sigma nu) (F : sigma) {t u : Term sigma nu}
    {x y : nu} (hxy : x ≠ y) (htu : conv R t u) :
    ¬ Consistent (extendedTRS R F t u x y) :=
  fun hcon => hxy (hcon x y (conv_var_var R F x y htu))

/-! ## The reduction -/

/-! ### Two shapes this reduction must avoid

`not_consistent_extended` proves the extension inconsistent outright, from the
conversion alone. Two consequences constrain how Theorem 69 can be stated.

First, a hypothesis of the form `Consistent (extendedTRS R F t u x y)` is
**refuted** by that theorem whenever `t` and `u` are convertible and the two
variables differ. Any statement deriving `t = u` from it is proved from a
contradiction and carries no content.

Second, requiring one symbol to be absent from every normal form is
**unsatisfiable**: the constant `F` is itself a normal form whenever it heads no
rule, and it contains `F`. `symbolAbsent_all_normalForms_false` records that.

The content of Theorem 69 is therefore neither of those. It is that the
**extension stays inside the class**, so a general consistency theorem applies to
it and contradicts the inconsistency above. That is
`UNconv_of_consistency_of_extensions`. -/

/-- No symbol is absent from every normal form: the constant built from it is a
normal form containing it. Stated for any system in which that constant is
irreducible, which holds whenever the symbol heads no rule. -/
theorem symbolAbsent_all_normalForms_false {R : TRS sigma nu} {F : sigma}
    (h : NormalForm R (.app F [])) :
    ¬ ∀ s : Term sigma nu, NormalForm R s → SymbolAbsent F s := by
  intro hall
  exact hall (.app F []) h (F, []) (by simp) rfl

/-- **Theorem 69, in the shape that produces UN=.**

Two inputs, both of them genuine statements about other systems rather than
about the conclusion. `hCON` is Theorem 68: every system inside the class has a
consistent equational theory. `hclass` says each extension built from a pair of
convertible normal forms stays inside the class.

The proof is the paper's, by contradiction: were two distinct normal forms
convertible, the extension would be inside the class and therefore consistent by
`hCON`, while `not_consistent_extended` shows it identifies the two chosen
variables. -/
theorem UNconv_of_consistency_of_extensions {R : TRS sigma nu} {x y : nu}
    (hxy : x ≠ y)
    (hCON : ∀ S : TRS sigma nu,
      NonOmegaOverlapping S → TRS.RhsDetermined S → Consistent S)
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNconv R := by
  intro s t hs ht hconv
  by_contra hne
  obtain ⟨F, hno, hvar⟩ := hclass s t hs ht hconv hne
  exact not_consistent_extended R F hxy hconv (hCON _ hno hvar)

/-- The same two inputs give unique normal forms with respect to reduction. -/
theorem UNred_of_consistency_of_extensions {R : TRS sigma nu} {x y : nu}
    (hxy : x ≠ y)
    (hCON : ∀ S : TRS sigma nu,
      NonOmegaOverlapping S → TRS.RhsDetermined S → Consistent S)
    (hclass : ∀ t u : Term sigma nu, NormalForm R t → NormalForm R u →
      conv R t u → t ≠ u →
      ∃ F : sigma, NonOmegaOverlapping (extendedTRS R F t u x y) ∧
        TRS.RhsDetermined (extendedTRS R F t u x y)) :
    UNred R :=
  UNred_of_UNconv (UNconv_of_consistency_of_extensions hxy hCON hclass)

/-! ## Why the paper freezes the variables too

`{ g(a) -> b }`, with `g = 0`, `a = 1`, `b = 2`. The term `g(x)` is a normal
form, because `a` is a constant and `x` a variable, so `g(x)` is not an instance
of `g(a)`. Yet `g(x)` and `g(a)` unify, hence omega-unify. Adding the Theorem 69
rule `F(g(x), x, y) -> x` therefore places an omega-unifiable pair between a
non-variable subterm of a new left-hand side and an old left-hand side, and the
extension is no longer non-omega-overlapping.

Freezing the variables into constants, the `Sigma + X` half of the paper's
extended signature, is what removes this: a ground normal form's subterm cannot
unify with a left-hand side without being a redex. -/

namespace FreezingNeeded

/-- `g(a) -> b`. -/
def ruleGA : Rule Nat Nat where
  lhs := .app 0 [.app 1 []]
  rhs := .app 2 []
  lhs_isApp := rfl

/-- The one-rule system. -/
def trs : TRS Nat Nat := [ruleGA]

/-- The open normal form `g(x)`. -/
def tGx : Term Nat Nat := .app 0 [.var 0]

/-- `g(x)` is a normal form: it is not an instance of `g(a)`, and its only
argument is a variable. -/
theorem tGx_normalForm : NormalForm trs tGx := by
  intro w hstep
  rcases Step.app_inv hstep with hroot | ⟨pre, post, a, b, hargs, -, hab⟩
  · obtain ⟨rule, hmem, sb, hsrc, -⟩ := hroot
    simp only [trs, List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    simp only [ruleGA, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Term.app.injEq, List.cons.injEq, and_true, true_and] at hsrc
    exact absurd hsrc (by simp)
  · cases pre with
    | cons c cs => simp at hargs
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hargs
        exact Step.not_var (hargs.1 ▸ hab)

/-- `g(x)` unifies with the rule's left-hand side. -/
theorem tGx_unifiable : Unifiable tGx ruleGA.lhs :=
  ⟨fun _ => .app 1 [], fun _ => .app 1 [], rfl⟩

/-- Hence it omega-unifies with it. -/
theorem tGx_omegaUnifiable : OmegaUnifiable tGx ruleGA.lhs :=
  OmegaUnifiable.of_unifiable tGx_unifiable

/-- **The extension of a non-omega-overlapping system by the Theorem 69 rules
need not be non-omega-overlapping when the variables are not frozen.** The new
rule's left-hand side `F(g(x), x, y)` has `g(x)` as a non-variable subterm, and
`g(x)` omega-unifies with the old left-hand side `g(a)`. -/
theorem extension_not_nonOmegaOverlapping :
    ¬ NonOmegaOverlapping (extendedTRS trs 9 tGx tGx 5 6) := by
  intro hno
  have hnew : extRuleL 9 tGx 5 6 ∈ extendedTRS trs 9 tGx tGx 5 6 :=
    List.mem_append_right _ (List.Mem.head _)
  have hold : ruleGA ∈ extendedTRS trs 9 tGx tGx 5 6 :=
    mem_extendedTRS (List.Mem.head _)
  have hsub : Subterm tGx (extRuleL 9 tGx 5 6).lhs :=
    Subterm.arg (List.Mem.head _) (Subterm.refl _)
  obtain ⟨-, heq⟩ := hno _ hnew _ hold tGx hsub rfl tGx_omegaUnifiable
  simp [extRuleL, tGx] at heq

/-- The finding in one statement: an open normal form can omega-unify with a
left-hand side, so the fresh symbol alone does not preserve the class. -/
theorem freezing_step_required :
    NormalForm trs tGx ∧ OmegaUnifiable tGx ruleGA.lhs ∧
      ¬ NonOmegaOverlapping (extendedTRS trs 9 tGx tGx 5 6) :=
  ⟨tGx_normalForm, tGx_omegaUnifiable, extension_not_nonOmegaOverlapping⟩

end FreezingNeeded

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.extendedTRS
#check @OperatorKO7.Meta.UniqueNormalization.SymbolAbsent
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_consistency_of_extensions
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_consistency_of_extensions

#print axioms OperatorKO7.Meta.UniqueNormalization.Step.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.conv.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.step_of_step_extended
#print axioms OperatorKO7.Meta.UniqueNormalization.normalForm_extended
#print axioms OperatorKO7.Meta.UniqueNormalization.conv_var_var
#print axioms OperatorKO7.Meta.UniqueNormalization.not_consistent_extended
#print axioms OperatorKO7.Meta.UniqueNormalization.symbolAbsent_all_normalForms_false
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_consistency_of_extensions
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_consistency_of_extensions
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.tGx_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.extension_not_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.FreezingNeeded.freezing_step_required
