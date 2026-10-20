import OperatorKO7.Meta.UniqueNormalization.RewriteAux
import OperatorKO7.Meta.UniqueNormalization.UNStatement

/-!
# The constructor translation

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K2.
Definition freeze: `Roadmaps\klop\definitions.md` (D7).

Section 3 of Kahrs and Smith: every TRS is translated into a Constructor TRS
over the doubled signature `sigma + sigma`, and consistency is preserved and
reflected. Machine-checked here: Lemma 13, Lemma 14, Proposition 15,
Corollary 16.

## Fidelity block (frozen `definitions.md`, D7, Definitions 9, 10, 11, 12)

> "Given a signature Sigma we write Sigma2 for the coproduct Sigma + Sigma,
> which we view as a constructor signature; the images of Sigma under the
> injections iota_1 and iota_2 give us Sigma_c and Sigma_d, respectively. We
> write F_c and F_d for the function symbols iota_1(F) and iota_2(F),
> respectively. We use the abbreviations floor(t) for T_{iota_1}(t) and
> ceil(t) for T_{iota_2}(t)."

> "Let gamma : Sigma2 -> Sigma be the signature morphism [id, id], i.e.
> gamma(F_c) = F, gamma(F_d) = F. We write |t| for T_gamma(t)."

> "Given a TRS T = (Sigma, R), a pattern is a proper subterm of the left-hand
> side of a rule in R. We write Pat(T) for the set of all patterns of the TRS T."

> "Let T be a TRS with ruleset R and signature Sigma. The constructor
> translation of T is a Constructor TRS T' = (Sigma2, R') built as follows.
> R' = R'_d union R'_c, where
> R'_d = { F_d(floor(t_1), ..., floor(t_n)) -> ceil(r) | F(t_1, ..., t_n) -> r in R }
> and
> R'_c = { F_d(floor(t_1), ..., floor(t_n)) -> F_c(floor(t_1), ..., floor(t_n))
>          | F(t_1, ..., t_n) in Pat(T) }."

Lean names: `constructorLabel` is floor, `destructorLabel` is ceil, `eraseLabel`
is the bars, `destructorPattern` is the left-hand side shape
`F_d(floor(t_1), ..., floor(t_n))` shared by both rule families, `transRule`
builds `R'_d` and `patternRuleOf` builds `R'_c`.

Patterns are carried as the **application nodes** occurring properly inside a
left-hand side, each stored as its symbol together with its argument list. That
is exactly the data `R'_c` needs, and it keeps the rule construction free of
side conditions: `patternRuleOf` never has to prove that a pattern is an
application, because only applications are ever collected.

## Strict source fidelity

Lemma 14's first half is stated in the paper with a transitive-closure arrow,
`ceil(t) ->+ ceil(u)`. This module now proves that strict statement exactly as
`lemma14_forward_strict`. The previously exposed reflexive-transitive form is
retained as the corollary `lemma14_forward` because Proposition 15 and existing
downstream code consume `StepStar`. Thus the mechanization preserves the stronger
source theorem without breaking the established API.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## The doubled signature and its three labellings -/

/-- The label-erasing signature morphism `gamma = [id, id]`. -/
def gammaSym : sigma ⊕ sigma → sigma := Sum.elim id id

/-- `floor(t)`: label every symbol a constructor. -/
def constructorLabel (t : Term sigma nu) : Term (sigma ⊕ sigma) nu :=
  Term.mapSym Sum.inl t

/-- `ceil(t)`: label every symbol a destructor. -/
def destructorLabel (t : Term sigma nu) : Term (sigma ⊕ sigma) nu :=
  Term.mapSym Sum.inr t

/-- `|t|`: erase the labels. -/
def eraseLabel (t : Term (sigma ⊕ sigma) nu) : Term sigma nu :=
  Term.mapSym gammaSym t

@[simp] theorem constructorLabel_app (f : sigma) (args : List (Term sigma nu)) :
    constructorLabel (.app f args) = .app (.inl f) (Term.mapSymList Sum.inl args) := rfl

@[simp] theorem destructorLabel_app (f : sigma) (args : List (Term sigma nu)) :
    destructorLabel (.app f args) = .app (.inr f) (Term.mapSymList Sum.inr args) := rfl

@[simp] theorem constructorLabel_var (x : nu) :
    constructorLabel (sigma := sigma) (.var x) = .var x := rfl

@[simp] theorem destructorLabel_var (x : nu) :
    destructorLabel (sigma := sigma) (.var x) = .var x := rfl

/-- Frozen D7: "Clearly, we have `|ceil(t)| = t = |floor(t)|`". -/
@[simp] theorem eraseLabel_constructorLabel (t : Term sigma nu) :
    eraseLabel (constructorLabel t) = t := by
  rw [eraseLabel, constructorLabel, Term.mapSym_mapSym]
  exact Term.mapSym_id t

/-- The other half of the same identity. -/
@[simp] theorem eraseLabel_destructorLabel (t : Term sigma nu) :
    eraseLabel (destructorLabel t) = t := by
  rw [eraseLabel, destructorLabel, Term.mapSym_mapSym]
  exact Term.mapSym_id t

/-- Erasing a constructor-labelled argument list returns it unchanged. -/
theorem eraseLabelList_constructorLabelList (args : List (Term sigma nu)) :
    Term.mapSymList (gammaSym (sigma := sigma)) (Term.mapSymList Sum.inl args) = args := by
  simp only [Term.mapSymList_eq_map, List.map_map]
  refine (List.map_congr_left (fun a _ => ?_)).trans (List.map_id'' (fun _ => rfl) ..)
  show Term.mapSym gammaSym (Term.mapSym Sum.inl a) = a
  exact eraseLabel_constructorLabel a

/-- Labelling commutes with substitution, constructor side. -/
theorem constructorLabel_apply (s : Subst sigma nu) (t : Term sigma nu) :
    constructorLabel (Subst.apply s t)
      = Subst.apply (Term.mapSubstSym Sum.inl s) (constructorLabel t) :=
  Term.mapSym_apply _ _ _

/-- Labelling commutes with substitution, destructor side. -/
theorem destructorLabel_apply (s : Subst sigma nu) (t : Term sigma nu) :
    destructorLabel (Subst.apply s t)
      = Subst.apply (Term.mapSubstSym Sum.inr s) (destructorLabel t) :=
  Term.mapSym_apply _ _ _

/-- Erasing commutes with substitution. -/
theorem eraseLabel_apply (s : Subst (sigma ⊕ sigma) nu) (t : Term (sigma ⊕ sigma) nu) :
    eraseLabel (Subst.apply s t)
      = Subst.apply (Term.mapSubstSym gammaSym s) (eraseLabel t) :=
  Term.mapSym_apply _ _ _

/-! ## The shared left-hand side shape -/

/-- `F_d(floor(t_1), ..., floor(t_n))`: the root becomes a destructor and every
proper subterm a constructor. Both rule families of the translation use this
shape for their left-hand sides. -/
def destructorPattern : Term sigma nu → Term (sigma ⊕ sigma) nu
  | .var x => .var x
  | .app f args => .app (.inr f) (Term.mapSymList Sum.inl args)

@[simp] theorem destructorPattern_app (f : sigma) (args : List (Term sigma nu)) :
    destructorPattern (.app f args) = .app (.inr f) (Term.mapSymList Sum.inl args) := rfl

theorem destructorPattern_isApp {t : Term sigma nu} (h : t.isApp = true) :
    (destructorPattern t).isApp = true := by
  cases t with
  | var x => simp at h
  | app f args => rfl

/-- Erasing the labels of the shared shape returns the original term. -/
@[simp] theorem eraseLabel_destructorPattern (t : Term sigma nu) :
    eraseLabel (destructorPattern t) = t := by
  cases t with
  | var x => rfl
  | app f args =>
      show Term.app (gammaSym (Sum.inr f))
        (Term.mapSymList gammaSym (Term.mapSymList Sum.inl args)) = _
      rw [eraseLabelList_constructorLabelList]
      rfl

/-! ## Patterns as application nodes -/

mutual
/-- Every application node of a term, as its symbol paired with its argument
list, the term's own root included. -/
def appNodes : Term sigma nu → List (sigma × List (Term sigma nu))
  | .var _ => []
  | .app f args => (f, args) :: appNodesList args
/-- `appNodes` across an argument list. -/
def appNodesList : List (Term sigma nu) → List (sigma × List (Term sigma nu))
  | [] => []
  | a :: as => appNodes a ++ appNodesList as
end

@[simp] theorem appNodes_var (x : nu) : appNodes (sigma := sigma) (.var x) = [] := rfl
@[simp] theorem appNodes_app (f : sigma) (args : List (Term sigma nu)) :
    appNodes (.app f args) = (f, args) :: appNodesList args := rfl
@[simp] theorem appNodesList_nil : appNodesList (sigma := sigma) (nu := nu) [] = [] := rfl
@[simp] theorem appNodesList_cons (a : Term sigma nu) (as : List (Term sigma nu)) :
    appNodesList (a :: as) = appNodes a ++ appNodesList as := rfl

theorem mem_appNodesList_of_mem {a : Term sigma nu} {args : List (Term sigma nu)}
    {n : sigma × List (Term sigma nu)} (ha : a ∈ args) (hn : n ∈ appNodes a) :
    n ∈ appNodesList args := by
  induction args with
  | nil => simp at ha
  | cons b bs ih =>
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact List.mem_append_left _ hn
      · exact List.mem_append_right _ (ih ha')

/-- The application nodes occurring **properly** inside a term. Frozen D7,
Definition 11: "a pattern is a proper subterm of the left-hand side of a rule". -/
def properAppNodes : Term sigma nu → List (sigma × List (Term sigma nu))
  | .var _ => []
  | .app _ args => appNodesList args

@[simp] theorem properAppNodes_app (f : sigma) (args : List (Term sigma nu)) :
    properAppNodes (.app f args) = appNodesList args := rfl

/-- `Pat(T)`, as application nodes. -/
def patternNodes : TRS sigma nu → List (sigma × List (Term sigma nu))
  | [] => []
  | rule :: rest => properAppNodes rule.lhs ++ patternNodes rest

theorem mem_patternNodes {R : TRS sigma nu} {rule : Rule sigma nu}
    {n : sigma × List (Term sigma nu)} (hrule : rule ∈ R)
    (hn : n ∈ properAppNodes rule.lhs) : n ∈ patternNodes R := by
  induction R with
  | nil => simp at hrule
  | cons r rest ih =>
      rcases List.mem_cons.1 hrule with rfl | h
      · exact List.mem_append_left _ hn
      · exact List.mem_append_right _ (ih h)

/-! ## The translation -/

/-- The `R'_d` rule of a source rule: frozen D7,
`F_d(floor(t_1), ..., floor(t_n)) -> ceil(r)`. -/
def transRule (rule : Rule sigma nu) : Rule (sigma ⊕ sigma) nu where
  lhs := destructorPattern rule.lhs
  rhs := destructorLabel rule.rhs
  lhs_isApp := destructorPattern_isApp rule.lhs_isApp

/-- The `R'_c` rule of a pattern node: frozen D7,
`F_d(floor(t_1), ..., floor(t_n)) -> F_c(floor(t_1), ..., floor(t_n))`. -/
def patternRuleOf (n : sigma × List (Term sigma nu)) : Rule (sigma ⊕ sigma) nu where
  lhs := .app (.inr n.1) (Term.mapSymList Sum.inl n.2)
  rhs := .app (.inl n.1) (Term.mapSymList Sum.inl n.2)
  lhs_isApp := rfl

/-- Frozen D7, Definition 12: the constructor translation `T'` of `T`. -/
def constructorTranslation (R : TRS sigma nu) : TRS (sigma ⊕ sigma) nu :=
  R.map transRule ++ (patternNodes R).map patternRuleOf

theorem transRule_mem {R : TRS sigma nu} {rule : Rule sigma nu} (h : rule ∈ R) :
    transRule rule ∈ constructorTranslation R :=
  List.mem_append_left _ (List.mem_map_of_mem h)

theorem patternRuleOf_mem {R : TRS sigma nu} {n : sigma × List (Term sigma nu)}
    (h : n ∈ patternNodes R) : patternRuleOf n ∈ constructorTranslation R :=
  List.mem_append_right _ (List.mem_map_of_mem h)

/-- Every rule of the translation is one of the two families. -/
theorem mem_constructorTranslation {R : TRS sigma nu} {rule : Rule (sigma ⊕ sigma) nu}
    (h : rule ∈ constructorTranslation R) :
    (∃ r ∈ R, rule = transRule r) ∨ (∃ n ∈ patternNodes R, rule = patternRuleOf n) := by
  rcases List.mem_append.1 h with h' | h'
  · obtain ⟨r, hr, hrule⟩ := List.mem_map.1 h'
    exact Or.inl ⟨r, hr, hrule.symm⟩
  · obtain ⟨n, hn, hrule⟩ := List.mem_map.1 h'
    exact Or.inr ⟨n, hn, hrule.symm⟩

/-! ## Lemma 13 -/

/-- **Lemma 13.** Frozen source: "Let T be a TRS and T' its constructor
translation. For any p in Pat(T) we have ceil(p) ->* floor(p)."

Stated here for any term whose application nodes are all pattern nodes, which is
the induction-friendly form: the direct arguments of a pattern are patterns, so
the hypothesis survives descent. -/
theorem lemma13 (R : TRS sigma nu) :
    ∀ (p : Term sigma nu), (∀ n ∈ appNodes p, n ∈ patternNodes R) →
      StepStar (constructorTranslation R) (destructorLabel p) (constructorLabel p) := by
  intro p
  induction p using Term.rec' with
  | hvar x => intro _; exact StepStar.refl _ _
  | happ f args ih =>
      intro hn
      have hnode : (f, args) ∈ patternNodes R := hn (f, args) (by simp)
      have hargs : ∀ a ∈ args,
          StepStar (constructorTranslation R) (destructorLabel a) (constructorLabel a) := by
        intro a ha
        refine ih a ha (fun m hm => hn m ?_)
        simp only [appNodes_app, List.mem_cons]
        exact Or.inr (mem_appNodesList_of_mem ha hm)
      have hstar : StepStar (constructorTranslation R)
          (.app (Sum.inr f) (Term.mapSymList Sum.inr args))
          (.app (Sum.inr f) (Term.mapSymList Sum.inl args)) := by
        rw [Term.mapSymList_eq_map, Term.mapSymList_eq_map]
        exact StepStar.args _ (forall₂_map_map hargs)
      refine StepStar.tail hstar (Step.root ⟨patternRuleOf (f, args),
        patternRuleOf_mem hnode, Subst.id, ?_, ?_⟩)
      · exact (Subst.id_apply _).symm
      · exact (Subst.id_apply _).symm

/-- The direct arguments of a rule's left-hand side satisfy Lemma 13's
hypothesis. -/
theorem appNodes_subset_patternNodes {R : TRS sigma nu} {rule : Rule sigma nu}
    (hrule : rule ∈ R) {f : sigma} {args : List (Term sigma nu)}
    (hlhs : rule.lhs = .app f args) {a : Term sigma nu} (ha : a ∈ args) :
    ∀ n ∈ appNodes a, n ∈ patternNodes R := by
  intro n hn
  refine mem_patternNodes hrule ?_
  rw [hlhs, properAppNodes_app]
  exact mem_appNodesList_of_mem ha hn

/-! ## Lemma 14, forward direction -/

/-- A reflexive-transitive prefix followed by one genuine step is a nonempty
transitive chain. This closes the exact `->* ; ->` to `->+` shape produced by the
constructor translation's root simulation. -/
private theorem transGen_tail_of_reflTransGen {α : Type u} {r : α → α → Prop}
    {a b c : α} (h : Relation.ReflTransGen r a b) (hbc : r b c) :
    Relation.TransGen r a c := by
  induction h generalizing c with
  | refl => exact Relation.TransGen.single hbc
  | tail _ hlast ih => exact Relation.TransGen.tail (ih hlast) hbc

/-- **Lemma 14, first half, strict source form.** Frozen source: "If t ->_T u
then ceil(t) ->+_{T'} ceil(u)." The root case performs zero or more constructor-
labelling steps inside the arguments and then one genuine translated root step;
the contextual case lifts a nonempty chain through the rewritten argument. -/
theorem lemma14_forward_strict (R : TRS sigma nu) :
    ∀ {t u : Term sigma nu}, Step R t u →
      Relation.TransGen (Step (constructorTranslation R))
        (destructorLabel t) (destructorLabel u) := by
  intro t u h
  induction h with
  | @root s t' hr =>
      obtain ⟨rule, hmem, sb, hs, ht⟩ := hr
      cases hlhs : rule.lhs with
      | var x =>
          have := rule.lhs_isApp
          rw [hlhs] at this
          simp at this
      | app g gargs =>
          set sb' : Subst (sigma ⊕ sigma) nu := Term.mapSubstSym Sum.inr sb with hsb'
          have hargs : ∀ a ∈ gargs,
              StepStar (constructorTranslation R)
                (Subst.apply sb' (destructorLabel a))
                (Subst.apply sb' (constructorLabel a)) := by
            intro a ha
            exact StepStar.subst sb'
              (lemma13 R a (appNodes_subset_patternNodes hmem hlhs ha))
          have hstar : StepStar (constructorTranslation R)
              (.app (Sum.inr g)
                (Subst.applyList sb' (Term.mapSymList Sum.inr gargs)))
              (.app (Sum.inr g)
                (Subst.applyList sb' (Term.mapSymList Sum.inl gargs))) := by
            rw [Subst.applyList_eq_map, Subst.applyList_eq_map,
              Term.mapSymList_eq_map, Term.mapSymList_eq_map, List.map_map, List.map_map]
            exact StepStar.args _ (forall₂_map_map hargs)
          have hsrc : destructorLabel s
              = .app (Sum.inr g)
                  (Subst.applyList sb' (Term.mapSymList Sum.inr gargs)) := by
            rw [hs, destructorLabel_apply, hlhs]
            rfl
          have hmid : Subst.apply sb' (transRule rule).lhs
              = .app (Sum.inr g)
                  (Subst.applyList sb' (Term.mapSymList Sum.inl gargs)) := by
            show Subst.apply sb' (destructorPattern rule.lhs) = _
            rw [hlhs]
            rfl
          have htgt : Subst.apply sb' (transRule rule).rhs = destructorLabel t' := by
            show Subst.apply sb' (destructorLabel rule.rhs) = _
            rw [ht, destructorLabel_apply]
          rw [hsrc]
          exact transGen_tail_of_reflTransGen hstar
            (Step.root ⟨transRule rule, transRule_mem hmem, sb', hmid.symm, htgt.symm⟩)
  | arg f pre post _ ih =>
      simp only [destructorLabel, Term.mapSym_app, Term.mapSymList_eq_map,
        List.map_append, List.map_cons]
      exact Relation.TransGen.lift
        (fun z => Term.app (Sum.inr f)
          (pre.map (Term.mapSym Sum.inr) ++ z :: post.map (Term.mapSym Sum.inr)))
        (fun _ _ hstep => Step.arg _ _ _ hstep) ih

/-- **Lemma 14, first half, reflexive-transitive API form.** This is the direct
corollary consumed by Proposition 15 and retained for downstream compatibility. -/
theorem lemma14_forward (R : TRS sigma nu) {t u : Term sigma nu} (h : Step R t u) :
    StepStar (constructorTranslation R) (destructorLabel t) (destructorLabel u) :=
  (lemma14_forward_strict R h).to_reflTransGen

/-! ## Lemma 14, backward direction -/

/-- **Lemma 14, second half.** Frozen source: "If p ->_{T'} q then
|p| ->_T |q| or |p| = |q|." A translated rule contributes a genuine step; a
pattern rule only relabels a root, so it leaves the erasure unchanged. -/
theorem lemma14_back (R : TRS sigma nu) :
    ∀ {p q : Term (sigma ⊕ sigma) nu}, Step (constructorTranslation R) p q →
      Step R (eraseLabel p) (eraseLabel q) ∨ eraseLabel p = eraseLabel q := by
  intro p q h
  induction h with
  | @root s t hr =>
      obtain ⟨rule, hmem, tb, hs, ht⟩ := hr
      rcases mem_constructorTranslation hmem with ⟨r, hr', rfl⟩ | ⟨n, _, rfl⟩
      · refine Or.inl (Step.root ⟨r, hr', Term.mapSubstSym gammaSym tb, ?_, ?_⟩)
        · rw [hs, eraseLabel_apply]
          simp only [transRule, eraseLabel_destructorPattern]
        · rw [ht, eraseLabel_apply]
          simp only [transRule, eraseLabel_destructorLabel]
      · refine Or.inr ?_
        have hlr : eraseLabel (patternRuleOf n).lhs = eraseLabel (patternRuleOf n).rhs := rfl
        rw [hs, ht, eraseLabel_apply, eraseLabel_apply, hlr]
  | arg f pre post _ ih =>
      rcases ih with hstep | heq
      · left
        simp only [eraseLabel, Term.mapSym_app, Term.mapSymList_eq_map,
          List.map_append, List.map_cons]
        exact Step.arg _ _ _ hstep
      · right
        simp only [eraseLabel, Term.mapSym_app, Term.mapSymList_eq_map,
          List.map_append, List.map_cons]
        exact congrArg (fun z => Term.app (gammaSym f)
          (pre.map (Term.mapSym gammaSym) ++ z :: post.map (Term.mapSym gammaSym))) heq

/-! ## Proposition 15 and Corollary 16 -/

/-- **Proposition 15, first half.** Frozen source: "For t, u in Ter(Sigma, X),
if t =_T u then ceil(t) =_{T'} ceil(u)." -/
theorem prop15_forward (R : TRS sigma nu) {t u : Term sigma nu} (h : conv R t u) :
    conv (constructorTranslation R) (destructorLabel t) (destructorLabel u) := by
  induction h with
  | refl => exact conv.refl _ _
  | tail _ hlast ih =>
      refine conv.trans ih ?_
      rcases hlast with hstep | hstep
      · exact conv.of_stepStar (lemma14_forward R hstep)
      · exact conv.symm (conv.of_stepStar (lemma14_forward R hstep))

/-- **Proposition 15, second half.** Frozen source: "For p, q in Ter(Sigma2, Y),
if p =_{T'} q then |p| =_T |q|." -/
theorem prop15_back (R : TRS sigma nu) {p q : Term (sigma ⊕ sigma) nu}
    (h : conv (constructorTranslation R) p q) :
    conv R (eraseLabel p) (eraseLabel q) := by
  induction h with
  | refl => exact conv.refl _ _
  | tail _ hlast ih =>
      refine conv.trans ih ?_
      rcases hlast with hstep | hstep
      · rcases lemma14_back R hstep with hs | he
        · exact conv.of_step hs
        · exact he ▸ conv.refl _ _
      · rcases lemma14_back R hstep with hs | he
        · exact conv.symm (conv.of_step hs)
        · exact he ▸ conv.refl _ _

/-- **Corollary 16.** Frozen source: "Let T be a TRS and T' its constructor
translation. Then T is consistent iff T' is."

Both directions use that a variable is its own image under every labelling. -/
theorem cor16 (R : TRS sigma nu) :
    Consistent R ↔ Consistent (constructorTranslation R) := by
  constructor
  · intro hcon x y hxy
    exact hcon x y (by simpa using prop15_back R hxy)
  · intro hcon x y hxy
    exact hcon x y (by simpa using prop15_forward R hxy)

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.constructorLabel
#check @OperatorKO7.Meta.UniqueNormalization.destructorLabel
#check @OperatorKO7.Meta.UniqueNormalization.eraseLabel
#check @OperatorKO7.Meta.UniqueNormalization.destructorPattern
#check @OperatorKO7.Meta.UniqueNormalization.appNodes
#check @OperatorKO7.Meta.UniqueNormalization.patternNodes
#check @OperatorKO7.Meta.UniqueNormalization.transRule
#check @OperatorKO7.Meta.UniqueNormalization.patternRuleOf
#check @OperatorKO7.Meta.UniqueNormalization.constructorTranslation
#check @OperatorKO7.Meta.UniqueNormalization.lemma14_forward_strict

#print axioms OperatorKO7.Meta.UniqueNormalization.eraseLabel_constructorLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.eraseLabel_destructorPattern
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma13
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma14_forward_strict
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma14_forward
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma14_back
#print axioms OperatorKO7.Meta.UniqueNormalization.prop15_forward
#print axioms OperatorKO7.Meta.UniqueNormalization.prop15_back
#print axioms OperatorKO7.Meta.UniqueNormalization.cor16

#check @OperatorKO7.Meta.UniqueNormalization.transGen_tail_of_reflTransGen
#print axioms OperatorKO7.Meta.UniqueNormalization.transGen_tail_of_reflTransGen
