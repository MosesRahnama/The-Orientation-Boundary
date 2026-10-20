import OperatorKO7.Meta.UniqueNormalization.TermMaps

/-!
# Substitutivity and multi-argument congruence for the rewrite relation

Campaign: `Roadmaps\klop\ROADMAP.md`, shared infrastructure for WP-K2.

`Meta\Rewriting\Rewrite.lean` supplies context closure through **one** argument
position. The constructor translation needs two facts it does not:

* **substitutivity**, that a rewrite step survives applying a substitution, which
  the paper uses when it writes "by substitutivity of rewriting" in Lemma 14;
* **multi-argument congruence**, that rewriting every argument of one
  application gives a rewrite sequence on the application, which the paper uses
  when it writes "Compatibility of rewriting gives us ..." in the same proof.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Substitutivity -/

/-- A rewrite step survives applying a substitution. -/
theorem Step.subst {R : TRS sigma nu} (t : Subst sigma nu) :
    ∀ {s u : Term sigma nu}, Step R s u →
      Step R (Subst.apply t s) (Subst.apply t u) := by
  intro s u h
  induction h with
  | root hr =>
      obtain ⟨rule, hmem, sigma', hs, hu⟩ := hr
      exact Step.root ⟨rule, hmem, Subst.comp t sigma',
        by rw [hs, Subst.apply_comp], by rw [hu, Subst.apply_comp]⟩
  | arg f pre post _ ih =>
      simp only [Subst.apply_app, Subst.applyList_eq_map, List.map_append, List.map_cons]
      exact Step.arg f _ _ ih

/-- A rewrite sequence survives applying a substitution. -/
theorem StepStar.subst {R : TRS sigma nu} (t : Subst sigma nu) {s u : Term sigma nu}
    (h : StepStar R s u) : StepStar R (Subst.apply t s) (Subst.apply t u) :=
  Relation.ReflTransGen.lift (Subst.apply t) (fun _ _ hs => Step.subst t hs) h

/-! ## Multi-argument congruence -/

/-- Rewriting a suffix of an argument list, with an untouched prefix. -/
theorem StepStar.args_append {R : TRS sigma nu} (f : sigma) :
    ∀ (pre : List (Term sigma nu)) {xs ys : List (Term sigma nu)},
      List.Forall₂ (StepStar R) xs ys →
      StepStar R (.app f (pre ++ xs)) (.app f (pre ++ ys)) := by
  intro pre xs
  induction xs generalizing pre with
  | nil =>
      intro ys h
      cases h
      exact StepStar.refl R _
  | cons a as ih =>
      intro ys h
      cases h with
      | cons hab habs =>
          rename_i b _
          refine StepStar.trans (StepStar.arg_congr R f pre as hab) ?_
          simpa using ih (pre ++ [b]) habs

/-- **Multi-argument congruence**: rewriting every argument of an application
gives a rewrite sequence on the application. -/
theorem StepStar.args {R : TRS sigma nu} (f : sigma) {xs ys : List (Term sigma nu)}
    (h : List.Forall₂ (StepStar R) xs ys) :
    StepStar R (.app f xs) (.app f ys) := by
  simpa using StepStar.args_append f [] h

/-- A pointwise relation between two maps of one list is a `Forall₂`. -/
theorem forall₂_map_map {alpha : Type u} {beta : Type v}
    {r : beta → beta → Prop} {f g : alpha → beta} :
    ∀ {xs : List alpha}, (∀ a ∈ xs, r (f a) (g a)) →
      List.Forall₂ r (xs.map f) (xs.map g) := by
  intro xs
  induction xs with
  | nil => intro _; exact List.Forall₂.nil
  | cons a as ih =>
      intro h
      exact List.Forall₂.cons (h a (by simp)) (ih (fun c hc => h c (by simp [hc])))

end OperatorKO7.Meta.Rewriting

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.Rewriting.Step.subst
#check @OperatorKO7.Meta.Rewriting.StepStar.subst
#check @OperatorKO7.Meta.Rewriting.StepStar.args

#print axioms OperatorKO7.Meta.Rewriting.Step.subst
#print axioms OperatorKO7.Meta.Rewriting.StepStar.subst
#print axioms OperatorKO7.Meta.Rewriting.StepStar.args_append
#print axioms OperatorKO7.Meta.Rewriting.StepStar.args
#print axioms OperatorKO7.Meta.Rewriting.forall₂_map_map
