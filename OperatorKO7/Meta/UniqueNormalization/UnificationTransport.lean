import OperatorKO7.Meta.UniqueNormalization.Lemma36
import OperatorKO7.Meta.UniqueNormalization.ConstructorTranslation

/-!
# Omega-unifiability along a signature morphism, and its symmetry

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 7, in support of Proposition 22 and of
the Theorem 69 signature extension.

Convention CC1 speaks about one signature, while the constructor translation and
the Theorem 69 extension move terms to another. Relabelling symbols along any map
`f` is a signature morphism, and the pushforward of a unification closure along
it, closed under equivalence, is again a unification closure:
`unifClosure_pushEqv`. The proof keeps, for every pair in the equivalence closure,
a witness of one of four shapes according to whether each side is an application
or a variable, and shows the witness survives reflexivity, symmetry and
transitivity. `omegaUnifiable_mapSym` is the consequence; `omegaUnifiable_eraseLabel`
is its instance for the label erasure.

`OmegaUnifiable.symm` swaps the two rename-apart tags.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u u' v w

variable {sigma : Type u} {tau : Type u'} {mu : Type v}

/-! ## Relabelling on the two term shapes -/

theorem mapSym_eq_var {f : sigma → tau} {a : Term sigma mu} {x : mu}
    (h : Term.mapSym f a = Term.var x) : a = Term.var x := by
  cases a with
  | var y =>
      rw [Term.mapSym_var] at h
      have hyx : y = x := by simpa using h
      rw [hyx]
  | app g xs => rw [Term.mapSym_app] at h; simp at h

theorem mapSym_eq_app {f : sigma → tau} {a : Term sigma mu} {g : tau}
    {xs : List (Term tau mu)} (h : Term.mapSym f a = Term.app g xs) :
    ∃ (g' : sigma) (xs' : List (Term sigma mu)),
      a = Term.app g' xs' ∧ f g' = g ∧ xs'.map (Term.mapSym f) = xs := by
  cases a with
  | var y => rw [Term.mapSym_var] at h; simp at h
  | app g' xs' =>
      rw [Term.mapSym_app, Term.mapSymList_eq_map] at h
      simp only [Term.app.injEq] at h
      exact ⟨g', xs', rfl, h.1, h.2⟩

/-! ## The pushforward and its four-shape witness -/

/-- The pushforward of `E` along the relabelling `f`. -/
def symPush (f : sigma → tau) (E : Term sigma mu → Term sigma mu → Prop)
    (a b : Term tau mu) : Prop :=
  ∃ a' b', E a' b' ∧ Term.mapSym f a' = a ∧ Term.mapSym f b' = b

/-- The equivalence closure of the pushforward. -/
def pushEqv (f : sigma → tau) (E : Term sigma mu → Term sigma mu → Prop) :
    Term tau mu → Term tau mu → Prop :=
  Relation.EqvGen (symPush f E)

/-- The witness kept for a pair of the closure: decomposition between two
applications, a lifted application beside a variable, and either a direct
relation or a two-application bridge between two variables. -/
def PushWitness (f : sigma → tau) (E : Term sigma mu → Term sigma mu → Prop) :
    Term tau mu → Term tau mu → Prop
  | .app g xs, .app h ys => g = h ∧ List.Forall₂ (pushEqv f E) xs ys
  | .app g xs, .var v => ∃ (g' : sigma) (ys' : List (Term sigma mu)),
      f g' = g ∧ E (.app g' ys') (.var v) ∧
        List.Forall₂ (pushEqv f E) xs (ys'.map (Term.mapSym f))
  | .var v, .app h ys => ∃ (h' : sigma) (ys' : List (Term sigma mu)),
      f h' = h ∧ E (.var v) (.app h' ys') ∧
        List.Forall₂ (pushEqv f E) (ys'.map (Term.mapSym f)) ys
  | .var v, .var w => E (.var v) (.var w) ∨
      ∃ (p' q' : sigma) (ps' qs' : List (Term sigma mu)),
        E (.var v) (.app p' ps') ∧ E (.app q' qs') (.var w) ∧ f p' = f q' ∧
          List.Forall₂ (pushEqv f E) (ps'.map (Term.mapSym f)) (qs'.map (Term.mapSym f))

section Witness

variable {f : sigma → tau} {E : Term sigma mu → Term sigma mu → Prop}

theorem pushEqv_refl (a : Term tau mu) : pushEqv f E a a := Relation.EqvGen.refl a
theorem pushEqv_symm {a b : Term tau mu} (h : pushEqv f E a b) : pushEqv f E b a :=
  Relation.EqvGen.symm a b h
theorem pushEqv_trans {a b c : Term tau mu} (h₁ : pushEqv f E a b) (h₂ : pushEqv f E b c) :
    pushEqv f E a c :=
  Relation.EqvGen.trans a b c h₁ h₂

theorem forall₂_pushEqv_refl (l : List (Term tau mu)) : List.Forall₂ (pushEqv f E) l l :=
  forall₂_self (fun a => pushEqv_refl a) l

theorem forall₂_pushEqv_symm {l₁ l₂ : List (Term tau mu)}
    (h : List.Forall₂ (pushEqv f E) l₁ l₂) : List.Forall₂ (pushEqv f E) l₂ l₁ :=
  forall₂_swap (fun _ _ hab => pushEqv_symm hab) h

theorem forall₂_pushEqv_trans :
    ∀ {l₁ l₂ l₃ : List (Term tau mu)}, List.Forall₂ (pushEqv f E) l₁ l₂ →
      List.Forall₂ (pushEqv f E) l₂ l₃ → List.Forall₂ (pushEqv f E) l₁ l₃ := by
  intro l₁ l₂ l₃ h₁
  induction h₁ generalizing l₃ with
  | nil => intro h₂; cases h₂; exact List.Forall₂.nil
  | cons hab _ ih =>
      intro h₂
      cases h₂ with
      | cons hbc htail => exact List.Forall₂.cons (pushEqv_trans hab hbc) (ih htail)

/-- Two lists related by `E` relabel to lists related by the closure. -/
theorem forall₂_pushEqv_of_forall₂ {xs' ys' : List (Term sigma mu)}
    (h : List.Forall₂ E xs' ys') :
    List.Forall₂ (pushEqv f E) (xs'.map (Term.mapSym f)) (ys'.map (Term.mapSym f)) := by
  refine forall₂_map₂_of ?_
  refine forall₂_mono ?_ h
  intro x' y' hxy
  exact Relation.EqvGen.rel _ _ ⟨x', y', hxy, rfl, rfl⟩

/-- Decomposition of `E` between two applications, relabelled. -/
theorem decomp_pushed (hE : UnifClosure E) {f' g' : sigma}
    {xs' ys' : List (Term sigma mu)} (h : E (.app f' xs') (.app g' ys')) :
    f' = g' ∧ List.Forall₂ (pushEqv f E) (xs'.map (Term.mapSym f)) (ys'.map (Term.mapSym f)) :=
  ⟨hE.symbol_eq h, forall₂_pushEqv_of_forall₂ (hE.args_forall₂ h)⟩

theorem pushWitness_of_rel (hE : UnifClosure E) {a b : Term tau mu} (h : symPush f E a b) :
    PushWitness f E a b := by
  obtain ⟨a', b', hab, rfl, rfl⟩ := h
  cases a' with
  | var v =>
      cases b' with
      | var w => exact Or.inl hab
      | app g' ys' =>
          rw [Term.mapSym_var, Term.mapSym_app, Term.mapSymList_eq_map]
          exact ⟨g', ys', rfl, hab, forall₂_pushEqv_refl _⟩
  | app f' xs' =>
      cases b' with
      | var w =>
          rw [Term.mapSym_app, Term.mapSym_var, Term.mapSymList_eq_map]
          exact ⟨f', xs', rfl, hab, forall₂_pushEqv_refl _⟩
      | app g' ys' =>
          rw [Term.mapSym_app, Term.mapSym_app, Term.mapSymList_eq_map, Term.mapSymList_eq_map]
          obtain ⟨hfg, hargs⟩ := decomp_pushed hE hab
          exact ⟨congrArg f hfg, hargs⟩

theorem pushWitness_refl (hE : UnifClosure E) (a : Term tau mu) : PushWitness f E a a := by
  cases a with
  | var v => exact Or.inl (hE.rfl' _)
  | app g xs => exact ⟨rfl, forall₂_pushEqv_refl xs⟩

theorem pushWitness_symm (hE : UnifClosure E) {a b : Term tau mu} (h : PushWitness f E a b) :
    PushWitness f E b a := by
  cases a with
  | var v =>
      cases b with
      | var w =>
          rcases h with h | ⟨p', q', ps', qs', h₁, h₂, hpq, hargs⟩
          · exact Or.inl (hE.symm' h)
          · exact Or.inr ⟨q', p', qs', ps', hE.symm' h₂, hE.symm' h₁, hpq.symm,
              forall₂_pushEqv_symm hargs⟩
      | app g ys =>
          obtain ⟨g', ys', hg, hrel, hargs⟩ := h
          exact ⟨g', ys', hg, hE.symm' hrel, forall₂_pushEqv_symm hargs⟩
  | app g xs =>
      cases b with
      | var w =>
          obtain ⟨g', ys', hg, hrel, hargs⟩ := h
          exact ⟨g', ys', hg, hE.symm' hrel, forall₂_pushEqv_symm hargs⟩
      | app h ys =>
          obtain ⟨hgh, hargs⟩ := h
          exact ⟨hgh.symm, forall₂_pushEqv_symm hargs⟩

theorem pushWitness_trans (hE : UnifClosure E) {a b c : Term tau mu}
    (h₁ : PushWitness f E a b) (h₂ : PushWitness f E b c) : PushWitness f E a c := by
  cases a with
  | app g xs =>
      cases b with
      | app h ys =>
          obtain ⟨hgh, hxy⟩ := h₁
          cases c with
          | app k zs =>
              obtain ⟨hhk, hyz⟩ := h₂
              exact ⟨hgh.trans hhk, forall₂_pushEqv_trans hxy hyz⟩
          | var w =>
              obtain ⟨h', ys', hh, hrel, hargs⟩ := h₂
              exact ⟨h', ys', hh.trans hgh.symm, hrel, forall₂_pushEqv_trans hxy hargs⟩
      | var v =>
          obtain ⟨g', ys', hg, hrel₁, hargs₁⟩ := h₁
          cases c with
          | app k zs =>
              obtain ⟨k', zs', hk, hrel₂, hargs₂⟩ := h₂
              have hE' : E (.app g' ys') (.app k' zs') := hE.trans' hrel₁ hrel₂
              obtain ⟨hgk, hargs⟩ := decomp_pushed hE hE'
              refine ⟨?_, forall₂_pushEqv_trans hargs₁ (forall₂_pushEqv_trans hargs hargs₂)⟩
              rw [← hg, ← hk, hgk]
          | var w =>
              rcases h₂ with hvw | ⟨p', q', ps', qs', hvp, hqw, hpq, hargs₂⟩
              · exact ⟨g', ys', hg, hE.trans' hrel₁ hvw, hargs₁⟩
              · have hE' : E (.app g' ys') (.app p' ps') := hE.trans' hrel₁ hvp
                obtain ⟨hgp, hargs⟩ := decomp_pushed hE hE'
                refine ⟨q', qs', ?_, hqw,
                  forall₂_pushEqv_trans hargs₁ (forall₂_pushEqv_trans hargs hargs₂)⟩
                rw [← hpq, ← hgp, hg]
  | var v =>
      cases b with
      | app h ys =>
          obtain ⟨h', ys', hh, hrel₁, hargs₁⟩ := h₁
          cases c with
          | app k zs =>
              obtain ⟨hhk, hyz⟩ := h₂
              exact ⟨h', ys', hh.trans hhk, hrel₁, forall₂_pushEqv_trans hargs₁ hyz⟩
          | var w =>
              obtain ⟨k', zs', hk, hrel₂, hargs₂⟩ := h₂
              exact Or.inr ⟨h', k', ys', zs', hrel₁, hrel₂, hh.trans hk.symm,
                forall₂_pushEqv_trans hargs₁ hargs₂⟩
      | var w =>
          cases c with
          | app k zs =>
              obtain ⟨k', zs', hk, hrel₂, hargs₂⟩ := h₂
              rcases h₁ with hvw | ⟨p', q', ps', qs', hvp, hqw, hpq, hargs₁⟩
              · exact ⟨k', zs', hk, hE.trans' hvw hrel₂, hargs₂⟩
              · have hE' : E (.app q' qs') (.app k' zs') := hE.trans' hqw hrel₂
                obtain ⟨hqk, hargs⟩ := decomp_pushed hE hE'
                refine ⟨p', ps', ?_, hvp,
                  forall₂_pushEqv_trans hargs₁ (forall₂_pushEqv_trans hargs hargs₂)⟩
                rw [hpq, hqk, hk]
          | var u =>
              rcases h₁ with hvw | ⟨p', q', ps', qs', hvp, hqw, hpq, hargs₁⟩
              · rcases h₂ with hwu | ⟨p'', q'', ps'', qs'', hwp, hqu, hpq', hargs₂⟩
                · exact Or.inl (hE.trans' hvw hwu)
                · exact Or.inr ⟨p'', q'', ps'', qs'', hE.trans' hvw hwp, hqu, hpq', hargs₂⟩
              · rcases h₂ with hwu | ⟨p'', q'', ps'', qs'', hwp, hqu, hpq', hargs₂⟩
                · exact Or.inr ⟨p', q', ps', qs', hvp, hE.trans' hqw hwu, hpq, hargs₁⟩
                · have hE' : E (.app q' qs') (.app p'' ps'') := hE.trans' hqw hwp
                  obtain ⟨hqp, hargs⟩ := decomp_pushed hE hE'
                  refine Or.inr ⟨p', q'', ps', qs'', hvp, hqu, ?_,
                    forall₂_pushEqv_trans hargs₁ (forall₂_pushEqv_trans hargs hargs₂)⟩
                  rw [hpq, hqp, hpq']

theorem pushWitness_of_pushEqv (hE : UnifClosure E) :
    ∀ {a b : Term tau mu}, pushEqv f E a b → PushWitness f E a b := by
  intro a b h
  induction h with
  | rel a b hab => exact pushWitness_of_rel hE hab
  | refl a => exact pushWitness_refl hE a
  | symm a b _ ih => exact pushWitness_symm hE ih
  | trans a b c _ _ ih₁ ih₂ => exact pushWitness_trans hE ih₁ ih₂

/-- **The pushforward closure is a unification closure.** -/
theorem unifClosure_pushEqv (hE : UnifClosure E) : UnifClosure (pushEqv f E) where
  rfl' := pushEqv_refl
  symm' := pushEqv_symm
  trans' := pushEqv_trans
  decomp := by
    intro g h xs ys hrel
    exact pushWitness_of_pushEqv hE hrel

end Witness

/-! ## Relabelling commutes with renaming -/

theorem mapSym_mapVar {mu' : Type w} (f : sigma → tau) (g : mu → mu') :
    ∀ t : Term sigma mu, Term.mapSym f (Term.mapVar g t) = Term.mapVar g (Term.mapSym f t) := by
  intro t
  induction t using Term.rec' with
  | hvar x => rfl
  | happ h args ih =>
      rw [Term.mapVar_app, Term.mapSym_app, Term.mapSym_app, Term.mapVar_app,
        Term.mapVarList_eq_map, Term.mapVarList_eq_map, Term.mapSymList_eq_map,
        Term.mapSymList_eq_map, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-- Omega-unifiability is preserved by any relabelling of symbols. -/
theorem omegaUnifiableShared_mapSym (f : sigma → tau) {s t : Term sigma mu}
    (h : OmegaUnifiableShared s t) :
    OmegaUnifiableShared (Term.mapSym f s) (Term.mapSym f t) := by
  obtain ⟨E, hE, hst⟩ := h
  exact ⟨pushEqv f E, unifClosure_pushEqv hE, Relation.EqvGen.rel _ _ ⟨s, t, hst, rfl, rfl⟩⟩

theorem omegaUnifiable_mapSym {nu : Type v} (f : sigma → tau) {s t : Term sigma nu}
    (h : OmegaUnifiable s t) : OmegaUnifiable (Term.mapSym f s) (Term.mapSym f t) := by
  unfold OmegaUnifiable leftCopy rightCopy at h ⊢
  rw [← mapSym_mapVar, ← mapSym_mapVar]
  exact omegaUnifiableShared_mapSym f h

/-- Source-semantic transport of omega-unifiability along any symbol relabelling. -/
theorem infiniteOmegaUnifiable_mapSym {nu : Type v} (f : sigma → tau) {s t : Term sigma nu}
    (h : InfiniteOmegaUnifiable s t) :
    InfiniteOmegaUnifiable (Term.mapSym f s) (Term.mapSym f t) :=
  (omegaUnifiable_iff_infinite _ _).mp
    (omegaUnifiable_mapSym f ((omegaUnifiable_iff_infinite _ _).mpr h))

/-- **Exact transport along a split signature embedding.** If `g` is a left inverse of `f`,
then relabelling by `f` preserves and reflects omega-unifiability. This is stronger than the
one-way functoriality above and is the exact transport theorem for signature inclusions that
come with an explicit retraction. -/
theorem omegaUnifiable_mapSym_iff_of_leftInverse {nu : Type v}
    (f : sigma → tau) (g : tau → sigma) (hgf : Function.LeftInverse g f)
    {s t : Term sigma nu} :
    OmegaUnifiable (Term.mapSym f s) (Term.mapSym f t) ↔ OmegaUnifiable s t := by
  constructor
  · intro h
    have hpush := omegaUnifiable_mapSym g h
    have hcomp : (fun x => g (f x)) = fun x => x := funext hgf
    rw [Term.mapSym_mapSym, Term.mapSym_mapSym, hcomp, Term.mapSym_id, Term.mapSym_id] at hpush
    exact hpush
  · exact omegaUnifiable_mapSym f

/-- Infinite-term semantic transport is also exact along split signature embeddings. -/
theorem infiniteOmegaUnifiable_mapSym_iff_of_leftInverse {nu : Type v}
    (f : sigma → tau) (g : tau → sigma) (hgf : Function.LeftInverse g f)
    {s t : Term sigma nu} :
    InfiniteOmegaUnifiable (Term.mapSym f s) (Term.mapSym f t) ↔
      InfiniteOmegaUnifiable s t := by
  rw [← omegaUnifiable_iff_infinite, ← omegaUnifiable_iff_infinite]
  exact omegaUnifiable_mapSym_iff_of_leftInverse f g hgf

/-- The instance for the label erasure of the constructor translation. -/
theorem omegaUnifiable_eraseLabel {nu : Type v} {s t : Term (sigma ⊕ sigma) nu}
    (h : OmegaUnifiable s t) : OmegaUnifiable (eraseLabel s) (eraseLabel t) :=
  omegaUnifiable_mapSym gammaSym h

/-- Source-semantic label erasure. -/
theorem infiniteOmegaUnifiable_eraseLabel {nu : Type v} {s t : Term (sigma ⊕ sigma) nu}
    (h : InfiniteOmegaUnifiable s t) :
    InfiniteOmegaUnifiable (eraseLabel s) (eraseLabel t) :=
  infiniteOmegaUnifiable_mapSym gammaSym h

/-! ## Symmetry of omega-unifiability -/

theorem Term.mapVar_mapVar {nu : Type v} {mu₁ : Type w} {mu₂ : Type w}
    (g : nu → mu₁) (h : mu₁ → mu₂) :
    ∀ t : Term sigma nu, Term.mapVar h (Term.mapVar g t) = Term.mapVar (fun x => h (g x)) t := by
  intro t
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      simp only [Term.mapVar_app, Term.mapVarList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-- Omega-unifiability is symmetric: swap the two rename-apart tags. -/
theorem OmegaUnifiable.symm {nu : Type v} {s t : Term sigma nu} (h : OmegaUnifiable s t) :
    OmegaUnifiable t s := by
  obtain ⟨E, hE, hst⟩ := h
  refine ⟨fun a b => E (Term.mapVar Sum.swap a) (Term.mapVar Sum.swap b), ⟨fun _ => hE.rfl' _,
    fun hab => hE.symm' hab, fun hab hbc => hE.trans' hab hbc, ?_⟩, ?_⟩
  · intro f g xs ys hxy
    simp only [Term.mapVar_app, Term.mapVarList_eq_map] at hxy
    obtain ⟨hfg, hargs⟩ := hE.decomp hxy
    exact ⟨hfg, forall₂_of_map₂ hargs⟩
  · show E (Term.mapVar Sum.swap (leftCopy t)) (Term.mapVar Sum.swap (rightCopy s))
    unfold leftCopy rightCopy
    rw [Term.mapVar_mapVar, Term.mapVar_mapVar]
    have h1 : (fun x : nu => Sum.swap (Sum.inl x : nu ⊕ nu)) = Sum.inr := by
      funext x; rfl
    have h2 : (fun x : nu => Sum.swap (Sum.inr x : nu ⊕ nu)) = Sum.inl := by
      funext x; rfl
    rw [h1, h2]
    exact hE.symm' hst

/-- Symmetry at the explicit infinite-term semantic level. -/
theorem InfiniteOmegaUnifiable.symm {nu : Type v} {s t : Term sigma nu}
    (h : InfiniteOmegaUnifiable s t) : InfiniteOmegaUnifiable t s :=
  (omegaUnifiable_iff_infinite _ _).mp
    (((omegaUnifiable_iff_infinite _ _).mpr h).symm)

/-- Two omega-unifiable applications share their root symbol. -/
theorem root_eq_of_omegaUnifiable {nu : Type v} {f g : sigma} {xs ys : List (Term sigma nu)}
    (h : OmegaUnifiable (Term.app f xs) (Term.app g ys)) : f = g := by
  obtain ⟨E, hE, hst⟩ := h
  unfold leftCopy rightCopy at hst
  simp only [Term.mapVar_app] at hst
  exact hE.symbol_eq hst

/-- Source-semantic version of root-symbol agreement. -/
theorem root_eq_of_infiniteOmegaUnifiable {nu : Type v} {f g : sigma}
    {xs ys : List (Term sigma nu)}
    (h : InfiniteOmegaUnifiable (Term.app f xs) (Term.app g ys)) : f = g :=
  root_eq_of_omegaUnifiable ((omegaUnifiable_iff_infinite _ _).mpr h)

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.pushEqv
#check @OperatorKO7.Meta.UniqueNormalization.unifClosure_pushEqv
#check @OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_mapSym
#check @OperatorKO7.Meta.UniqueNormalization.infiniteOmegaUnifiable_mapSym
#check @OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_mapSym_iff_of_leftInverse
#check @OperatorKO7.Meta.UniqueNormalization.infiniteOmegaUnifiable_mapSym_iff_of_leftInverse

#print axioms OperatorKO7.Meta.UniqueNormalization.unifClosure_pushEqv
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.infiniteOmegaUnifiable_mapSym
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_mapSym_iff_of_leftInverse
#print axioms OperatorKO7.Meta.UniqueNormalization.infiniteOmegaUnifiable_mapSym_iff_of_leftInverse
#print axioms OperatorKO7.Meta.UniqueNormalization.omegaUnifiable_eraseLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.infiniteOmegaUnifiable_eraseLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.OmegaUnifiable.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.InfiniteOmegaUnifiable.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.root_eq_of_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.root_eq_of_infiniteOmegaUnifiable
