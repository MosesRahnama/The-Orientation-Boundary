import OperatorKO7.Meta.UniqueNormalization.Transfer

/-!
# Omega-unification against ground terms

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K1a follow-up.

`FreezingNeeded` in `Theorem69.lean` shows that an **open** normal form can
omega-unify with a left-hand side, which is why Kahrs and Smith enlarge the
signature by the variable set and freeze the variables of the two normal forms
into constants. This module proves the positive counterpart: once the terms are
ground, both obstructions the Theorem 69 extension has to avoid disappear.

Two results, and they are the mathematical content of "the extension stays
inside the class":

* `eq_of_ground_omegaUnifiable`: distinct ground terms never omega-unify, so the
  two new rules `F(t, x, y) -> x` and `F(u, x, y) -> y` do not overlap each
  other once `t` and `u` are ground and distinct;
* `exists_match_of_ground_omegaUnifiable`: a ground term that omega-unifies with
  a left-hand side is an instance of it, hence a redex. A ground normal form
  therefore has no subterm omega-unifying with any left-hand side, which is
  `subterm_not_omegaUnifiable_of_ground_normalForm`.

The proofs use the finite `UnifClosure` representation because it exposes the
decomposition relation needed by the induction. `RationalUnification.lean` now
proves that representation equivalent to explicit potentially infinite M-type
substitution semantics, and this module exports both formulations. The matcher
construction uses classical choice to read one representative off the finite
certificate; the campaign baseline permits it.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v w

variable {sigma : Type u} {nu : Type v}

/-! ## Ground terms -/

/-- A term with no variable occurrences. -/
def Ground (t : Term sigma nu) : Prop := ∀ x : nu, ¬ VarOccurs x t

/-- Arguments of a ground application are ground. -/
theorem Ground.of_arg {f : sigma} {args : List (Term sigma nu)}
    (h : Ground (.app f args)) {a : Term sigma nu} (ha : a ∈ args) : Ground a :=
  fun x hx => h x (VarOccurs.arg ha hx)

/-- A ground term is an application. -/
theorem Ground.isApp {t : Term sigma nu} (h : Ground t) : t.isApp = true := by
  cases t with
  | var x => exact (h x VarOccurs.here).elim
  | app f args => rfl

/-- Subterms of a ground term are ground. -/
theorem Ground.subterm {t s : Term sigma nu} (h : Ground t) (hsub : Subterm s t) :
    Ground s := by
  induction hsub with
  | refl => exact h
  | @arg a f args hmem _ ih => exact ih (h.of_arg hmem)

/-- Renaming leaves a ground term unchanged, so any two renamings agree on it. -/
theorem Ground.mapVar_eq {mu : Type w} (g h : nu → mu) :
    ∀ (t : Term sigma nu), Ground t → Term.mapVar g t = Term.mapVar h t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro hg; exact (hg x VarOccurs.here).elim
  | happ f args ih =>
      intro hg
      simp only [Term.mapVar_app, Term.mapVarList_eq_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha (hg.of_arg ha))

/-- On a ground term the two rename-apart copies coincide. -/
theorem Ground.leftCopy_eq_rightCopy {t : Term sigma nu} (h : Ground t) :
    leftCopy t = rightCopy t :=
  Ground.mapVar_eq Sum.inl Sum.inr t h

/-! ## Distinct ground terms never omega-unify -/

/-- A unification closure relating the two copies of ground terms forces them
equal: the decomposition clause descends through the whole structure, and a
ground term has no variable leaf to absorb a difference. -/
theorem eq_of_unifClosure_ground
    {E : Term sigma (nu ⊕ nu) → Term sigma (nu ⊕ nu) → Prop} (hE : UnifClosure E) :
    ∀ (a : Term sigma nu), Ground a → ∀ b : Term sigma nu, Ground b →
      E (leftCopy a) (rightCopy b) → a = b := by
  have hlist : ∀ (as : List (Term sigma nu)),
      (∀ a ∈ as, Ground a → ∀ b : Term sigma nu, Ground b →
        E (leftCopy a) (rightCopy b) → a = b) →
      (∀ a ∈ as, Ground a) →
      ∀ bs : List (Term sigma nu), (∀ b ∈ bs, Ground b) →
        List.Forall₂ E (as.map leftCopy) (bs.map rightCopy) → as = bs := by
    intro as
    induction as with
    | nil =>
        intro _ _ bs _ h
        cases bs with
        | nil => rfl
        | cons b bs => cases h
    | cons a as ihs =>
        intro hmem hga bs hgb h
        cases bs with
        | nil => cases h
        | cons b bs =>
            cases h with
            | cons hab habs =>
                have h1 := hmem a (by simp) (hga a (by simp)) b (hgb b (by simp)) hab
                have h2 := ihs (fun c hc => hmem c (by simp [hc]))
                  (fun c hc => hga c (by simp [hc])) bs
                  (fun c hc => hgb c (by simp [hc])) habs
                rw [h1, h2]
  intro a
  induction a using Term.rec' with
  | hvar x => intro hg; exact (hg x VarOccurs.here).elim
  | happ f args ih =>
      intro hga b hgb hrel
      cases b with
      | var y => exact (hgb y VarOccurs.here).elim
      | app g bs =>
          have hrel' : E (.app f (Term.mapVarList Sum.inl args))
              (.app g (Term.mapVarList Sum.inr bs)) := hrel
          obtain ⟨hfg, hargs⟩ := hE.decomp hrel'
          subst hfg
          rw [Term.mapVarList_eq_map, Term.mapVarList_eq_map] at hargs
          refine congrArg _ ?_
          exact hlist args (fun c hc => ih c hc) (fun c hc => hga.of_arg hc) bs
            (fun c hc => hgb.of_arg hc) hargs

/-- **Distinct ground terms are not omega-unifiable.** -/
theorem eq_of_ground_omegaUnifiable {a b : Term sigma nu}
    (ha : Ground a) (hb : Ground b) (h : OmegaUnifiable a b) : a = b := by
  obtain ⟨E, hE, hrel⟩ := h
  exact eq_of_unifClosure_ground hE a ha b hb hrel

/-- The contrapositive, in the form the Theorem 69 extension consumes: the two
new rules cannot overlap each other once the two normal forms are ground and
distinct. -/
theorem not_omegaUnifiable_of_ground_ne {a b : Term sigma nu}
    (ha : Ground a) (hb : Ground b) (hne : a ≠ b) : ¬ OmegaUnifiable a b :=
  fun h => hne (eq_of_ground_omegaUnifiable ha hb h)

/-- Source-semantic form: distinct ground terms do not unify through explicit
potentially infinite substitutions either. -/
theorem eq_of_ground_infiniteOmegaUnifiable {a b : Term sigma nu}
    (ha : Ground a) (hb : Ground b) (h : InfiniteOmegaUnifiable a b) : a = b :=
  eq_of_ground_omegaUnifiable ha hb (omegaUnifiable_of_infinite h)

/-- Source-semantic contrapositive of `eq_of_ground_infiniteOmegaUnifiable`. -/
theorem not_infiniteOmegaUnifiable_of_ground_ne {a b : Term sigma nu}
    (ha : Ground a) (hb : Ground b) (hne : a ≠ b) : ¬ InfiniteOmegaUnifiable a b :=
  fun h => hne (eq_of_ground_infiniteOmegaUnifiable ha hb h)

/-! ## A ground term omega-unifying with a left-hand side is an instance of it -/

/-- **Omega-unification against a ground term collapses to matching.** If a
ground term omega-unifies with `l`, then it is a substitution instance of `l`.

The matcher is read off the certificate: a variable of `l` is sent to the ground
term the certificate relates it to, which the previous theorem shows is unique.
Non-linear `l` is covered by that uniqueness, so repeated variables receive one
and the same image. -/
theorem exists_match_of_ground_omegaUnifiable {s l : Term sigma nu}
    (hs : Ground s) (h : OmegaUnifiable s l) :
    ∃ sb : Subst sigma nu, s = Subst.apply sb l := by
  classical
  obtain ⟨E, hE, hrel⟩ := h
  refine ⟨fun x =>
    if hx : ∃ w : Term sigma nu, Ground w ∧ E (leftCopy w) (Term.var (Sum.inr x))
    then hx.choose else s, ?_⟩
  set sb : Subst sigma nu := fun x =>
    if hx : ∃ w : Term sigma nu, Ground w ∧ E (leftCopy w) (Term.var (Sum.inr x))
    then hx.choose else s with hsb
  -- the matcher sends a certificate-related variable to that unique ground term
  have hpick : ∀ (x : nu) (w : Term sigma nu), Ground w →
      E (leftCopy w) (Term.var (Sum.inr x)) → sb x = w := by
    intro x w hw hrw
    have hex : ∃ v : Term sigma nu, Ground v ∧ E (leftCopy v) (Term.var (Sum.inr x)) :=
      ⟨w, hw, hrw⟩
    have hc := hex.choose_spec
    have hval : sb x = hex.choose := by rw [hsb]; exact dif_pos hex
    rw [hval]
    refine eq_of_unifClosure_ground hE hex.choose hc.1 w hw ?_
    rw [← hw.leftCopy_eq_rightCopy]
    exact hE.trans' hc.2 (hE.symm' hrw)
  have hlist : ∀ (ms : List (Term sigma nu)),
      (∀ m ∈ ms, ∀ w : Term sigma nu, Ground w →
        E (leftCopy w) (rightCopy m) → w = Subst.apply sb m) →
      ∀ ws : List (Term sigma nu), (∀ w ∈ ws, Ground w) →
        List.Forall₂ E (ws.map leftCopy) (ms.map rightCopy) →
        ws = ms.map (Subst.apply sb) := by
    intro ms
    induction ms with
    | nil =>
        intro _ ws _ h
        cases ws with
        | nil => rfl
        | cons w ws => cases h
    | cons m ms ihs =>
        intro hmem ws hgw h
        cases ws with
        | nil => cases h
        | cons w ws =>
            cases h with
            | cons hwm hws =>
                have h1 := hmem m (by simp) w (hgw w (by simp)) hwm
                have h2 := ihs (fun c hc => hmem c (by simp [hc])) ws
                  (fun c hc => hgw c (by simp [hc])) hws
                rw [h1, h2]
                simp
  have key : ∀ (m : Term sigma nu) (w : Term sigma nu), Ground w →
      E (leftCopy w) (rightCopy m) → w = Subst.apply sb m := by
    intro m
    induction m using Term.rec' with
    | hvar x =>
        intro w hw hrw
        have : E (leftCopy w) (Term.var (Sum.inr x)) := hrw
        exact (hpick x w hw this).symm
    | happ f args ih =>
        intro w hw hrw
        cases w with
        | var y => exact (hw y VarOccurs.here).elim
        | app g ws =>
            have hrw' : E (.app g (Term.mapVarList Sum.inl ws))
                (.app f (Term.mapVarList Sum.inr args)) := hrw
            obtain ⟨hgf, hargs⟩ := hE.decomp hrw'
            subst hgf
            rw [Term.mapVarList_eq_map, Term.mapVarList_eq_map] at hargs
            have := hlist args (fun c hc => ih c hc) ws (fun c hc => hw.of_arg hc) hargs
            simp only [Subst.apply_app, Subst.applyList_eq_map]
            exact congrArg _ this
  exact key l s hs hrel

/-- Source-semantic form of matching against a ground term. -/
theorem exists_match_of_ground_infiniteOmegaUnifiable {s l : Term sigma nu}
    (hs : Ground s) (h : InfiniteOmegaUnifiable s l) :
    ∃ sb : Subst sigma nu, s = Subst.apply sb l :=
  exists_match_of_ground_omegaUnifiable hs (omegaUnifiable_of_infinite h)

/-! ## A ground normal form has no omega-unifiable subterm -/

/-- **The positive counterpart of `FreezingNeeded`.** No non-variable subterm of
a ground normal form omega-unifies with any left-hand side of the system: such a
subterm would be an instance of that left-hand side, hence a redex inside a
normal form. -/
theorem subterm_not_omegaUnifiable_of_ground_normalForm {R : TRS sigma nu}
    {t s : Term sigma nu} (hnf : NormalForm R t) (hg : Ground t)
    (hsub : Subterm s t) {rule : Rule sigma nu} (hmem : rule ∈ R) :
    ¬ OmegaUnifiable s rule.lhs := by
  intro hu
  obtain ⟨sb, hmatch⟩ := exists_match_of_ground_omegaUnifiable (hg.subterm hsub) hu
  exact (hnf.subterm hsub) (Subst.apply sb rule.rhs)
    (Step.root ⟨rule, hmem, sb, hmatch, rfl⟩)

/-- Source-semantic version of the normal-form overlap exclusion. -/
theorem subterm_not_infiniteOmegaUnifiable_of_ground_normalForm {R : TRS sigma nu}
    {t s : Term sigma nu} (hnf : NormalForm R t) (hg : Ground t)
    (hsub : Subterm s t) {rule : Rule sigma nu} (hmem : rule ∈ R) :
    ¬ InfiniteOmegaUnifiable s rule.lhs :=
  fun h => subterm_not_omegaUnifiable_of_ground_normalForm hnf hg hsub hmem
    (omegaUnifiable_of_infinite h)

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.Ground
#check @OperatorKO7.Meta.UniqueNormalization.eq_of_ground_omegaUnifiable
#check @OperatorKO7.Meta.UniqueNormalization.not_omegaUnifiable_of_ground_ne
#check @OperatorKO7.Meta.UniqueNormalization.eq_of_ground_infiniteOmegaUnifiable
#check @OperatorKO7.Meta.UniqueNormalization.not_infiniteOmegaUnifiable_of_ground_ne
#check @OperatorKO7.Meta.UniqueNormalization.exists_match_of_ground_omegaUnifiable
#check @OperatorKO7.Meta.UniqueNormalization.exists_match_of_ground_infiniteOmegaUnifiable
#check @OperatorKO7.Meta.UniqueNormalization.subterm_not_omegaUnifiable_of_ground_normalForm
#check @OperatorKO7.Meta.UniqueNormalization.subterm_not_infiniteOmegaUnifiable_of_ground_normalForm

#print axioms OperatorKO7.Meta.UniqueNormalization.Ground.mapVar_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.eq_of_unifClosure_ground
#print axioms OperatorKO7.Meta.UniqueNormalization.eq_of_ground_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.not_omegaUnifiable_of_ground_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.eq_of_ground_infiniteOmegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.not_infiniteOmegaUnifiable_of_ground_ne
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_match_of_ground_omegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.exists_match_of_ground_infiniteOmegaUnifiable
#print axioms OperatorKO7.Meta.UniqueNormalization.subterm_not_omegaUnifiable_of_ground_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.subterm_not_infiniteOmegaUnifiable_of_ground_normalForm
