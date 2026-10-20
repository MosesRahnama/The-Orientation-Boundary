import OperatorKO7.Meta.UniqueNormalization.Section7JointClosure

/-!
# Context closure of tight proof graphs

Maximal tight graphs are constructor-closed. A missing destructor congruence
produces an unequal context-related pair of first-root contracta. Well-founded
descent of right-hand-side destructor symbols resolves every such pair, proves
universality of every equality-maximal graph, and gives transitivity of Down,
conversion equality, constructor compatibility and consistency. Variables and
their substitution instances are unrestricted.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- A context-related pair outside a constructor-closed relation contains a
destructor congruence outside that relation. Both witnesses are subterms of
the fixed endpoints; no rewrite-size hypothesis is used. -/
theorem CT.exists_missing_barRel_of_constructorClosed
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {E : CRel sigma nu}
    (hclosed : ∀ a b, a ∈ A → b ∈ A → hatEq E a b → E a b)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hct : CT E a b) (hmissing : ¬ E a b) :
    ∃ x y, Subterm x a ∧ Subterm y b ∧ x ∈ A ∧ y ∈ A ∧
      barRel E x y ∧ ¬ E x y := by
  classical
  have split : ∀ {xs ys : List (Term (sigma ⊕ sigma) nu)},
      List.Forall₂ (CT E) xs ys →
        List.Forall₂ E xs ys ∨
          ∃ x y, x ∈ xs ∧ y ∈ ys ∧ CT E x y ∧ ¬ E x y := by
    intro xs ys h
    induction h with
    | nil => exact Or.inl List.Forall₂.nil
    | @cons x y xs ys hxy _ ih =>
        by_cases heq : E x y
        · rcases ih with hall | ⟨p, q, hp, hq, hpq, hne⟩
          · exact Or.inl (List.Forall₂.cons heq hall)
          · exact Or.inr ⟨p, q, List.mem_cons_of_mem _ hp,
              List.mem_cons_of_mem _ hq, hpq, hne⟩
        · exact Or.inr ⟨x, y, by simp, by simp, hxy, heq⟩
  have main : ∀ a, a ∈ A → ∀ b, b ∈ A → CT E a b → ¬ E a b →
      ∃ x y, Subterm x a ∧ Subterm y b ∧ x ∈ A ∧ y ∈ A ∧
        barRel E x y ∧ ¬ E x y := by
    intro a
    induction a using Term.rec' with
    | hvar z =>
        intro _ b _ hct hne
        exact (hne (CT.var_left_iff.mp hct)).elim
    | happ f xs ih =>
        intro ha b hb hct hne
        rcases CT.unfold.mp hct with heq | ⟨g, us, ys, _, hleft, rfl, hargs⟩
        · exact (hne heq).elim
        obtain ⟨hfg, hxus⟩ := Term.app.inj hleft
        subst g
        subst us
        rcases split hargs with hall | ⟨p, q, hp, hq, hpq, hneq⟩
        · cases f with
          | inl c =>
              exact (hne (hclosed _ _ ha hb
                (Or.inr ⟨.inl c, xs, ys, ⟨c, rfl⟩, rfl, rfl, hall⟩))).elim
          | inr d =>
              exact ⟨.app (.inr d) xs, .app (.inr d) ys,
                Subterm.refl _, Subterm.refl _, ha, hb,
                ⟨.inr d, xs, ys, ⟨d, rfl⟩, rfl, rfl, hall⟩, hne⟩
        · obtain ⟨x, y, hxp, hyq, hx, hy, hbar, hbad⟩ :=
            ih p hp (hA.arg ha hp) q (hA.arg hb hq) hpq hneq
          exact ⟨x, y, Subterm.arg hp hxp, Subterm.arg hq hyq,
            hx, hy, hbar, hbad⟩
  exact main a ha b hb hct hmissing

/-- Any tight edge is represented when its source has a root-free route to a
graph normal form. Rerooting preserves every old equality. -/
theorem PGraph.TightEqualityComplete.eqvOn_of_nonRootReach_tightEdge
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {a r b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hpath : TightNonRootReach rho a r) (hr : rho.NF r)
    (hedge : TightEdge R (EqvOn A rho.par) a b) :
    EqvOn A rho.par a b := by
  by_contra hne
  obtain ⟨beta, hBeta, hnf, heq, _⟩ := htight.reroot_nonRootReach hpath hr
  have hneBeta : ¬ EqvOn A beta.par a b := fun h => hne ((heq a b).mp h)
  have hedgeBeta : TightEdge R (EqvOn A beta.par) a b :=
    hedge.mono (fun x y h => (heq x y).mpr h)
  obtain ⟨gamma, hGamma, hBetaGamma, _, hnew⟩ :=
    hBeta.extend_one hA hR ha hb hnf hneBeta hedgeBeta
  have hext : rho.EqualityExtends gamma := by
    intro x y h
    exact hBetaGamma ((heq x y).mpr h)
  exact hne (hmax gamma hGamma hext hnew)

/-- Equality-maximal tight graphs are closed under constructor congruence.
No overlap or destructor-closure premise is needed. -/
theorem PGraph.TightEqualityComplete.constructorClosed
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hhat : hatEq (EqvOn A rho.par) a b) : EqvOn A rho.par a b := by
  obtain ⟨s, has, hsnf⟩ := exists_root rho.term a
  have hs : s ∈ A := rho.mem_of_reach_right ha has
  have hasEq : EqvOn A rho.par a s := EqvOn.of_reach ha hs has
  have hca : ConTopped a := ConTopped.of_hatEq hhat
  have hcs : ConTopped s :=
    conTopped_of_reach hR (fun h => rho.grey h) has hca
  have hasHat : hatEq (EqvOn A rho.par) a s :=
    rho.constructorCompatible hA hR hca hcs hasEq
  have hsbHat : hatEq (EqvOn A rho.par) s b :=
    hatEq.trans (E := EqvOn A rho.par) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
      (hatEq.symm (E := EqvOn A rho.par) (fun _ _ h => EqvOn.symm h) hasHat) hhat
  have hsb : EqvOn A rho.par s b :=
    hmax.eqvOn_of_nf_tightEdge hA hR htight hs hb hsnf
      (Or.inr (Or.inr hsbHat))
  exact EqvOn.trans hasEq hsb

/-- A destructor-headed node has a root-free route to a normal form or a
root-free route to a first root contraction. -/
theorem PGraph.Tight.destructorRoute
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R} (htight : rho.Tight)
    {a : Term (sigma ⊕ sigma) nu} (ha : a ∈ A)
    (hshape : ∃ d args, a = .app (.inr d) args) :
    (∃ r, TightNonRootReach rho a r ∧ rho.NF r) ∨
      (∃ x y, TightNonRootReach rho a x ∧ rho.par x = some y ∧
        rootStep R x y ∧ barRel (EqvOn A rho.par) a x) := by
  rcases (rho.normalRoot_spec a).1.tightNonRoot_or_firstRoot with hfree |
      ⟨x, y, hprefix, hxy, hroot⟩
  · exact Or.inl ⟨rho.normalRoot a, hfree, (rho.normalRoot_spec a).2⟩
  · exact Or.inr ⟨x, y, hprefix, hxy, hroot,
      hprefix.barRel_eqvOn hA htight ha hshape⟩

/-- Every missing destructor congruence has two actual first-root paths. Their
contracta are related by context closure and are not graph-equal. -/
theorem PGraph.TightEqualityComplete.missing_barRel_has_root_residual
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hbar : barRel (EqvOn A rho.par) a b) (hmissing : ¬ EqvOn A rho.par a b) :
    ∃ x y z w, TightNonRootReach rho a x ∧ rho.par x = some y ∧
      rootStep R x y ∧ TightNonRootReach rho b z ∧ rho.par z = some w ∧
      rootStep R z w ∧ barRel (EqvOn A rho.par) x z ∧
      CT (EqvOn A rho.par) y w ∧ ¬ EqvOn A rho.par y w := by
  have haShape : ∃ d args, a = .app (.inr d) args := by
    obtain ⟨f, xs, ys, ⟨d, hfd⟩, hax, _, _⟩ := hbar
    exact ⟨d, xs, hax.trans (congrArg (fun g => Term.app g xs) hfd)⟩
  have hbShape : ∃ d args, b = .app (.inr d) args := by
    obtain ⟨f, xs, ys, ⟨d, hfd⟩, _, hby, _⟩ := hbar
    exact ⟨d, ys, hby.trans (congrArg (fun g => Term.app g ys) hfd)⟩
  have hbarBA : barRel (EqvOn A rho.par) b a :=
    tildeOn_flip (tildeOn_mono (fun _ _ h => EqvOn.symm h) hbar)
  rcases htight.destructorRoute hA ha haShape with ⟨r, har, hr⟩ |
      ⟨x, y, hax, hxy, hrootXY, hbarAX⟩
  · exact (hmissing (hmax.eqvOn_of_nonRootReach_tightEdge hA hR htight ha hb
      har hr (Or.inr (Or.inl hbar)))).elim
  rcases htight.destructorRoute hA hb hbShape with ⟨r, hbr, hr⟩ |
      ⟨z, w, hbz, hzw, hrootZW, hbarBZ⟩
  · exact (hmissing (EqvOn.symm
      (hmax.eqvOn_of_nonRootReach_tightEdge hA hR htight hb ha
        hbr hr (Or.inr (Or.inl hbarBA))))).elim
  have hbarXA : barRel (EqvOn A rho.par) x a :=
    tildeOn_flip (tildeOn_mono (fun _ _ h => EqvOn.symm h) hbarAX)
  have hbarXZ : barRel (EqvOn A rho.par) x z :=
    barRel_eqvOn_trans (barRel_eqvOn_trans hbarXA hbar) hbarBZ
  have hres : CT (EqvOn A rho.par) y w :=
    thm37 (E := EqvOn A rho.par) hR hstrong (fun _ _ h => EqvOn.symm h)
      (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
      (rho.constructorCompatible_eqvOn hA hR) hrootXY hbarXZ hrootZW
  have hay : EqvOn A rho.par a y :=
    EqvOn.of_reach ha (rho.mem_edge hxy).2
      (hax.toReach.trans (Reach.head hxy (Reach.refl y)))
  have hbw : EqvOn A rho.par b w :=
    EqvOn.of_reach hb (rho.mem_edge hzw).2
      (hbz.toReach.trans (Reach.head hzw (Reach.refl w)))
  refine ⟨x, y, z, w, hax, hxy, hrootXY, hbz, hzw, hrootZW, hbarXZ, hres, ?_⟩
  intro hyw
  exact hmissing (EqvOn.trans (EqvOn.trans hay hyw) (EqvOn.symm hbw))

/-- After constructor closure, signature-closure failure is exactly a missing
destructor congruence between members of the coalgebra. -/
theorem PGraph.TightEqualityComplete.not_sigmaClosedOn_iff_missing_barRel
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight) :
    ¬ SigmaClosedOn A (EqvOn A rho.par) ↔
      ∃ a b, a ∈ A ∧ b ∈ A ∧ barRel (EqvOn A rho.par) a b ∧
        ¬ EqvOn A rho.par a b := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro a b ha hb htilde
    rcases hatRel_or_barRel_of_tildeAll htilde with hhat | hbar
    · exact hmax.constructorClosed hA hR htight ha hb (Or.inr hhat)
    · by_contra hmissing
      exact hnone ⟨a, b, ha, hb, hbar, hmissing⟩
  · rintro ⟨a, b, ha, hb, hbar, hmissing⟩ hclosed
    exact hmissing (hclosed a b ha hb (tildeAll_of_barRel hbar))

/-- A missing destructor congruence produces another missing destructor
congruence inside the two first-root contracta. The subterm bound is on those
contracta, not on the original sources. -/
theorem PGraph.TightEqualityComplete.missing_barRel_has_subterm_residual
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hbar : barRel (EqvOn A rho.par) a b) (hmissing : ¬ EqvOn A rho.par a b) :
    ∃ x y z w u v, TightNonRootReach rho a x ∧ rho.par x = some y ∧
      rootStep R x y ∧ TightNonRootReach rho b z ∧ rho.par z = some w ∧
      rootStep R z w ∧ Subterm u y ∧ Subterm v w ∧ u ∈ A ∧ v ∈ A ∧
      barRel (EqvOn A rho.par) u v ∧ ¬ EqvOn A rho.par u v := by
  obtain ⟨x, y, z, w, hax, hxy, hrootXY, hbz, hzw, hrootZW, _, hct, hne⟩ :=
    hmax.missing_barRel_has_root_residual hA hR hstrong htight ha hb hbar hmissing
  obtain ⟨u, v, huy, hvw, hu, hv, huv, hneUV⟩ :=
    CT.exists_missing_barRel_of_constructorClosed hA
      (fun _ _ hx hy hh => hmax.constructorClosed hA hR htight hx hy hh)
      (rho.mem_edge hxy).2 (rho.mem_edge hzw).2 hct hne
  exact ⟨x, y, z, w, u, v, hax, hxy, hrootXY, hbz, hzw, hrootZW,
    huy, hvw, hu, hv, huv, hneUV⟩

/-! ## Syntactic rule dependencies -/

/-- Every function symbol in a term satisfies the stated predicate. Variables
impose no condition on their later substitution instances. -/
inductive SymbolsSatisfy (P : sigma ⊕ sigma → Prop) :
    Term (sigma ⊕ sigma) nu → Prop
  | var (x : nu) : SymbolsSatisfy P (.var x)
  | app {f : sigma ⊕ sigma} {args : List (Term (sigma ⊕ sigma) nu)} :
      P f → (∀ a ∈ args, SymbolsSatisfy P a) → SymbolsSatisfy P (.app f args)

theorem SymbolsSatisfy.app_iff {P : sigma ⊕ sigma → Prop}
    {f : sigma ⊕ sigma} {args : List (Term (sigma ⊕ sigma) nu)} :
    SymbolsSatisfy P (.app f args) ↔ P f ∧ ∀ a ∈ args, SymbolsSatisfy P a := by
  constructor
  · intro h; cases h with | app hf hs => exact ⟨hf, hs⟩
  · rintro ⟨hf, hs⟩; exact .app hf hs

/-- Substitution cannot remove a function symbol already present in a term. -/
theorem SymbolsSatisfy.of_apply {P : sigma ⊕ sigma → Prop}
    {s : Subst (sigma ⊕ sigma) nu} {t : Term (sigma ⊕ sigma) nu}
    (h : SymbolsSatisfy P (Subst.apply s t)) : SymbolsSatisfy P t := by
  induction t using Term.rec' with
  | hvar x => exact .var x
  | happ f args ih =>
      simp only [Subst.apply_app, Subst.applyList_eq_map] at h
      obtain ⟨hf, hs⟩ := SymbolsSatisfy.app_iff.mp h
      exact .app hf (fun a ha => ih a ha (hs _ (List.mem_map_of_mem ha)))

/-- A variable occurrence places its entire substitution instance inside the
substituted term, so that instance satisfies the same symbol predicate. -/
theorem SymbolsSatisfy.at_variable {P : sigma ⊕ sigma → Prop}
    {s : Subst (sigma ⊕ sigma) nu} {t : Term (sigma ⊕ sigma) nu}
    (h : SymbolsSatisfy P (Subst.apply s t)) {x : nu} (hx : VarOccurs x t) :
    SymbolsSatisfy P (s x) := by
  induction hx with
  | here => exact h
  | @arg f args a ha _ ih =>
      apply ih
      simp only [Subst.apply_app, Subst.applyList_eq_map] at h
      exact (SymbolsSatisfy.app_iff.mp h).2 _ (List.mem_map_of_mem ha)

/-- Congruence at the symbols of a pattern suffices to relate its substitution
instances. Closure at symbols inside substituted variables is unnecessary. -/
theorem SymbolsSatisfy.relates_instances
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {P : sigma ⊕ sigma → Prop} {E : CRel sigma nu}
    (hclosed : ∀ f as bs, P f → Term.app f as ∈ A → Term.app f bs ∈ A →
      List.Forall₂ E as bs → E (.app f as) (.app f bs))
    {s t : Subst (sigma ⊕ sigma) nu} {p : Term (sigma ⊕ sigma) nu}
    (hp : SymbolsSatisfy P p)
    (hvars : ∀ x, VarOccurs x p → E (s x) (t x))
    (hs : Subst.apply s p ∈ A) (ht : Subst.apply t p ∈ A) :
    E (Subst.apply s p) (Subst.apply t p) := by
  induction p using Term.rec' with
  | hvar x => exact hvars x .here
  | happ f args ih =>
      obtain ⟨hf, hargs⟩ := SymbolsSatisfy.app_iff.mp hp
      simp only [Subst.apply_app, Subst.applyList_eq_map] at hs ht ⊢
      apply hclosed f _ _ hf hs ht
      apply forall₂_of_pointwise
      intro a ha
      exact ih a ha (hargs a ha) (fun x hx => hvars x (.arg ha hx))
        (hA.arg hs (List.mem_map_of_mem ha))
        (hA.arg ht (List.mem_map_of_mem ha))

/-- Constructor symbols are unrestricted; each right-hand-side destructor is
strictly below the rule's left-hand-side destructor in the supplied relation. -/
def RhsSymbolsDescend (R : TRS (sigma ⊕ sigma) nu) (lt : sigma → sigma → Prop) : Prop :=
  ∀ rule ∈ R, ∀ d ps, rule.lhs = .app (.inr d) ps →
    SymbolsSatisfy (fun f => match f with | .inl _ => True | .inr e => lt e d) rule.rhs

/-- Syntactic descent resolves a semantic critical pair using only congruence
at constructors and strictly lower destructor symbols. -/
theorem RhsSymbolsDescend.semantic_pair
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt)
    {E : CRel sigma nu} (hsymm : ∀ a b, E a b → E b a)
    (htrans : ∀ a b c, E a b → E b c → E a c) (hCC : ConstructorCompatible E)
    {d : sigma}
    (hclosed : ∀ f as bs,
      (match f with | .inl _ => True | .inr e => lt e d) →
      Term.app f as ∈ A → Term.app f bs ∈ A → List.Forall₂ E as bs →
      E (.app f as) (.app f bs))
    {as bs : List (Term (sigma ⊕ sigma) nu)} {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A)
    (hleft : rootStep R (.app (.inr d) as) a)
    (hargs : List.Forall₂ E as bs)
    (hright : rootStep R (.app (.inr d) bs) b) : E a b := by
  obtain ⟨rule₁, hm₁, s, hsrc₁, htgt₁⟩ := hleft
  obtain ⟨rule₂, hm₂, t, hsrc₂, htgt₂⟩ := hright
  obtain ⟨F₁, ps, hlhs₁, hps⟩ := hR rule₁ hm₁
  obtain ⟨F₂, qs, hlhs₂, hqs⟩ := hR rule₂ hm₂
  rw [hlhs₁] at hsrc₁
  rw [hlhs₂] at hsrc₂
  simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq] at hsrc₁ hsrc₂
  obtain ⟨hF₁, rfl⟩ := hsrc₁
  obtain ⟨hF₂, rfl⟩ := hsrc₂
  have hF₁' : F₁ = d := by simpa using hF₁.symm
  have hF₂' : F₂ = d := by simpa using hF₂.symm
  subst F₁
  subst F₂
  have hOU : OmegaUnifiable rule₁.lhs rule₂.lhs := by
    rw [hlhs₁, hlhs₂]
    exact lemma36 hsymm htrans hCC hps hqs hargs
  obtain ⟨g, hgvar⟩ := hstrong.2 rule₁ hm₁ rule₂ hm₂ hOU
  have hsupp₁ := hdesc rule₁ hm₁ d ps hlhs₁
  have hgr : SymbolsSatisfy
      (fun f => match f with | .inl _ => True | .inr e => lt e d) g.gr := by
    apply SymbolsSatisfy.of_apply (s := g.s₁)
    rw [g.apply_gr₁]
    exact hsupp₁
  have hga : a = Subst.apply (Subst.comp s g.s₁) g.gr := by
    rw [Subst.apply_comp, g.apply_gr₁, htgt₁]
  have hgb : b = Subst.apply (Subst.comp t g.s₂) g.gr := by
    rw [Subst.apply_comp, g.apply_gr₂, htgt₂]
  rw [hga] at ha
  rw [hgb] at hb
  rw [hga, hgb]
  apply hgr.relates_instances hA hclosed ?_ ha hb
  intro x hx
  have hgl₁ := g.apply_gl₁
  have hgl₂ := g.apply_gl₂
  cases hgl : g.gl with
  | var y =>
      have hxy : x = y := by
        have hocc := hgvar x hx
        rw [hgl] at hocc
        cases hocc with | here => rfl
      subst y
      rw [hgl] at hgl₁
      simp only [Subst.apply_var] at hgl₁
      have hwhole : SymbolsSatisfy
          (fun f => match f with | .inl _ => True | .inr e => lt e d)
          (Subst.apply g.s₁ g.gr) := by
        rw [g.apply_gr₁]
        exact hsupp₁
      have hself := hwhole.at_variable hx
      rw [hgl₁, hlhs₁] at hself
      have hirr : ∀ e, ¬ lt e e := by
        intro e
        induction hwf.apply e with
        | intro e _ ih => intro he; exact ih e he he
      exact (hirr d (SymbolsSatisfy.app_iff.mp hself).1).elim
  | app G rs =>
      rw [hgl, hlhs₁] at hgl₁
      rw [hgl, hlhs₂] at hgl₂
      simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq] at hgl₁ hgl₂
      obtain ⟨hG, hrs₁⟩ := hgl₁
      obtain ⟨_, hrs₂⟩ := hgl₂
      have hrsCon : ∀ p ∈ rs, ConOnly p := by
        intro p hp
        apply ConOnly.of_apply (s := g.s₁)
        exact hps _ (by rw [← hrs₁]; exact List.mem_map_of_mem hp)
      have hvar : VarOccurs x (.app (.inr d) rs) := by
        have hocc := hgvar x hx
        rw [hgl, hG] at hocc
        exact hocc
      have hmapl : rs.map (Subst.apply (Subst.comp s g.s₁)) = ps.map (Subst.apply s) := by
        rw [← hrs₁, List.map_map]
        exact List.map_congr_left (fun q _ => Subst.apply_comp s g.s₁ q)
      have hmapr : rs.map (Subst.apply (Subst.comp t g.s₂)) = qs.map (Subst.apply t) := by
        rw [← hrs₂, List.map_map]
        exact List.map_congr_left (fun q _ => Subst.apply_comp t g.s₂ q)
      have haligned : List.Forall₂ E
          (rs.map (Subst.apply (Subst.comp s g.s₁)))
          (rs.map (Subst.apply (Subst.comp t g.s₂))) := by
        rw [hmapl, hmapr]
        exact hargs
      obtain ⟨p, hp, hxp⟩ := hvar.app_inv
      exact lemma33 hCC p (hrsCon p hp) (pointwise_of_forall₂ haligned p hp) x hxp

/-- Well-founded syntactic destructor dependencies imply full local signature
closure on every maximal tight graph. The graph and its equations are fixed
throughout the induction; no bound on the sizes of substitution instances is used. -/
theorem PGraph.TightEqualityComplete.sigmaClosedOn_of_rhsSymbolsDescend
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight) :
    SigmaClosedOn A (EqvOn A rho.par) := by
  have closeD : ∀ d as bs,
      Term.app (.inr d) as ∈ A → Term.app (.inr d) bs ∈ A →
      List.Forall₂ (EqvOn A rho.par) as bs →
      EqvOn A rho.par (.app (.inr d) as) (.app (.inr d) bs) := by
    intro d
    induction d using hwf.induction with
    | h d ih =>
        intro as bs ha hb hargs
        by_contra hmissing
        have hbar : barRel (EqvOn A rho.par) (.app (.inr d) as) (.app (.inr d) bs) :=
          ⟨.inr d, as, bs, ⟨d, rfl⟩, rfl, rfl, hargs⟩
        obtain ⟨x, y, z, w, hax, hxy, hrootXY, hbz, hzw, hrootZW, hbarXZ, _, hne⟩ :=
          hmax.missing_barRel_has_root_residual hA hR hstrong htight ha hb hbar hmissing
        have hxShape : ∃ xs, x = Term.app (.inr d) xs := by
          obtain ⟨f, us, vs, _, heq, hx, _⟩ :=
            hax.barRel_eqvOn hA htight ha ⟨d, as, rfl⟩
          have hf := (Term.app.inj heq).1
          exact ⟨vs, hx.trans (congrArg (fun g => Term.app g vs) hf.symm)⟩
        have hzShape : ∃ zs, z = Term.app (.inr d) zs := by
          obtain ⟨f, us, vs, _, heq, hz, _⟩ :=
            hbz.barRel_eqvOn hA htight hb ⟨d, bs, rfl⟩
          have hf := (Term.app.inj heq).1
          exact ⟨vs, hz.trans (congrArg (fun g => Term.app g vs) hf.symm)⟩
        obtain ⟨xs, rfl⟩ := hxShape
        obtain ⟨zs, rfl⟩ := hzShape
        obtain ⟨f, us, vs, _, hx, hz, hrel⟩ := hbarXZ
        have hxu := (Term.app.inj hx).2
        have hzv := (Term.app.inj hz).2
        subst us
        subst vs
        apply hne
        apply hdesc.semantic_pair hA hR hstrong hwf (E := EqvOn A rho.par)
          (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
          (rho.constructorCompatible_eqvOn hA hR) (d := d) ?_
          (rho.mem_edge hxy).2 (rho.mem_edge hzw).2 hrootXY hrel hrootZW
        intro f us vs hf hu hv hall
        cases f with
        | inl c =>
            exact hmax.constructorClosed hA hR htight hu hv
              (Or.inr ⟨.inl c, us, vs, ⟨c, rfl⟩, rfl, rfl, hall⟩)
        | inr e => exact ih e hf us vs hu hv hall
  rintro a b ha hb ⟨f, as, bs, _, rfl, rfl, hargs⟩
  cases f with
  | inl c =>
      exact hmax.constructorClosed hA hR htight ha hb
        (Or.inr ⟨.inl c, as, bs, ⟨c, rfl⟩, rfl, rfl, hargs⟩)
  | inr d => exact closeD d as bs ha hb hargs

/-- Every maximal tight graph of a syntactically descending constructor system
represents the full relativized invariant on its finite carrier. -/
theorem PGraph.TightEqualityComplete.universal_of_rhsSymbolsDescend
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight) :
    rho.Universal :=
  hmax.universal_of_sigmaClosedOn hA hR hstrong htight
    (hmax.sigmaClosedOn_of_rhsSymbolsDescend hA hR hstrong hwf hdesc htight)

/-- One finite graph simultaneously represents root steps, every constructor
and destructor congruence, and the full relativized invariant. -/
theorem exists_tight_universal_of_rhsSymbolsDescend
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt) :
    ∃ rho : PGraph A R, rho.Tight ∧ rho.TightEqualityComplete ∧
      RootStepsRepresented A R rho ∧ SigmaClosedOn A (EqvOn A rho.par) ∧ rho.Universal := by
  obtain ⟨rho, htight, hmax⟩ := exists_tightEqualityComplete A R
  have hclosed := hmax.sigmaClosedOn_of_rhsSymbolsDescend hA hR hstrong hwf hdesc htight
  exact ⟨rho, htight, hmax,
    hmax.rootStepsRepresented_of_sigmaClosedOn hA hR hstrong htight hclosed,
    hclosed, hmax.universal_of_sigmaClosedOn hA hR hstrong htight hclosed⟩

/-- Constructor-only patterns satisfy every symbol predicate that accepts
constructor symbols, independently of its destructor cases. -/
theorem SymbolsSatisfy.of_conOnly {P : sigma ⊕ sigma → Prop}
    (hP : ∀ c, P (.inl c)) {t : Term (sigma ⊕ sigma) nu} (h : ConOnly t) :
    SymbolsSatisfy P t := by
  induction h with
  | var x => exact .var x
  | app c args _ ih => exact .app (hP c) ih

/-- Constructor-only right-hand sides discharge the syntactic dependency
condition with the empty relation. Variables remain unrestricted. -/
theorem RhsSymbolsDescend.of_constructor_rhs {R : TRS (sigma ⊕ sigma) nu}
    (hrhs : ∀ rule ∈ R, ConOnly rule.rhs) :
    RhsSymbolsDescend R (fun _ _ => False) := by
  intro rule hr d ps _
  exact SymbolsSatisfy.of_conOnly (fun _ => True.intro) (hrhs rule hr)

/-- Constructor-only right-hand sides produce one fully closed graph over
every finite coalgebra, with no chosen order or graph-closure premise. -/
theorem exists_tight_universal_of_constructor_rhs
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (hrhs : ∀ rule ∈ R, ConOnly rule.rhs) :
    ∃ rho : PGraph A R, rho.Tight ∧ rho.TightEqualityComplete ∧
      RootStepsRepresented A R rho ∧ SigmaClosedOn A (EqvOn A rho.par) ∧ rho.Universal := by
  have hwf : WellFounded (fun _ _ : sigma => False) :=
    ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  exact exists_tight_universal_of_rhsSymbolsDescend hA hR hstrong hwf
    (RhsSymbolsDescend.of_constructor_rhs hrhs)

/-- Syntactic descent proves transitivity of the actual relativized invariant,
not just transitivity of a separately constructed graph relation. -/
theorem DownOn.trans_of_rhsSymbolsDescend
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt)
    {a b c : Term (sigma ⊕ sigma) nu} (hab : DownOn A R a b) (hbc : DownOn A R b c) :
    DownOn A R a c := by
  obtain ⟨rho, _, _, _, _, huniv⟩ :=
    exists_tight_universal_of_rhsSymbolsDescend hA hR hstrong hwf hdesc
  exact (huniv a c).mp (EqvOn.trans ((huniv a b).mpr hab) ((huniv b c).mpr hbc))

/-- Finite support removes the coalgebra restriction from transitivity. The
signature, variable type, rule set, and substitution instances are arbitrary. -/
theorem Down.trans_of_rhsSymbolsDescend
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt) :
    ∀ a b c, Down R a b → Down R b c → Down R a c :=
  Down.trans_of_finite_coalgebras (fun _ hA _ _ _ hab hbc =>
    DownOn.trans_of_rhsSymbolsDescend hA hR hstrong hwf hdesc hab hbc)

/-- Conversion equals the inductively defined invariant for syntactically
descending constructor systems; finite supports are constructed by the proof. -/
theorem conv_eq_down_of_rhsSymbolsDescend
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt)
    (a b : Term (sigma ⊕ sigma) nu) : conv R a b ↔ Down R a b :=
  conv_eq_down (Down.trans_of_rhsSymbolsDescend hR hstrong hwf hdesc) a b

/-! ## All maximal graphs and the conversion relation -/

/-- A universal graph represents every equation of every graph on its carrier. -/
theorem PGraph.Universal.extends_from
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {beta : PGraph A R} (hbeta : beta.Universal) (rho : PGraph A R) :
    rho.EqualityExtends beta := by
  intro a b hab
  exact (hbeta a b).mpr (rho.sub hab)

/-- Once one universal graph exists, equality maximality implies universality
for every graph on the same carrier, without tightness or targeting. -/
theorem PGraph.EqualityComplete.universal_of_exists_universal
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hmax : rho.EqualityComplete)
    (hex : ∃ beta : PGraph A R, beta.Universal) : rho.Universal := by
  obtain ⟨beta, hbeta⟩ := hex
  intro a b
  exact ⟨fun h => rho.sub h,
    fun h => hmax beta (hbeta.extends_from rho) ((hbeta a b).mpr h)⟩

/-- Syntactic descent makes every equality-maximal proof graph universal;
the input graph need not satisfy the tight-edge restriction. -/
theorem PGraph.EqualityComplete.universal_of_rhsSymbolsDescend
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt)
    {rho : PGraph A R} (hmax : rho.EqualityComplete) : rho.Universal := by
  obtain ⟨beta, _, _, _, _, hbeta⟩ :=
    exists_tight_universal_of_rhsSymbolsDescend hA hR hstrong hwf hdesc
  exact hmax.universal_of_exists_universal ⟨beta, hbeta⟩

/-- Every initial graph has a tight universal replacement preserving all its
equations. Parent edges may change; no parent-extension claim is made. -/
theorem PGraph.exists_tightUniversal_extension_of_rhsSymbolsDescend
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt)
    (rho : PGraph A R) :
    ∃ beta : PGraph A R, rho.EqualityExtends beta ∧ beta.Tight ∧
      beta.TightEqualityComplete ∧ RootStepsRepresented A R beta ∧
      SigmaClosedOn A (EqvOn A beta.par) ∧ beta.Universal := by
  obtain ⟨beta, htight, hmax, hroot, hclosed, huniv⟩ :=
    exists_tight_universal_of_rhsSymbolsDescend hA hR hstrong hwf hdesc
  exact ⟨beta, huniv.extends_from rho, htight, hmax, hroot, hclosed, huniv⟩

/-- Conversion preserves constructor heads and relates their arguments
componentwise for the syntactically descending class. -/
theorem constructorCompatible_conv_of_rhsSymbolsDescend
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt) :
    ConstructorCompatible (conv R) := by
  intro a b hca hcb hab
  have hdown := (conv_eq_down_of_rhsSymbolsDescend hR hstrong hwf hdesc a b).mp hab
  rcases Down.constructorCompatible hR a b hca hcb hdown with
      hvar | ⟨f, xs, ys, hax, hby, hall⟩
  · exact Or.inl hvar
  · exact Or.inr ⟨f, xs, ys, hax, hby,
      forall₂_mono (fun _ _ h => Down.to_conv h) hall⟩

/-- No conversion identifies distinct variables in the descending class.
The variable type is arbitrary, with no infinity or cardinality premise. -/
theorem consistent_of_rhsSymbolsDescend
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {lt : sigma → sigma → Prop} (hwf : WellFounded lt) (hdesc : RhsSymbolsDescend R lt) :
    Consistent R := by
  intro x y hxy
  exact Down.consistent hR
    ((conv_eq_down_of_rhsSymbolsDescend hR hstrong hwf hdesc _ _).mp hxy)

/-- Constructor-only right-hand sides give consistency without an order or
graph-closure premise. -/
theorem consistent_of_constructor_rhs
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (hrhs : ∀ rule ∈ R, ConOnly rule.rhs) : Consistent R := by
  have hwf : WellFounded (fun _ _ : sigma => False) :=
    ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  exact consistent_of_rhsSymbolsDescend hR hstrong hwf
    (RhsSymbolsDescend.of_constructor_rhs hrhs)

/-! ## Constructor-slice certification -/

/-- Constructor-headed parent paths have constructor congruence endpoints
before full proof-graph soundness has been established. -/
theorem hatEq_of_reach_of_selfGrey
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    {a s : Term (sigma ⊕ sigma) nu} (hpath : Reach g a s)
    (ha : a ∈ A) (hca : ConTopped a) : hatEq (EqvOn A g) a s := by
  induction hpath with
  | refl a =>
      rcases hca with ⟨x, rfl⟩ | ⟨c, args, rfl⟩
      · exact Or.inl ⟨x, rfl, rfl⟩
      · exact Or.inr ⟨.inl c, args, args, ⟨c, rfl⟩, rfl, rfl,
          forall₂_self_of (fun x hx => EqvOn.refl (hA.arg ha hx))⟩
  | head hab _ ih =>
      have hhat := hatEq_of_grey_of_conTopped hR hca (hgrey hab)
      exact hatEq.trans (E := EqvOn A g) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂) hhat
        (ih (hmem hab).2 (ConTopped.of_hatEq_right hhat))

/-- The equality of a self-grey parent function is constructor-compatible.
The proof uses neither invariant soundness nor parent termination. -/
theorem constructorCompatible_eqvOn_of_selfGrey
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b) :
    ConstructorCompatible (EqvOn A g) := by
  intro a b hca hcb hab
  obtain ⟨ha, hb, s, has, hbs⟩ := hab
  have hleft := hatEq_of_reach_of_selfGrey hA hR hmem hgrey has ha hca
  have hright := hatEq_of_reach_of_selfGrey hA hR hmem hgrey hbs hb hcb
  have hhat : hatEq (EqvOn A g) a b :=
    hatEq.trans (E := EqvOn A g) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂) hleft
      (hatEq.symm (E := EqvOn A g) (fun _ _ h => EqvOn.symm h) hright)
  rcases hhat with hvar | ⟨f, xs, ys, ⟨c, hfc⟩, hax, hby, hall⟩
  · exact Or.inl hvar
  · subst f
    exact Or.inr ⟨c, xs, ys, hax, hby, hall⟩

/-- For a self-grey parent function, soundness on constructor-topped equality
pairs implies soundness on every equality pair. Finite valleys suffice;
termination, coalgebra closure and overlap assumptions are unnecessary. -/
theorem eqvOn_downOn_of_constructorSlice
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (hR : ConstructorRules R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    (hslice : ∀ {a b}, ConTopped a → ConTopped b →
      EqvOn A g a b → DownOn A R a b)
    {a b : Term (sigma ⊕ sigma) nu} (hab : EqvOn A g a b) :
    DownOn A R a b := by
  have reach_sound : ∀ {x y}, Reach g x y → x ∈ A → y ∈ A → DownOn A R x y := by
    intro x y hxy
    induction hxy with
    | refl x => intro hx _; exact DownOn.refl hx
    | @head x c y hxc hcy ih =>
        intro hx hy
        rcases hgrey hxc with hroot | hbar | hhat
        · exact downOn_peel hx (hmem hxc).2 (Or.inl hroot) (ih (hmem hxc).2 hy)
        · exact downOn_peel hx (hmem hxc).2 (Or.inr hbar) (ih (hmem hxc).2 hy)
        · have hcx : ConTopped x := ConTopped.of_hatEq hhat
          exact hslice hcx (conTopped_of_reach hR hgrey (Reach.head hxc hcy) hcx)
            (EqvOn.of_reach hx hy (Reach.head hxc hcy))
  have con_valley : ∀ {x y s}, Reach g y s → x ∈ A → y ∈ A →
      ConTopped x → Reach g x s → DownOn A R x y := by
    intro x y s hys
    induction hys with
    | refl s =>
        intro hx hs hcx hxs
        exact hslice hcx (conTopped_of_reach hR hgrey hxs hcx)
          (EqvOn.of_reach hx hs hxs)
    | @head y c s hyc hcs ih =>
        intro hx hy hcx hxs
        rcases hgrey hyc with hroot | hbar | hhat
        · exact DownOn.symm (downOn_peel hy (hmem hyc).2 (Or.inl hroot)
            (DownOn.symm (ih hx (hmem hyc).2 hcx hxs)))
        · exact DownOn.symm (downOn_peel hy (hmem hyc).2 (Or.inr hbar)
            (DownOn.symm (ih hx (hmem hyc).2 hcx hxs)))
        · exact hslice hcx (ConTopped.of_hatEq hhat)
            ⟨hx, hy, s, hxs, Reach.head hyc hcs⟩
  obtain ⟨ha, hb, s, has, hbs⟩ := hab
  induction has with
  | refl s => exact DownOn.symm (reach_sound hbs hb ha)
  | @head a c s hac hcs ih =>
      rcases hgrey hac with hroot | hbar | hhat
      · exact downOn_peel ha (hmem hac).2 (Or.inl hroot) (ih (hmem hac).2 hbs)
      · exact downOn_peel ha (hmem hac).2 (Or.inr hbar) (ih (hmem hac).2 hbs)
      · exact con_valley hbs ha hb (ConTopped.of_hatEq hhat) (Reach.head hac hcs)

/-- Constructor-slice soundness is equivalent to full equality soundness for
any self-grey parent function of a constructor system. -/
theorem eqvOn_downOn_iff_constructorSlice
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (hR : ConstructorRules R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b) :
    (∀ {a b}, EqvOn A g a b → DownOn A R a b) ↔
      (∀ {a b}, ConTopped a → ConTopped b → EqvOn A g a b → DownOn A R a b) := by
  constructor
  · intro h _ _ _ _ hab; exact h hab
  · intro h _ _ hab; exact eqvOn_downOn_of_constructorSlice hR hmem hgrey h hab

/-- One equality pair needs soundness only for constructor pairs reached from
its own two endpoints. No other equality class is a premise. -/
theorem eqvOn_downOn_of_reachableConstructorSlice
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (hR : ConstructorRules R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    {a b : Term (sigma ⊕ sigma) nu} (hab : EqvOn A g a b)
    (hslice : ∀ {x y}, Reach g a x → Reach g b y → ConTopped x → ConTopped y →
      EqvOn A g x y → DownOn A R x y) : DownOn A R a b := by
  have reach_sound : ∀ {x y}, Reach g x y → x ∈ A → y ∈ A →
      (∀ {p q}, Reach g x p → Reach g y q → ConTopped p → ConTopped q →
        EqvOn A g p q → DownOn A R p q) → DownOn A R x y := by
    intro x y hxy
    induction hxy with
    | refl x => intro hx _ _; exact DownOn.refl hx
    | @head x c y hxc hcy ih =>
        intro hx hy hs
        have hc : c ∈ A := (hmem hxc).2
        have htail : DownOn A R c y := ih hc hy
          (fun hp hq hcp hcq hpq => hs (Reach.head hxc hp) hq hcp hcq hpq)
        rcases hgrey hxc with hroot | hbar | hhat
        · exact downOn_peel hx hc (Or.inl hroot) htail
        · exact downOn_peel hx hc (Or.inr hbar) htail
        · have hcx : ConTopped x := ConTopped.of_hatEq hhat
          exact hs (Reach.refl x) (Reach.refl y) hcx
            (conTopped_of_reach hR hgrey (Reach.head hxc hcy) hcx)
            (EqvOn.of_reach hx hy (Reach.head hxc hcy))
  have con_valley : ∀ {x y s}, Reach g y s → x ∈ A → y ∈ A →
      ConTopped x → Reach g x s →
      (∀ {p q}, Reach g x p → Reach g y q → ConTopped p → ConTopped q →
        EqvOn A g p q → DownOn A R p q) → DownOn A R x y := by
    intro x y s hys
    induction hys with
    | refl s =>
        intro hx hs hcx hxs hslice
        exact hslice (Reach.refl x) (Reach.refl s) hcx
          (conTopped_of_reach hR hgrey hxs hcx) (EqvOn.of_reach hx hs hxs)
    | @head y c s hyc hcs ih =>
        intro hx hy hcx hxs hs
        have hc : c ∈ A := (hmem hyc).2
        have htail : DownOn A R x c := ih hx hc hcx hxs
          (fun hp hq hcp hcq hpq => hs hp (Reach.head hyc hq) hcp hcq hpq)
        rcases hgrey hyc with hroot | hbar | hhat
        · exact DownOn.symm (downOn_peel hy hc (Or.inl hroot) (DownOn.symm htail))
        · exact DownOn.symm (downOn_peel hy hc (Or.inr hbar) (DownOn.symm htail))
        · exact hs (Reach.refl x) (Reach.refl y) hcx (ConTopped.of_hatEq hhat)
            ⟨hx, hy, s, hxs, Reach.head hyc hcs⟩
  obtain ⟨ha, hb, s, has, hbs⟩ := hab
  induction has with
  | refl s =>
      exact DownOn.symm (reach_sound hbs hb ha
        (fun hp hq hcp hcq hpq => DownOn.symm
          (hslice hq hp hcq hcp (EqvOn.symm hpq))))
  | @head a c s hac hcs ih =>
      have hc : c ∈ A := (hmem hac).2
      have htail : DownOn A R c b := ih
        (fun hp hq hcp hcq hpq => hslice (Reach.head hac hp) hq hcp hcq hpq) hc hbs
      rcases hgrey hac with hroot | hbar | hhat
      · exact downOn_peel ha hc (Or.inl hroot) htail
      · exact downOn_peel ha hc (Or.inr hbar) htail
      · exact con_valley hbs ha hb (ConTopped.of_hatEq hhat) (Reach.head hac hcs) hslice

/-- An unsound equality has an unsound constructor pair on the same two parent
paths. The witnesses are actual reached nodes of the proposed graph. -/
theorem EqvOn.exists_reachable_constructor_failure
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (hR : ConstructorRules R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    {a b : Term (sigma ⊕ sigma) nu} (hab : EqvOn A g a b)
    (hbad : ¬ DownOn A R a b) :
    ∃ x y, Reach g a x ∧ Reach g b y ∧ ConTopped x ∧ ConTopped y ∧
      EqvOn A g x y ∧ ¬ DownOn A R x y := by
  classical
  by_contra hnone
  apply hbad
  apply eqvOn_downOn_of_reachableConstructorSlice hR hmem hgrey hab
  intro x y hax hby hcx hcy hxy
  by_contra hnot
  exact hnone ⟨x, y, hax, hby, hcx, hcy, hxy, hnot⟩

/-- A terminating self-grey parent function becomes a proof graph by proving
soundness only on its constructor-topped equality pairs. -/
def PGraph.of_constructorSlice
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (hR : ConstructorRules R)
    (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hterm : Terminating g)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    (hslice : ∀ {a b}, ConTopped a → ConTopped b →
      EqvOn A g a b → DownOn A R a b) : PGraph A R where
  par := g
  mem_edge := hmem
  term := hterm
  sub := eqvOn_downOn_of_constructorSlice hR hmem hgrey hslice
  grey := hgrey

/-! ## Constructor dependencies with proved seeds -/

/-- A constructor pair depends on a reached constructor pair through one aligned
argument pair. Seed pairs are excluded at all three positions. -/
def ConstructorSupportDependency
    (A : List (Term (sigma ⊕ sigma) nu))
    (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (seed : CRel sigma nu)
    (q p : Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu) : Prop :=
  ¬ seed q.1 q.2 ∧ ¬ seed p.1 p.2 ∧ EqvOn A g p.1 p.2 ∧
    ∃ c xs ys x y, p.1 = .app (.inl c) xs ∧ p.2 = .app (.inl c) ys ∧
      (x, y) ∈ xs.zip ys ∧ EqvOn A g x y ∧ ¬ seed x y ∧
      Reach g x q.1 ∧ Reach g y q.2 ∧ ConTopped q.1 ∧ ConTopped q.2 ∧
      EqvOn A g q.1 q.2

/-- Proved seeds and well-founded constructor dependencies establish graph
soundness for arbitrary constructor rules. Neither rule termination nor a
destructor-symbol order nor an overlap condition is a premise. -/
theorem eqvOn_downOn_of_wellFounded_constructorSupport
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    {seed : CRel sigma nu}
    (hseed : ∀ {a b}, seed a b → DownOn A R a b)
    (hwf : WellFounded (ConstructorSupportDependency A g seed))
    {a b : Term (sigma ⊕ sigma) nu} (hab : EqvOn A g a b) : DownOn A R a b := by
  classical
  have lift : ∀ {xs ys : List (Term (sigma ⊕ sigma) nu)},
      List.Forall₂ (EqvOn A g) xs ys →
      (∀ x y, (x, y) ∈ xs.zip ys → EqvOn A g x y → DownOn A R x y) →
      List.Forall₂ (DownOn A R) xs ys := by
    intro xs ys hall
    induction hall with
    | nil => intro _; exact List.Forall₂.nil
    | @cons x y xs ys hxy htail ih =>
        intro h
        exact List.Forall₂.cons (h x y (by simp) hxy)
          (ih (fun p q hpq heq => h p q (by simp [hpq]) heq))
  have hslice : ∀ p : Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu,
      ConTopped p.1 → ConTopped p.2 → EqvOn A g p.1 p.2 → DownOn A R p.1 p.2 := by
    intro p
    induction p using hwf.induction with
    | h p ih =>
        intro hcp hdp hp
        by_cases hsp : seed p.1 p.2
        · exact hseed hsp
        · rcases constructorCompatible_eqvOn_of_selfGrey hA hR hmem hgrey
            p.1 p.2 hcp hdp hp with
            ⟨z, hz₁, hz₂⟩ | ⟨c, xs, ys, hx, hy, hargs⟩
          · have heq : p.1 = p.2 := hz₁.trans hz₂.symm
            exact heq ▸ DownOn.refl hp.1
          · have hdown : List.Forall₂ (DownOn A R) xs ys := by
              apply lift hargs
              intro x y hxy heq
              by_cases hsxy : seed x y
              · exact hseed hsxy
              · apply eqvOn_downOn_of_reachableConstructorSlice hR hmem hgrey heq
                intro s t hxs hyt hcs hct hst
                by_cases hsst : seed s t
                · exact hseed hsst
                · apply ih (s, t) ?_ hcs hct hst
                  exact ⟨hsst, hsp, hp, c, xs, ys, x, y,
                    hx, hy, hxy, heq, hsxy, hxs, hyt, hcs, hct, hst⟩
            rw [hx, hy]
            exact DownOn.hatCl (hx ▸ hp.1) (hy ▸ hp.2.1) hdown
  exact eqvOn_downOn_of_constructorSlice hR hmem hgrey
    (fun {x y} hx hy hxy => hslice (x, y) hx hy hxy) hab

/-- The constructor-support certificate constructs a proof graph with exactly
the proposed parent function. Parent termination is required only here. -/
def PGraph.of_constructorSupport
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hmem : ∀ {a b}, g a = some b → a ∈ A ∧ b ∈ A)
    (hterm : Terminating g)
    (hgrey : ∀ {a b}, g a = some b → Grey A R (EqvOn A g) a b)
    {seed : CRel sigma nu}
    (hseed : ∀ {a b}, seed a b → DownOn A R a b)
    (hwf : WellFounded (ConstructorSupportDependency A g seed)) : PGraph A R where
  par := g
  mem_edge := hmem
  term := hterm
  sub := eqvOn_downOn_of_wellFounded_constructorSupport hA hR hmem hgrey hseed hwf
  grey := hgrey

/-! ## Destructor-only contexts -/

/-- The least relation containing E and closed under destructor applications. -/
def DCT (E : CRel sigma nu) : CRel sigma nu :=
  fun a b => ∀ S : CRel sigma nu,
    (∀ x y, E x y → S x y) →
    (∀ x y, barRel S x y → S x y) → S a b

theorem DCT.base {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : E a b) : DCT E a b :=
  fun _ hbase _ => hbase a b h

theorem DCT.least {E S : CRel sigma nu}
    (hbase : ∀ a b, E a b → S a b)
    (hclosed : ∀ a b, barRel S a b → S a b)
    {a b : Term (sigma ⊕ sigma) nu} (h : DCT E a b) : S a b :=
  h S hbase hclosed

theorem DCT.barClosed {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : barRel (DCT E) a b) : DCT E a b := by
  intro S hbase hclosed
  apply hclosed a b
  exact tildeOn_mono (fun _ _ hab => hab S hbase hclosed) h

theorem DCT.app {E : CRel sigma nu} {d : sigma}
    {xs ys : List (Term (sigma ⊕ sigma) nu)} (h : List.Forall₂ (DCT E) xs ys) :
    DCT E (.app (.inr d) xs) (.app (.inr d) ys) :=
  DCT.barClosed ⟨.inr d, xs, ys, ⟨d, rfl⟩, rfl, rfl, h⟩

theorem DCT.mono {E F : CRel sigma nu} (h : ∀ a b, E a b → F a b)
    {a b : Term (sigma ⊕ sigma) nu} (hab : DCT E a b) : DCT F a b :=
  DCT.least (fun a b he => DCT.base (h a b he))
    (fun _ _ => DCT.barClosed) hab

theorem DCT.toCT {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : DCT E a b) : CT E a b :=
  DCT.least (fun _ _ => CT.base)
    (fun _ _ hb => CT.sigmaClosed _ _ (tildeAll_of_barRel hb)) h

theorem DCT.unfold {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu} :
    DCT E a b ↔ E a b ∨ barRel (DCT E) a b := by
  constructor
  · intro hab
    apply DCT.least (S := fun x y => E x y ∨ barRel (DCT E) x y)
      (fun _ _ h => Or.inl h) ?_ hab
    intro x y hxy
    exact Or.inr (tildeOn_mono (fun _ _ h => h.elim DCT.base DCT.barClosed) hxy)
  · exact fun h => h.elim DCT.base DCT.barClosed

/-- Destructor contexts introduce no pair with a constructor-topped endpoint. -/
theorem DCT.conTopped_left_iff {E : CRel sigma nu}
    {a b : Term (sigma ⊕ sigma) nu} (ha : ConTopped a) :
    DCT E a b ↔ E a b := by
  constructor
  · intro hab
    rcases DCT.unfold.mp hab with he | ⟨f, xs, ys, ⟨d, rfl⟩, rfl, _, _⟩
    · exact he
    · exact (not_conTopped_destructor xs ha).elim
  · exact DCT.base

theorem DCT.conTopped_right_iff {E : CRel sigma nu}
    {a b : Term (sigma ⊕ sigma) nu} (hb : ConTopped b) :
    DCT E a b ↔ E a b := by
  constructor
  · intro hab
    rcases DCT.unfold.mp hab with he | ⟨f, xs, ys, ⟨d, rfl⟩, _, rfl, _⟩
    · exact he
    · exact (not_conTopped_destructor ys hb).elim
  · exact DCT.base

theorem DCT.constructorCompatible {E : CRel sigma nu}
    (hE : ConstructorCompatible E) : ConstructorCompatible (DCT E) := by
  intro a b ha hb hab
  rcases hE a b ha hb ((DCT.conTopped_left_iff ha).mp hab) with
      hv | ⟨f, xs, ys, hax, hby, hargs⟩
  · exact Or.inl hv
  · exact Or.inr ⟨f, xs, ys, hax, hby,
      forall₂_mono (fun _ _ => DCT.base) hargs⟩

/-- A missing destructor-context equation contains a missing one-step
destructor congruence between subterms. Constructor closure is not required. -/
theorem DCT.exists_missing_barRel {E : CRel sigma nu}
    {a b : Term (sigma ⊕ sigma) nu} (hab : DCT E a b) (hne : ¬ E a b) :
    ∃ x y, Subterm x a ∧ Subterm y b ∧ barRel E x y ∧ ¬ E x y := by
  classical
  have split : ∀ {xs ys : List (Term (sigma ⊕ sigma) nu)},
      List.Forall₂ (DCT E) xs ys →
        List.Forall₂ E xs ys ∨
          ∃ x y, x ∈ xs ∧ y ∈ ys ∧ DCT E x y ∧ ¬ E x y := by
    intro xs ys h
    induction h with
    | nil => exact Or.inl List.Forall₂.nil
    | @cons x y xs ys hxy _ ih =>
        by_cases he : E x y
        · rcases ih with hall | ⟨p, q, hp, hq, hpq, hnot⟩
          · exact Or.inl (List.Forall₂.cons he hall)
          · exact Or.inr ⟨p, q, List.mem_cons_of_mem _ hp,
              List.mem_cons_of_mem _ hq, hpq, hnot⟩
        · exact Or.inr ⟨x, y, by simp, by simp, hxy, he⟩
  induction a using Term.rec' generalizing b with
  | hvar z =>
      exact (hne ((DCT.conTopped_left_iff (ConTopped.var z)).mp hab)).elim
  | happ f xs ih =>
      rcases DCT.unfold.mp hab with he | ⟨g, us, ys, hg, hleft, rfl, hargs⟩
      · exact (hne he).elim
      obtain ⟨rfl, rfl⟩ := Term.app.inj hleft
      rcases split hargs with hall | ⟨p, q, hp, hq, hpq, hnot⟩
      · exact ⟨.app f xs, .app f ys, Subterm.refl _, Subterm.refl _,
          ⟨f, xs, ys, hg, rfl, rfl, hall⟩, hne⟩
      · obtain ⟨x, y, hxp, hyq, hbar, hbad⟩ := ih p hp hpq hnot
        exact ⟨x, y, Subterm.arg hp hxp, Subterm.arg hq hyq, hbar, hbad⟩

/-- Substitution through an all-destructor term uses only destructor contexts. -/
theorem DCT.destructorLabel_instances
    {E : CRel sigma nu} {s t : Subst (sigma ⊕ sigma) nu}
    (r : Term sigma nu) (hvars : ∀ x, VarOccurs x r → E (s x) (t x)) :
    DCT E (Subst.apply s (destructorLabel r))
      (Subst.apply t (destructorLabel r)) := by
  induction r using Term.rec' with
  | hvar x => exact DCT.base (hvars x .here)
  | happ f args ih =>
      simp only [destructorLabel_app, Subst.apply_app, Subst.applyList_eq_map,
        Term.mapSymList_eq_map, List.map_map]
      apply DCT.app
      apply forall₂_of_pointwise
      intro q hq
      exact ih q hq (fun x hx => hvars x (.arg hq hx))

/-- An active translated right-hand side has a base or destructor-only residual. -/
theorem destructorLabel_instances_destructor_residual
    {E : CRel sigma nu} {s t : Subst (sigma ⊕ sigma) nu}
    (r : Term sigma nu) (hvars : ∀ x, VarOccurs x r → E (s x) (t x)) :
    E (Subst.apply s (destructorLabel r)) (Subst.apply t (destructorLabel r)) ∨
      barRel (DCT E) (Subst.apply s (destructorLabel r))
        (Subst.apply t (destructorLabel r)) :=
  DCT.unfold.mp (DCT.destructorLabel_instances r hvars)

/-! ## One-term coalgebra extension -/

/-- For a new application whose arguments are old terms, context comparison
with an old term reduces to one argumentwise comparison in the old relation. -/
theorem CT.one_new_app_iff
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app f xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B)
    {b : Term (sigma ⊕ sigma) nu} (hb : b ∈ B) :
    CT E (.app f xs) b ↔ tildeAll E (.app f xs) b := by
  constructor
  · intro hct
    rcases CT.unfold.mp hct with he | ⟨g, us, ys, _, hleft, rfl, hargs⟩
    · exact (hnew (hmem he).1).elim
    obtain ⟨rfl, rfl⟩ := Term.app.inj hleft
    refine ⟨f, xs, ys, trivial, rfl, rfl, ?_⟩
    apply forall₂_onGuard_elim hxs (fun y hy => hB.arg hb hy)
    exact forall₂_mono (fun _ _ hxy hx hy => hcl.eq_of_CT hB hx hy hxy) hargs
  · intro h
    exact CT.sigmaClosed _ _ (tildeOn_mono (fun _ _ => CT.base) h)

/-- The destructor-only comparison reduces to one destructor congruence. -/
theorem DCT.one_new_app_iff
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app f xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B)
    {b : Term (sigma ⊕ sigma) nu} (hb : b ∈ B) :
    DCT E (.app f xs) b ↔ barRel E (.app f xs) b := by
  constructor
  · intro hct
    rcases DCT.unfold.mp hct with he | ⟨g, us, ys, hg, hleft, rfl, hargs⟩
    · exact (hnew (hmem he).1).elim
    obtain ⟨rfl, rfl⟩ := Term.app.inj hleft
    refine ⟨f, xs, ys, hg, rfl, rfl, ?_⟩
    apply forall₂_onGuard_elim hxs (fun y hy => hB.arg hb hy)
    exact forall₂_mono
      (fun _ _ hxy hx hy => hcl.eq_of_CT hB hx hy (DCT.toCT hxy)) hargs
  · intro h
    exact DCT.barClosed (tildeOn_mono (fun _ _ => DCT.base) h)

/-- All old representatives of a new application belong to one old class. -/
theorem CT.one_new_representatives_eq
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hnew : Term.app f xs ∉ B) (hxs : ∀ x ∈ xs, x ∈ B)
    {b c : Term (sigma ⊕ sigma) nu} (hb : b ∈ B) (hc : c ∈ B)
    (hab : CT E (.app f xs) b) (hac : CT E (.app f xs) c) : E b c := by
  obtain ⟨g, us, ys, _, hleft, rfl, hxy⟩ :=
    (CT.one_new_app_iff hB hcl hmem hnew hxs hb).mp hab
  obtain ⟨rfl, rfl⟩ := Term.app.inj hleft
  obtain ⟨g, us, zs, _, hleft, rfl, hxz⟩ :=
    (CT.one_new_app_iff hB hcl hmem hnew hxs hc).mp hac
  obtain ⟨rfl, rfl⟩ := Term.app.inj hleft
  apply hcl _ _ hb hc
  refine ⟨f, ys, zs, trivial, rfl, rfl, ?_⟩
  exact forall₂_compose_of_mem
    (forall₂_flip (forall₂_mono hsymm hxy)) hxz
    (fun _ _ _ _ _ _ h₁ h₂ => htrans _ _ _ h₁ h₂)

/-! ## Conservative context insertion -/

private theorem coalgebra_cons_app_args_mem
    {B : List (Term (sigma ⊕ sigma) nu)}
    {f : sigma ⊕ sigma} {xs : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra (.app f xs :: B)) : ∀ x ∈ xs, x ∈ B := by
  intro x hx
  rcases List.mem_cons.mp
      (hA.arg (f := f) (args := xs) (List.mem_cons_self ..) hx) with heq | hold
  · have hlt := Term.size_lt_of_mem (f := f) hx
    rw [heq] at hlt
    exact (Nat.lt_irrefl _ hlt).elim
  · exact hold

/-- On a one-term coalgebra extension, all old context representatives of the
new term belong to one old equality class. The new term may be a variable. -/
theorem CT.one_new_representatives_eq_of_coalgebra
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hnew : a ∉ B) {b c : Term (sigma ⊕ sigma) nu}
    (hb : b ∈ B) (hc : c ∈ B) (hab : CT E a b) (hac : CT E a c) : E b c := by
  cases a with
  | var z => exact (hnew (hmem (CT.var_left_iff.mp hab)).1).elim
  | app f xs =>
      exact CT.one_new_representatives_eq hB hcl hmem hsymm htrans
        hnew (coalgebra_cons_app_args_mem hA) hb hc hab hac

/-- A term represents itself; the inserted term also represents each old
application obtained by context comparison. -/
def ContextRepresentative (E : CRel sigma nu)
    (a x p : Term (sigma ⊕ sigma) nu) : Prop :=
  x = p ∨ x = a ∧ CT E a p

/-- Attach the inserted term to the old equality class of its context
representatives. No root rewrite or transitive closure is included. -/
def OneTermContextExtension (E : CRel sigma nu)
    (a : Term (sigma ⊕ sigma) nu) : CRel sigma nu :=
  fun x y => (x = a ∧ y = a) ∨
    ∃ p q, ContextRepresentative E a x p ∧ E p q ∧
      ContextRepresentative E a y q

theorem OneTermContextExtension.base {E : CRel sigma nu}
    (a : Term (sigma ⊕ sigma) nu) {x y : Term (sigma ⊕ sigma) nu}
    (h : E x y) : OneTermContextExtension E a x y :=
  Or.inr ⟨x, y, Or.inl rfl, h, Or.inl rfl⟩

theorem OneTermContextExtension.mem
    {B : List (Term (sigma ⊕ sigma) nu)} {E : CRel sigma nu}
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    {a x y : Term (sigma ⊕ sigma) nu}
    (h : OneTermContextExtension E a x y) : x ∈ a :: B ∧ y ∈ a :: B := by
  rcases h with ⟨rfl, rfl⟩ | ⟨p, q, hxp, hpq, hyq⟩
  · exact ⟨by simp, by simp⟩
  have representative_mem : ∀ {z r}, ContextRepresentative E a z r →
      r ∈ B → z ∈ a :: B := by
    intro z r hzr hr
    rcases hzr with rfl | ⟨rfl, _⟩
    · exact List.mem_cons_of_mem a hr
    · exact List.mem_cons_self
  exact ⟨representative_mem hxp (hmem hpq).1,
    representative_mem hyq (hmem hpq).2⟩

theorem OneTermContextExtension.refl
    {B : List (Term (sigma ⊕ sigma) nu)} {E : CRel sigma nu}
    (hrefl : ∀ x ∈ B, E x x) {a x : Term (sigma ⊕ sigma) nu}
    (hx : x ∈ a :: B) : OneTermContextExtension E a x x := by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inl ⟨rfl, rfl⟩
  · exact OneTermContextExtension.base a (hrefl x hx)

theorem OneTermContextExtension.symm {E : CRel sigma nu}
    (hsymm : ∀ x y, E x y → E y x)
    {a x y : Term (sigma ⊕ sigma) nu}
    (h : OneTermContextExtension E a x y) : OneTermContextExtension E a y x := by
  rcases h with ⟨hx, hy⟩ | ⟨p, q, hxp, hpq, hyq⟩
  · exact Or.inl ⟨hy, hx⟩
  · exact Or.inr ⟨q, p, hyq, hsymm p q hpq, hxp⟩

/-- Context insertion does not merge two old equality classes. -/
theorem OneTermContextExtension.old_iff
    {B : List (Term (sigma ⊕ sigma) nu)} {E : CRel sigma nu}
    {a x y : Term (sigma ⊕ sigma) nu} (hnew : a ∉ B)
    (hx : x ∈ B) (hy : y ∈ B) :
    OneTermContextExtension E a x y ↔ E x y := by
  constructor
  · intro h
    rcases h with ⟨rfl, _⟩ | ⟨p, q, hxp, hpq, hyq⟩
    · exact (hnew hx).elim
    rcases hxp with rfl | ⟨rfl, _⟩
    · rcases hyq with rfl | ⟨rfl, _⟩
      · exact hpq
      · exact (hnew hy).elim
    · exact (hnew hx).elim
  · exact OneTermContextExtension.base a

/-- Without an old context representative, insertion adds exactly one singleton
class. -/
theorem OneTermContextExtension.isolated_iff
    {B : List (Term (sigma ⊕ sigma) nu)} {E : CRel sigma nu}
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    {a x y : Term (sigma ⊕ sigma) nu}
    (hno : ∀ p ∈ B, ¬ CT E a p) :
    OneTermContextExtension E a x y ↔ (x = a ∧ y = a) ∨ E x y := by
  constructor
  · intro h
    rcases h with hdiag | ⟨p, q, hxp, hpq, hyq⟩
    · exact Or.inl hdiag
    rcases hxp with rfl | ⟨_, hct⟩
    · rcases hyq with rfl | ⟨_, hct⟩
      · exact Or.inr hpq
      · exact (hno q (hmem hpq).2 hct).elim
    · exact (hno p (hmem hpq).1 hct).elim
  · rintro (hdiag | he)
    · exact Or.inl hdiag
    · exact OneTermContextExtension.base a he

/-- A fresh variable contributes a singleton class. -/
theorem OneTermContextExtension.variable_iff
    {B : List (Term (sigma ⊕ sigma) nu)} {E : CRel sigma nu}
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B) {z : nu}
    (hnew : Term.var z ∉ B) {x y : Term (sigma ⊕ sigma) nu} :
    OneTermContextExtension E (.var z) x y ↔
      (x = .var z ∧ y = .var z) ∨ E x y :=
  OneTermContextExtension.isolated_iff hmem
    (fun _ _ h => hnew (hmem (CT.var_left_iff.mp h)).1)

private theorem contextRepresentative_same_class
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    (hrefl : ∀ x ∈ B, E x x)
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hnew : a ∉ B)
    {z p q : Term (sigma ⊕ sigma) nu} (hp : p ∈ B) (hq : q ∈ B)
    (hzp : ContextRepresentative E a z p)
    (hzq : ContextRepresentative E a z q) : E p q := by
  rcases hzp with rfl | ⟨rfl, hzp⟩
  · rcases hzq with rfl | ⟨rfl, _⟩
    · exact hrefl _ hp
    · exact (hnew hp).elim
  · rcases hzq with hEq | ⟨_, hzq⟩
    · exact (hnew (hEq.symm ▸ hq)).elim
    · exact CT.one_new_representatives_eq_of_coalgebra hB hA hcl hmem
        hsymm htrans hnew hp hq hzp hzq

theorem OneTermContextExtension.trans
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    (hrefl : ∀ x ∈ B, E x x)
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hnew : a ∉ B)
    {x y z : Term (sigma ⊕ sigma) nu}
    (hxy : OneTermContextExtension E a x y)
    (hyz : OneTermContextExtension E a y z) :
    OneTermContextExtension E a x z := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨p, q, hxp, hpq, hyq⟩
  · exact hyz
  rcases hyz with ⟨rfl, rfl⟩ | ⟨r, s, hyr, hrs, hzs⟩
  · exact Or.inr ⟨p, q, hxp, hpq, hyq⟩
  have hqr : E q r := contextRepresentative_same_class hB hA hcl hmem hrefl
    hsymm htrans hnew (hmem hpq).2 (hmem hrs).1 hyq hyr
  exact Or.inr ⟨p, s, hxp, htrans _ _ _ hpq (htrans _ _ _ hqr hrs), hzs⟩

/-- Every context comparison between members is represented after insertion. -/
theorem OneTermContextExtension.of_context
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hrefl : ∀ x ∈ B, E x x) (hsymm : ∀ x y, E x y → E y x)
    {a x y : Term (sigma ⊕ sigma) nu}
    (hx : x ∈ a :: B) (hy : y ∈ a :: B) (hct : CT E x y) :
    OneTermContextExtension E a x y := by
  rcases List.mem_cons.mp hx with hxNew | hxOld
  · subst x
    rcases List.mem_cons.mp hy with hyNew | hyOld
    · subst y
      exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨y, y, Or.inr ⟨rfl, hct⟩, hrefl y hyOld, Or.inl rfl⟩
  · rcases List.mem_cons.mp hy with hyNew | hyOld
    · subst y
      exact Or.inr ⟨x, x, Or.inl rfl, hrefl x hxOld,
        Or.inr ⟨rfl, CT.symm hsymm hct⟩⟩
    · exact OneTermContextExtension.base a (hcl.eq_of_CT hB hxOld hyOld hct)

/-- Context insertion is closed under all function symbols on the enlarged
carrier, even when an old representative is equal to a different-headed term. -/
theorem OneTermContextExtension.sigmaClosedOn
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hrefl : ∀ x ∈ B, E x x) (hsymm : ∀ x y, E x y → E y x)
    (hnew : a ∉ B) : SigmaClosedOn (a :: B) (OneTermContextExtension E a) := by
  have old_args : ∀ {g ys}, Term.app g ys ∈ a :: B →
      ∀ y ∈ ys, y ∈ B := by
    intro g ys hmem y hy
    rcases List.mem_cons.mp hmem with heq | hold
    · subst a
      exact coalgebra_cons_app_args_mem hA y hy
    · exact hB.arg hold hy
  intro x y hx hy htilde
  obtain ⟨g, ps, qs, _, rfl, rfl, hpq⟩ := htilde
  have hargs : List.Forall₂ E ps qs := by
    apply forall₂_onGuard_elim (old_args hx) (old_args hy)
    exact forall₂_mono (fun p q hpq hp hq =>
      (OneTermContextExtension.old_iff hnew hp hq).mp hpq) hpq
  exact OneTermContextExtension.of_context hB hcl hrefl hsymm hx hy
    (CT.app (forall₂_mono (fun _ _ h => CT.base h) hargs))

/-- Every equivalence extending the old relation and closed under contexts
contains the explicit one-term extension. -/
theorem OneTermContextExtension.least
    {B : List (Term (sigma ⊕ sigma) nu)} {E F : CRel sigma nu}
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    (hEF : ∀ x y, E x y → F x y)
    (hrefl : ∀ x ∈ a :: B, F x x)
    (hsymm : ∀ x y, F x y → F y x)
    (htrans : ∀ x y z, F x y → F y z → F x z)
    (hclosed : SigmaClosedOn (a :: B) F)
    {x y : Term (sigma ⊕ sigma) nu}
    (h : OneTermContextExtension E a x y) : F x y := by
  rcases h with ⟨hx, hy⟩ | ⟨p, q, hxp, hpq, hyq⟩
  · subst x
    subst y
    exact hrefl a (by simp)
  have represent : ∀ {z r}, ContextRepresentative E a z r → r ∈ B → F z r := by
    intro z r hzr hr
    rcases hzr with heq | ⟨heq, hct⟩
    · subst z
      exact hrefl r (List.mem_cons_of_mem a hr)
    · subst z
      exact hclosed.eq_of_CT hA (by simp) (List.mem_cons_of_mem a hr)
        (CT.mono hEF hct)
  exact htrans _ _ _ (represent hxp (hmem hpq).1)
    (htrans _ _ _ (hEF p q hpq) (hsymm _ _ (represent hyq (hmem hpq).2)))

private theorem contextRepresentative_hatEq
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    (hrefl : ∀ x ∈ B, E x x) (hnew : a ∉ B)
    {x p : Term (sigma ⊕ sigma) nu} (hcx : ConTopped x) (hp : p ∈ B)
    (hxp : ContextRepresentative E a x p) : hatEq E x p := by
  rcases hxp with rfl | ⟨rfl, hct⟩
  · rcases hcx with ⟨z, rfl⟩ | ⟨f, xs, rfl⟩
    · exact Or.inl ⟨z, rfl, rfl⟩
    · exact Or.inr ⟨.inl f, xs, xs, ⟨f, rfl⟩, rfl, rfl,
        forall₂_self_of (fun z hz => hrefl z (hB.arg hp hz))⟩
  · rcases hcx with ⟨z, rfl⟩ | ⟨f, xs, rfl⟩
    · exact (hnew (hmem (CT.var_left_iff.mp hct)).1).elim
    · obtain ⟨g, us, ys, _, heq, rfl, hargs⟩ :=
        (CT.one_new_app_iff hB hcl hmem hnew
          (coalgebra_cons_app_args_mem hA) hp).mp hct
      obtain ⟨rfl, rfl⟩ := Term.app.inj heq
      exact Or.inr ⟨.inl f, xs, ys, ⟨f, rfl⟩, rfl, rfl, hargs⟩

/-- Constructor compatibility survives context insertion on every finite
coalgebra. This conclusion uses the old equivalence laws, not rewrite soundness. -/
theorem OneTermContextExtension.constructorCompatible
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {E : CRel sigma nu} (hcl : SigmaClosedOn B E)
    (hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B)
    (hrefl : ∀ x ∈ B, E x x)
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hcc : ConstructorCompatible E) (hnew : a ∉ B) :
    ConstructorCompatible (OneTermContextExtension E a) := by
  intro x y hcx hcy hxy
  have hhat : hatEq (OneTermContextExtension E a) x y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨p, q, hxp, hpq, hyq⟩
    · rcases hcx with ⟨z, rfl⟩ | ⟨f, xs, rfl⟩
      · exact Or.inl ⟨z, rfl, rfl⟩
      · exact Or.inr ⟨.inl f, xs, xs, ⟨f, rfl⟩, rfl, rfl,
          forall₂_self_of (fun z hz => OneTermContextExtension.refl hrefl
            (hA.arg (f := .inl f) (args := xs) (List.mem_cons_self ..) hz))⟩
    · have hxp' := contextRepresentative_hatEq hB hA hcl hmem hrefl
        hnew hcx (hmem hpq).1 hxp
      have hyq' := contextRepresentative_hatEq hB hA hcl hmem hrefl
        hnew hcy (hmem hpq).2 hyq
      have hpq' : hatEq E p q := by
        rcases hcc p q (ConTopped.of_hatEq_right hxp')
          (ConTopped.of_hatEq_right hyq') hpq with hvar | ⟨f, ps, qs, hp, hq, hargs⟩
        · exact Or.inl hvar
        · exact Or.inr ⟨.inl f, ps, qs, ⟨f, rfl⟩, hp, hq, hargs⟩
      exact hatEq.mono (fun _ _ h => OneTermContextExtension.base a h)
        (hatEq.trans htrans hxp' (hatEq.trans htrans hpq' (hatEq.symm hsymm hyq')))
  rcases hhat with hvar | ⟨f, xs, ys, ⟨c, hfc⟩, hx, hy, hargs⟩
  · exact Or.inl hvar
  · subst f
    exact Or.inr ⟨c, xs, ys, hx, hy, hargs⟩

/-- Enlarging the carrier without adding parent edges adds only isolated
diagonal pairs to the represented equality. -/
theorem PGraph.eqvOn_largerCarrier_iff
    {B A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (hBA : ∀ x ∈ B, x ∈ A)
    {x y : Term (sigma ⊕ sigma) nu} :
    EqvOn A rho.par x y ↔ (x = y ∧ x ∈ A) ∨ EqvOn B rho.par x y := by
  classical
  have outside_eq : ∀ {p q}, p ∉ B → Reach rho.par p q → p = q := by
    intro p q hp hpath
    cases hpath with
    | refl => rfl
    | head hedge _ => exact (hp (rho.mem_edge hedge).1).elim
  constructor
  · rintro ⟨hxA, hyA, r, hxr, hyr⟩
    by_cases hx : x ∈ B
    · have hr := rho.mem_of_reach_right hx hxr
      have hy : y ∈ B := by
        by_contra hy
        exact hy ((outside_eq hy hyr).symm ▸ hr)
      exact Or.inr ⟨hx, hy, r, hxr, hyr⟩
    · have hxr' := outside_eq hx hxr
      subst r
      cases hyr with
      | refl => exact Or.inl ⟨rfl, hxA⟩
      | head hedge htail =>
          exact (hx (rho.mem_of_reach_right (rho.mem_edge hedge).2 htail)).elim
  · rintro (⟨rfl, hx⟩ | ⟨hx, hy, r, hxr, hyr⟩)
    · exact EqvOn.refl hx
    · exact ⟨hBA x hx, hBA y hy, r, hxr, hyr⟩

/-- Retain every parent and add isolated nodes when enlarging the carrier. -/
def PGraph.liftCarrier
    {B A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (hBA : ∀ x ∈ B, x ∈ A) : PGraph A R where
  par := rho.par
  mem_edge := fun h => ⟨hBA _ (rho.mem_edge h).1, hBA _ (rho.mem_edge h).2⟩
  term := rho.term
  sub := by
    intro x y hxy
    rcases (rho.eqvOn_largerCarrier_iff hBA).mp hxy with ⟨rfl, hx⟩ | hold
    · exact DownOn.refl hx
    · exact DownOn.mono hBA (rho.sub hold)
  grey := by
    intro x y hxy
    rcases rho.grey hxy with hroot | hbar | hhat
    · exact Or.inl hroot
    · exact Or.inr (Or.inl (tildeOn_mono
        (fun _ _ h => DownOn.mono hBA h) hbar))
    · exact Or.inr (Or.inr (hatEq.mono (fun _ _ h =>
        (rho.eqvOn_largerCarrier_iff hBA).mpr (Or.inr h)) hhat))

theorem PGraph.liftCarrier_par
    {B A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (hBA : ∀ x ∈ B, x ∈ A) :
    (rho.liftCarrier hBA).par = rho.par := rfl

theorem PGraph.liftCarrier_nf
    {B A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (hBA : ∀ x ∈ B, x ∈ A)
    {a : Term (sigma ⊕ sigma) nu} (ha : a ∉ B) : (rho.liftCarrier hBA).NF a := by
  change rho.par a = none
  cases hpar : rho.par a with
  | none => rfl
  | some b => exact (ha (rho.mem_edge hpar).1).elim

theorem PGraph.liftCarrier_tight
    {B A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph B R) (hBA : ∀ x ∈ B, x ∈ A) (ht : rho.Tight) :
    (rho.liftCarrier hBA).Tight := by
  intro x y hxy
  exact (ht hxy).mono (fun _ _ h =>
    (rho.eqvOn_largerCarrier_iff hBA).mpr (Or.inr h))

/-- A reflexive, symmetric, transitive relation containing every parent edge
contains every represented equality on the carrier. -/
theorem PGraph.eqvOn_subset_of_parent
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {F : CRel sigma nu}
    (hrefl : ∀ x ∈ A, F x x) (hsymm : ∀ x y, F x y → F y x)
    (htrans : ∀ x y z, F x y → F y z → F x z)
    (hedge : ∀ {x y}, rho.par x = some y → F x y)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : EqvOn A rho.par x y) : F x y := by
  have route : ∀ {p q}, p ∈ A → Reach rho.par p q → F p q := by
    intro p q hp hpath
    induction hpath with
    | refl => exact hrefl _ hp
    | @head p q r hpq _ ih =>
        exact htrans _ _ _ (hedge hpq) (ih (rho.mem_edge hpq).2)
  obtain ⟨hx, hy, r, hxr, hyr⟩ := hxy
  exact htrans _ _ _ (route hx hxr) (hsymm _ _ (route hy hyr))

/-- A locally context-closed proof graph extends to a one-term larger coalgebra
with exactly the conservative context equality and every old parent retained. -/
theorem PGraph.exists_contextInsertion
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph B R) (hcl : SigmaClosedOn B (EqvOn B rho.par))
    (hnew : a ∉ B) :
    ∃ beta : PGraph (a :: B) R,
      (∀ {x y}, rho.par x = some y → beta.par x = some y) ∧
      (∀ x, x ≠ a → beta.par x = rho.par x) ∧
      (∀ x y, EqvOn (a :: B) beta.par x y ↔
        OneTermContextExtension (EqvOn B rho.par) a x y) ∧
      SigmaClosedOn (a :: B) (EqvOn (a :: B) beta.par) ∧
      (rho.Tight → beta.Tight) := by
  classical
  let E : CRel sigma nu := EqvOn B rho.par
  let F : CRel sigma nu := OneTermContextExtension E a
  let alpha := rho.liftCarrier (fun x hx => List.mem_cons_of_mem a hx)
  have hmem : ∀ {x y}, E x y → x ∈ B ∧ y ∈ B := fun h => h.mem
  have hErefl : ∀ x ∈ B, E x x := fun _ hx => EqvOn.refl hx
  have hEsymm : ∀ x y, E x y → E y x := fun _ _ h => h.symm
  have hEtrans : ∀ x y z, E x y → E y z → E x z := fun _ _ _ h₁ h₂ => h₁.trans h₂
  have hFclosed := OneTermContextExtension.sigmaClosedOn hB hA hcl hErefl hEsymm hnew
  have close_of_exact : ∀ (beta : PGraph (a :: B) R),
      (∀ x y, EqvOn (a :: B) beta.par x y ↔ F x y) →
      SigmaClosedOn (a :: B) (EqvOn (a :: B) beta.par) := by
    intro beta heq x y hx hy hargs
    exact (heq x y).mpr (hFclosed x y hx hy
      (tildeOn_mono (fun p q hpq => (heq p q).mp hpq) hargs))
  by_cases hex : ∃ p ∈ B, CT E a p
  · obtain ⟨p, hp, hcontext⟩ := hex
    have hrepr : tildeAll E a p := by
      cases a with
      | var z => exact (hnew (hmem (CT.var_left_iff.mp hcontext)).1).elim
      | app f xs =>
          exact (CT.one_new_app_iff hB hcl hmem hnew
            (coalgebra_cons_app_args_mem hA) hp).mp hcontext
    have hedge : TightEdge R (EqvOn (a :: B) alpha.par) a p := by
      obtain ⟨f, xs, ys, _, rfl, rfl, hargs⟩ := hrepr
      have hargs' := forall₂_mono (fun x y h =>
        (rho.eqvOn_largerCarrier_iff
          (fun x hx => List.mem_cons_of_mem (.app f xs) hx)).mpr
          (Or.inr h)) hargs
      cases f with
      | inl c => exact Or.inr (Or.inr
          (Or.inr ⟨.inl c, xs, ys, ⟨c, rfl⟩, rfl, rfl, hargs'⟩))
      | inr d => exact Or.inr (Or.inl
          ⟨.inr d, xs, ys, ⟨d, rfl⟩, rfl, rfl, hargs'⟩)
    have hne : ¬ EqvOn (a :: B) alpha.par a p := by
      intro h
      rcases (rho.eqvOn_largerCarrier_iff
        (fun x hx => List.mem_cons_of_mem a hx)).mp h with ⟨heq, _⟩ | hold
      · exact hnew (heq.symm ▸ hp)
      · exact hnew hold.mem.1
    obtain ⟨beta, hpar, hext, hnewEdge⟩ := alpha.extend_one_exact hA hR
      (by simp) (List.mem_cons_of_mem a hp) (rho.liftCarrier_nf _ hnew) hne
      (hedge.toGrey alpha)
    have old : ∀ x y, E x y → EqvOn (a :: B) beta.par x y := by
      intro x y h
      exact EqvOn.mono hext ((rho.eqvOn_largerCarrier_iff
        (fun x hx => List.mem_cons_of_mem a hx)).mpr (Or.inr h))
    have hap : EqvOn (a :: B) beta.par a p :=
      EqvOn.of_reach (by simp) (List.mem_cons_of_mem a hp)
        (Reach.head hnewEdge (Reach.refl p))
    have lower : ∀ x y, F x y → EqvOn (a :: B) beta.par x y := by
      intro x y h
      rcases h with ⟨rfl, rfl⟩ | ⟨u, v, hxu, huv, hyv⟩
      · exact EqvOn.refl (by simp)
      have represent : ∀ {z r}, ContextRepresentative E a z r → r ∈ B →
          EqvOn (a :: B) beta.par z r := by
        intro z r hzr hr
        rcases hzr with rfl | ⟨rfl, hct⟩
        · exact EqvOn.refl (List.mem_cons_of_mem a hr)
        · exact hap.trans (old p r
            (CT.one_new_representatives_eq_of_coalgebra hB hA hcl hmem hEsymm
              hEtrans hnew hp hr hcontext hct))
      exact (represent hxu (hmem huv).1).trans
        ((old u v huv).trans (represent hyv (hmem huv).2).symm)
    have upper : ∀ x y, EqvOn (a :: B) beta.par x y → F x y := by
      intro x y h
      apply beta.eqvOn_subset_of_parent
        (fun _ hx => OneTermContextExtension.refl hErefl hx)
        (fun _ _ h => OneTermContextExtension.symm hEsymm h)
        (fun _ _ _ h₁ h₂ => OneTermContextExtension.trans hB hA hcl hmem
          hErefl hEsymm hEtrans hnew h₁ h₂) ?_ h
      intro u v huv
      rw [hpar] at huv
      rcases extendPar_edge huv with ⟨hu, hv⟩ | hold
      · subst u
        subst v
        exact OneTermContextExtension.of_context hB hcl hErefl hEsymm
          (by simp) (List.mem_cons_of_mem a hp) hcontext
      · exact OneTermContextExtension.base a (EqvOn.of_reach
          (rho.mem_edge hold).1 (rho.mem_edge hold).2 (Reach.head hold (Reach.refl v)))
    have heq : ∀ x y, EqvOn (a :: B) beta.par x y ↔ F x y :=
      fun x y => ⟨upper x y, lower x y⟩
    refine ⟨beta, fun h => hext h, ?_, heq, close_of_exact beta heq, ?_⟩
    · intro x hx
      rw [hpar]
      exact extendPar_of_ne hx
    · intro ht x y hxy
      rw [hpar] at hxy
      rcases extendPar_edge hxy with ⟨rfl, rfl⟩ | hold
      · exact hedge.mono (fun _ _ h => EqvOn.mono hext h)
      · exact (ht hold).mono old
  · have hisolated : ∀ p ∈ B, ¬ CT E a p := fun p hp hct => hex ⟨p, hp, hct⟩
    have heq : ∀ x y, EqvOn (a :: B) alpha.par x y ↔ F x y := by
      intro x y
      change EqvOn (a :: B) rho.par x y ↔ OneTermContextExtension E a x y
      rw [rho.eqvOn_largerCarrier_iff (fun x hx => List.mem_cons_of_mem a hx),
        OneTermContextExtension.isolated_iff hmem hisolated]
      constructor
      · rintro (⟨rfl, hx⟩ | hold)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr (hErefl x hx)
        · exact Or.inr hold
      · rintro (⟨rfl, rfl⟩ | hold)
        · exact Or.inl ⟨rfl, by simp⟩
        · exact Or.inr hold
    exact ⟨alpha, fun h => h, fun _ _ => rfl, heq, close_of_exact alpha heq,
      fun ht => rho.liftCarrier_tight _ ht⟩

/-- The explicit context extension is sound for the actual Down inference;
the proof constructs the graph that certifies its represented equality. -/
theorem OneTermContextExtension.downOn
    {B : List (Term (sigma ⊕ sigma) nu)} (hB : Coalgebra B)
    {a : Term (sigma ⊕ sigma) nu} (hA : Coalgebra (a :: B))
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph B R) (hcl : SigmaClosedOn B (EqvOn B rho.par))
    (hnew : a ∉ B) {x y : Term (sigma ⊕ sigma) nu}
    (hxy : OneTermContextExtension (EqvOn B rho.par) a x y) :
    DownOn (a :: B) R x y := by
  obtain ⟨beta, _, _, heq, _, _⟩ := rho.exists_contextInsertion hB hA hR hcl hnew
  exact beta.sub ((heq x y).mpr hxy)

/-! ## Simultaneous parent replacement and root joining -/

/-- Replace one parent and join its former root to the other class's root. -/
noncomputable def PGraph.spliceParent
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a b : Term (sigma ⊕ sigma) nu) :=
  extendPar (extendPar rho.par a b) (rho.normalRoot a) (rho.normalRoot b)

/-- The two replacements preserve termination whenever the old classes differ. -/
theorem PGraph.spliceParent_terminating
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b) :
    Terminating (rho.spliceParent a b) := by
  have hroots : rho.normalRoot a ≠ rho.normalRoot b :=
    fun h => hne ((rho.eqvOn_iff_normalRoot_eq ha hb).mpr h)
  have hba : rho.normalRoot b ≠ a := by
    intro h
    apply hne
    exact EqvOn.symm (EqvOn.of_reach hb ha (h ▸ (rho.normalRoot_spec b).1))
  have htemp : Terminating (extendPar rho.par a b) :=
    terminating_extendPar_of_no_return rho.term
      (fun h => hne (EqvOn.symm (EqvOn.of_reach hb ha h)))
  apply terminating_extendPar_of_no_return htemp
  intro h
  have hs : extendPar rho.par a b (rho.normalRoot b) = none := by
    rw [extendPar_of_ne hba]
    exact (rho.normalRoot_spec b).2
  exact hroots (h.toParentPath.eq_of_none hs).symm

/-- Every splice edge is one of the two specified replacements or an old
edge with neither replacement source. -/
theorem PGraph.spliceParent_edge
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b x y : Term (sigma ⊕ sigma) nu}
    (h : rho.spliceParent a b x = some y) :
    (x = rho.normalRoot a ∧ y = rho.normalRoot b) ∨
      (x ≠ rho.normalRoot a ∧ x = a ∧ y = b) ∨
      (x ≠ rho.normalRoot a ∧ x ≠ a ∧ rho.par x = some y) := by
  classical
  by_cases hr : x = rho.normalRoot a
  · subst x
    exact Or.inl ⟨rfl, (Option.some.inj
      ((extendPar_self (extendPar rho.par a b) _ _).symm.trans h)).symm⟩
  · have h' : extendPar rho.par a b x = some y :=
      (extendPar_of_ne hr).symm.trans h
    by_cases hx : x = a
    · subst x
      exact Or.inr (Or.inl ⟨hr, rfl,
        (Option.some.inj ((extendPar_self rho.par a b).symm.trans h')).symm⟩)
    · exact Or.inr (Or.inr ⟨hr, hx, (extendPar_of_ne hx).symm.trans h'⟩)

theorem PGraph.spliceParent_mem
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b x y : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (h : rho.spliceParent a b x = some y) :
    x ∈ A ∧ y ∈ A := by
  rcases rho.spliceParent_edge h with ⟨rfl, rfl⟩ |
    ⟨_, rfl, rfl⟩ | ⟨_, _, hold⟩
  · exact ⟨rho.normalRoot_mem ha, rho.normalRoot_mem hb⟩
  · exact ⟨ha, hb⟩
  · exact rho.mem_edge hold

/-- The replacement retains every old equality, including the displaced
parent equation. No reversal of a rewrite step is used. -/
theorem PGraph.spliceParent_preserves
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : EqvOn A rho.par x y) :
    EqvOn A (rho.spliceParent a b) x y := by
  have hnewRoot : rho.spliceParent a b (rho.normalRoot a) =
      some (rho.normalRoot b) := extendPar_self _ _ _
  have bPath : Reach (rho.spliceParent a b) b (rho.normalRoot b) := by
    rcases (rho.normalRoot_spec b).1.extend_of_not_reach (a := a) (b := b) with
      hkeep | hreturn
    · rcases hkeep.extend_of_not_reach
        (a := rho.normalRoot a) (b := rho.normalRoot b) with hkeep | hreturn
      · exact hkeep
      · have noNew : ∀ {p q}, Reach (extendPar rho.par a b) p q →
            ¬ Reach rho.par p a → Reach rho.par p q := by
          intro p q h
          induction h with
          | refl => intro _; exact Reach.refl _
          | @head p c q he _ ih =>
              intro hno
              have hp : p ≠ a := by intro h; subst p; exact hno (Reach.refl a)
              have hold := (extendPar_of_ne hp).symm.trans he
              exact Reach.head hold (ih (fun h => hno (Reach.head hold h)))
        have hba : ¬ Reach rho.par b a :=
          fun h => hne (EqvOn.symm (EqvOn.of_reach hb ha h))
        exact (hne ⟨ha, hb, rho.normalRoot a, (rho.normalRoot_spec a).1,
          noNew hreturn hba⟩).elim
    · exact (hne (EqvOn.symm (EqvOn.of_reach hb ha hreturn))).elim
  apply EqvOn.mono_of_parent_eqv ?_ hxy
  intro p q hpq
  have hp := (rho.mem_edge hpq).1
  have hq := (rho.mem_edge hpq).2
  by_cases hpa : p = a
  · subst p
    have haRoot : a ≠ rho.normalRoot a := by
      intro h
      have hn : rho.par a = none := h ▸ (rho.normalRoot_spec a).2
      rw [hn] at hpq
      cases hpq
    have hnewA : rho.spliceParent a b a = some b := by
      change extendPar (extendPar rho.par a b) _ _ a = some b
      rw [extendPar_of_ne haRoot, extendPar_self]
    have qPath : Reach (rho.spliceParent a b) q (rho.normalRoot b) := by
      have hqr : Reach rho.par q (rho.normalRoot a) := by
        rw [rho.normalRoot_eq_of_reach (Reach.head hpq (Reach.refl q))]
        exact (rho.normalRoot_spec q).1
      rcases hqr.extend_of_not_reach (a := a) (b := b) with htemp | hreturn
      · have htoRoot : Reach (rho.spliceParent a b) q (rho.normalRoot a) := by
          have hp := htemp.toParentPath.replace_to_source (b := rho.normalRoot b)
          apply (hp.mono ?_).toReach
          intro x y he
          by_cases hx : x = rho.normalRoot a
          · subst x
            have hy : y = rho.normalRoot b :=
              (Option.some.inj ((ParentReplacement.replace_self _ _ _).symm.trans he)).symm
            subst y
            exact extendPar_self _ _ _
          · exact (extendPar_of_ne hx).trans
              ((ParentReplacement.replace_of_ne hx).symm.trans he)
        exact htoRoot.trans (Reach.head hnewRoot (Reach.refl _))
      · exact (rho.term.no_parent_cycle hpq hreturn).elim
    exact ⟨ha, hq, rho.normalRoot b, Reach.head hnewA bPath, qPath⟩
  · have hpr : p ≠ rho.normalRoot a := by
      intro h
      subst p
      rw [(rho.normalRoot_spec a).2] at hpq
      cases hpq
    exact EqvOn.of_reach hp hq (Reach.head (by
      change extendPar (extendPar rho.par a b) _ _ p = some q
      rw [extendPar_of_ne hpr, extendPar_of_ne hpa]
      exact hpq) (Reach.refl q))

/-- The splice represents the requested equation between different old classes. -/
theorem PGraph.spliceParent_new
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b) :
    EqvOn A (rho.spliceParent a b) a b := by
  have har := rho.spliceParent_preserves ha hb hne
    (EqvOn.of_reach ha (rho.normalRoot_mem ha) (rho.normalRoot_spec a).1)
  have hbs := rho.spliceParent_preserves ha hb hne
    (EqvOn.of_reach hb (rho.normalRoot_mem hb) (rho.normalRoot_spec b).1)
  have hrs : EqvOn A (rho.spliceParent a b) (rho.normalRoot a) (rho.normalRoot b) :=
    EqvOn.of_reach (rho.normalRoot_mem ha) (rho.normalRoot_mem hb)
      (Reach.head (extendPar_self _ _ _) (Reach.refl _))
  exact har.trans (hrs.trans hbs.symm)

/-- Merge exactly the two old equivalence classes, leaving all others unchanged. -/
def PGraph.SpliceEq
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a b : Term (sigma ⊕ sigma) nu) : CRel sigma nu :=
  fun x y => EqvOn A rho.par x y ∨
    (EqvOn A rho.par x a ∧ EqvOn A rho.par b y) ∨
    (EqvOn A rho.par x b ∧ EqvOn A rho.par a y)

theorem PGraph.SpliceEq.symm
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a b x y : Term (sigma ⊕ sigma) nu}
    (h : rho.SpliceEq a b x y) : rho.SpliceEq a b y x := by
  rcases h with h | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨hby.symm, hxa.symm⟩)
  · exact Or.inr (Or.inl ⟨hay.symm, hxb.symm⟩)

theorem PGraph.SpliceEq.trans
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a b x y z : Term (sigma ⊕ sigma) nu}
    (hxy : rho.SpliceEq a b x y) (hyz : rho.SpliceEq a b y z) :
    rho.SpliceEq a b x z := by
  rcases hxy with hxy | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
  · rcases hyz with hyz | ⟨hya, hbz⟩ | ⟨hyb, haz⟩
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr (Or.inl ⟨hxy.trans hya, hbz⟩)
    · exact Or.inr (Or.inr ⟨hxy.trans hyb, haz⟩)
  · rcases hyz with hyz | ⟨_, hbz⟩ | ⟨_, haz⟩
    · exact Or.inr (Or.inl ⟨hxa, hby.trans hyz⟩)
    · exact Or.inr (Or.inl ⟨hxa, hbz⟩)
    · exact Or.inl (hxa.trans haz)
  · rcases hyz with hyz | ⟨_, hbz⟩ | ⟨_, haz⟩
    · exact Or.inr (Or.inr ⟨hxb, hay.trans hyz⟩)
    · exact Or.inl (hxb.trans hbz)
    · exact Or.inr (Or.inr ⟨hxb, haz⟩)

/-- The actual two-edge parent has exactly the merged-class equality. -/
theorem PGraph.spliceParent_eqv_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b x y : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b) :
    EqvOn A (rho.spliceParent a b) x y ↔ rho.SpliceEq a b x y := by
  have hedge : ∀ {p q}, rho.spliceParent a b p = some q → rho.SpliceEq a b p q := by
    intro p q hpq
    rcases rho.spliceParent_edge hpq with ⟨rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, hold⟩
    · exact Or.inr (Or.inl ⟨
        (EqvOn.of_reach ha (rho.normalRoot_mem ha) (rho.normalRoot_spec a).1).symm,
        EqvOn.of_reach hb (rho.normalRoot_mem hb) (rho.normalRoot_spec b).1⟩)
    · exact Or.inr (Or.inl ⟨EqvOn.refl ha, EqvOn.refl hb⟩)
    · exact Or.inl (EqvOn.of_reach (rho.mem_edge hold).1 (rho.mem_edge hold).2
        (Reach.head hold (Reach.refl _)))
  have route : ∀ {p q}, Reach (rho.spliceParent a b) p q → p ∈ A →
      rho.SpliceEq a b p q := by
    intro p q hpq
    induction hpq with
    | refl => intro hp; exact Or.inl (EqvOn.refl hp)
    | head he _ ih =>
        intro _
        exact (hedge he).trans (ih (rho.spliceParent_mem ha hb he).2)
  constructor
  · rintro ⟨hx, hy, r, hxr, hyr⟩
    exact (route hxr hx).trans (route hyr hy).symm
  · intro h
    have hab := rho.spliceParent_new ha hb hne
    rcases h with hold | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
    · exact rho.spliceParent_preserves ha hb hne hold
    · exact (rho.spliceParent_preserves ha hb hne hxa).trans
        (hab.trans (rho.spliceParent_preserves ha hb hne hby))
    · exact (rho.spliceParent_preserves ha hb hne hxb).trans
        (hab.symm.trans (rho.spliceParent_preserves ha hb hne hay))

/-- If constructors were roots, the splice introduces only one possible
constructor equality: equality between the two joined roots. -/
theorem PGraph.spliceParent_constructor_pair
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R)
    (hcnf : ∀ {c}, ConTopped c → rho.NF c)
    {a b x y : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hx : ConTopped x) (hy : ConTopped y)
    (hxy : EqvOn A (rho.spliceParent a b) x y) :
    x = y ∨ (x = rho.normalRoot a ∧ y = rho.normalRoot b) ∨
      (x = rho.normalRoot b ∧ y = rho.normalRoot a) := by
  have endpoint : ∀ {p q}, ConTopped p → EqvOn A rho.par p q →
      p = rho.normalRoot q := by
    intro p q hp hpq
    have hn : rho.normalRoot p = p :=
      ((rho.normalRoot_spec p).1.toParentPath.eq_of_none (hcnf hp)).symm
    exact hn.symm.trans ((rho.eqvOn_iff_normalRoot_eq hpq.mem.1 hpq.mem.2).mp hpq)
  rcases (rho.spliceParent_eqv_iff ha hb hne).mp hxy with h | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
  · obtain ⟨_, _, r, hxr, hyr⟩ := h
    exact Or.inl ((hxr.toParentPath.eq_of_none (hcnf hx)).trans
      (hyr.toParentPath.eq_of_none (hcnf hy)).symm)
  · exact Or.inr (Or.inl ⟨endpoint hx hxa, endpoint hy hby.symm⟩)
  · exact Or.inr (Or.inr ⟨endpoint hx hxb, endpoint hy hay.symm⟩)

/-- Two independently justified replacements construct one sound graph when
constructors were roots. Both local edge conditions use the explicit class
merge, not an assumed final proof graph. -/
noncomputable def PGraph.spliceGraph
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hR : ConstructorRules R)
    (hcnf : ∀ {c}, ConTopped c → rho.NF c)
    {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b)
    (hroots : hatEq (rho.SpliceEq a b) (rho.normalRoot a) (rho.normalRoot b))
    (hsound : DownOn A R (rho.normalRoot a) (rho.normalRoot b)) : PGraph A R := by
  have hg : ∀ {x y}, rho.spliceParent a b x = some y →
      Grey A R (EqvOn A (rho.spliceParent a b)) x y := by
    intro x y he
    rcases rho.spliceParent_edge he with ⟨rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, hold⟩
    · exact Or.inr (Or.inr (hatEq.mono (fun _ _ h =>
        (rho.spliceParent_eqv_iff ha hb hne).mpr h) hroots))
    · exact Grey.mono (fun _ _ h => rho.spliceParent_preserves ha hb hne h) hab
    · exact Grey.mono (fun _ _ h => rho.spliceParent_preserves ha hb hne h) (rho.grey hold)
  have hsub : ∀ {x y}, EqvOn A (rho.spliceParent a b) x y → DownOn A R x y := by
    apply eqvOn_downOn_of_constructorSlice hR
      (fun h => rho.spliceParent_mem ha hb h) hg
    intro x y hx hy hxy
    rcases rho.spliceParent_constructor_pair hcnf ha hb hne hx hy hxy with
      rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact DownOn.refl hxy.mem.1
    · exact hsound
    · exact hsound.symm
  exact {
    par := rho.spliceParent a b
    mem_edge := fun h => rho.spliceParent_mem ha hb h
    term := rho.spliceParent_terminating ha hb hne
    sub := hsub
    grey := hg }

/-- A constructor splice preserves tightness, every old equation and every
represented root contraction on the same carrier. -/
theorem PGraph.exists_constructor_splice
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hR : ConstructorRules R) (htight : rho.Tight)
    (hcnf : ∀ {c}, ConTopped c → rho.NF c)
    {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : TightEdge R (EqvOn A rho.par) a b)
    (hroots : hatEq (rho.SpliceEq a b) (rho.normalRoot a) (rho.normalRoot b))
    (hsound : DownOn A R (rho.normalRoot a) (rho.normalRoot b)) :
    ∃ beta : PGraph A R, beta.par = rho.spliceParent a b ∧ beta.Tight ∧
      rho.EqualityExtends beta ∧ EqvOn A beta.par a b ∧
      (∀ x y, EqvOn A beta.par x y ↔ rho.SpliceEq a b x y) ∧
      (RootStepsRepresented A R rho → RootStepsRepresented A R beta) := by
  let beta := rho.spliceGraph hR hcnf ha hb hne (hab.toGrey rho) hroots hsound
  have hpar : beta.par = rho.spliceParent a b := rfl
  have hext : rho.EqualityExtends beta :=
    fun _ _ h => rho.spliceParent_preserves ha hb hne h
  have ht : beta.Tight := by
    intro x y he
    change rho.spliceParent a b x = some y at he
    rcases rho.spliceParent_edge he with ⟨rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, hold⟩
    · exact Or.inr (Or.inr (hatEq.mono (fun _ _ h =>
        (rho.spliceParent_eqv_iff ha hb hne).mpr h) hroots))
    · exact hab.mono (fun _ _ h => hext h)
    · exact (htight hold).mono (fun _ _ h => hext h)
  exact ⟨beta, hpar, ht, hext, rho.spliceParent_new ha hb hne,
    fun _ _ => rho.spliceParent_eqv_iff ha hb hne, fun hroot => hroot.mono hext⟩

/-- Distinct old classes are the exact condition for splice termination.
Joining a class to itself creates a self-loop at its old root. -/
theorem PGraph.spliceParent_terminating_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) :
    Terminating (rho.spliceParent a b) ↔ ¬ EqvOn A rho.par a b := by
  constructor
  · intro hwf hab
    have hr := (rho.eqvOn_iff_normalRoot_eq ha hb).mp hab
    have he : rho.spliceParent a b (rho.normalRoot a) = some (rho.normalRoot a) := by
      change extendPar (extendPar rho.par a b) (rho.normalRoot a)
        (rho.normalRoot b) (rho.normalRoot a) = some (rho.normalRoot a)
      rw [extendPar_self, hr]
    exact hwf.no_parent_cycle he (Reach.refl _)
  · exact rho.spliceParent_terminating ha hb

/-- Only constructor pairs crossing the two selected old classes need new
soundness proofs. Old constructor paths may be nonempty. -/
def PGraph.CrossConstructorSound
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a b : Term (sigma ⊕ sigma) nu) : Prop :=
  ∀ {x y}, ConTopped x → ConTopped y →
    EqvOn A rho.par x a → EqvOn A rho.par b y → DownOn A R x y

/-- The old edge and the new root edge give the complete Grey classification
of the constructed parent, with no constructor normal-form restriction. -/
theorem PGraph.spliceParent_grey
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b)
    (hroots : Grey A R (rho.SpliceEq a b) (rho.normalRoot a) (rho.normalRoot b))
    {x y : Term (sigma ⊕ sigma) nu} (he : rho.spliceParent a b x = some y) :
    Grey A R (EqvOn A (rho.spliceParent a b)) x y := by
  rcases rho.spliceParent_edge he with ⟨rfl, rfl⟩ |
    ⟨_, rfl, rfl⟩ | ⟨_, _, hold⟩
  · exact Grey.mono (fun _ _ h => (rho.spliceParent_eqv_iff ha hb hne).mpr h) hroots
  · exact Grey.mono (fun _ _ h => rho.spliceParent_preserves ha hb hne h) hab
  · exact Grey.mono (fun _ _ h => rho.spliceParent_preserves ha hb hne h) (rho.grey hold)

/-- Cross-class constructor soundness is necessary and sufficient for full
soundness of this explicit splice. No soundness of a transitive union is assumed. -/
theorem PGraph.spliceParent_sound_iff_crossConstructorSound
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b)
    (hroots : Grey A R (rho.SpliceEq a b) (rho.normalRoot a) (rho.normalRoot b)) :
    (∀ {x y}, EqvOn A (rho.spliceParent a b) x y → DownOn A R x y) ↔
      rho.CrossConstructorSound a b := by
  constructor
  · intro h x y _ _ hxa hby
    exact h ((rho.spliceParent_eqv_iff ha hb hne).mpr (Or.inr (Or.inl ⟨hxa, hby⟩)))
  · intro hcross x y hxy
    apply eqvOn_downOn_of_constructorSlice hR
      (fun h => rho.spliceParent_mem ha hb h)
      (fun h => rho.spliceParent_grey ha hb hne hab hroots h) ?_ hxy
    intro p q hp hq hpq
    rcases (rho.spliceParent_eqv_iff ha hb hne).mp hpq with hold | ⟨hpa, hbq⟩ | ⟨hpb, haq⟩
    · exact rho.sub hold
    · exact hcross hp hq hpa hbq
    · exact (hcross hq hp haq.symm hpb.symm).symm

/-- Construct the sound graph from exactly the newly required constructor
pairs. Root-step, destructor and constructor root edges are all admitted. -/
noncomputable def PGraph.spliceGraphOfCrossSlice
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : Grey A R (EqvOn A rho.par) a b)
    (hroots : Grey A R (rho.SpliceEq a b) (rho.normalRoot a) (rho.normalRoot b))
    (hcross : rho.CrossConstructorSound a b) : PGraph A R where
  par := rho.spliceParent a b
  mem_edge := fun h => rho.spliceParent_mem ha hb h
  term := rho.spliceParent_terminating ha hb hne
  sub := (rho.spliceParent_sound_iff_crossConstructorSound hR ha hb hne hab hroots).mpr hcross
  grey := fun h => rho.spliceParent_grey ha hb hne hab hroots h

/-- Tightness uses represented argument equalities in addition to the semantic
Grey evidence needed by destructor edges. Every old equation survives. -/
theorem PGraph.exists_splice_of_crossSlice
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hR : ConstructorRules R) (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) (hne : ¬ EqvOn A rho.par a b)
    (hab : TightEdge R (EqvOn A rho.par) a b)
    (hrootGrey : Grey A R (rho.SpliceEq a b) (rho.normalRoot a) (rho.normalRoot b))
    (hrootTight : TightEdge R (rho.SpliceEq a b) (rho.normalRoot a) (rho.normalRoot b))
    (hcross : rho.CrossConstructorSound a b) :
    ∃ beta : PGraph A R, beta.par = rho.spliceParent a b ∧ beta.Tight ∧
      rho.EqualityExtends beta ∧ EqvOn A beta.par a b ∧
      (∀ x y, EqvOn A beta.par x y ↔ rho.SpliceEq a b x y) ∧
      (RootStepsRepresented A R rho → RootStepsRepresented A R beta) := by
  let beta := rho.spliceGraphOfCrossSlice hR ha hb hne (hab.toGrey rho) hrootGrey hcross
  have hext : rho.EqualityExtends beta :=
    fun _ _ h => rho.spliceParent_preserves ha hb hne h
  have ht : beta.Tight := by
    intro x y he
    change rho.spliceParent a b x = some y at he
    rcases rho.spliceParent_edge he with ⟨rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, hold⟩
    · exact hrootTight.mono (fun _ _ h => (rho.spliceParent_eqv_iff ha hb hne).mpr h)
    · exact hab.mono (fun _ _ h => hext h)
    · exact (htight hold).mono (fun _ _ h => hext h)
  exact ⟨beta, rfl, ht, hext, rho.spliceParent_new ha hb hne,
    fun _ _ => rho.spliceParent_eqv_iff ha hb hne, fun hroot => hroot.mono hext⟩

/-- The constructor-root case supplies the general cross-class criterion
from the independent proof of the two roots' relation. -/
theorem PGraph.crossConstructorSound_of_constructor_roots
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R)
    (hcnf : ∀ {c}, ConTopped c → rho.NF c)
    {a b : Term (sigma ⊕ sigma) nu}
    (hsound : DownOn A R (rho.normalRoot a) (rho.normalRoot b)) :
    rho.CrossConstructorSound a b := by
  intro x y hx hy hxa hby
  have hxroot : x = rho.normalRoot a :=
    ((rho.normalRoot_spec x).1.toParentPath.eq_of_none (hcnf hx)).trans
      ((rho.eqvOn_iff_normalRoot_eq hxa.mem.1 hxa.mem.2).mp hxa)
  have hyroot : y = rho.normalRoot b :=
    ((rho.normalRoot_spec y).1.toParentPath.eq_of_none (hcnf hy)).trans
      ((rho.eqvOn_iff_normalRoot_eq hby.mem.2 hby.mem.1).mp hby.symm)
  rw [hxroot, hyroot]
  exact hsound

/-! ## Simultaneous joins at old roots -/

/-- Retain every old parent edge and install the entire root parent at once. -/
noncomputable def PGraph.rootGraft
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R)
    (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)) :
    Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu) :=
  fun x => match rho.par x with
    | some y => some y
    | none => q x

theorem PGraph.rootGraft_old_edge
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    {x y : Term (sigma ⊕ sigma) nu} (h : rho.par x = some y) :
    rho.rootGraft q x = some y := by simp only [rootGraft, h]

theorem PGraph.rootGraft_root_edge
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    {x y : Term (sigma ⊕ sigma) nu} (hn : rho.NF x) (h : q x = some y) :
    rho.rootGraft q x = some y := by
  change rho.par x = none at hn
  simp only [rootGraft, hn, h]

theorem PGraph.rootGraft_edge_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    {x y : Term (sigma ⊕ sigma) nu} :
    rho.rootGraft q x = some y ↔ rho.par x = some y ∨ (rho.NF x ∧ q x = some y) := by
  cases hx : rho.par x with
  | none => simp [rootGraft, PGraph.NF, hx]
  | some z => simp [rootGraft, PGraph.NF, hx]

private theorem PGraph.root_eq_self_of_nf
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {x : Term (sigma ⊕ sigma) nu} (hx : rho.NF x) :
    rho.normalRoot x = x := ((rho.normalRoot_spec x).1.toParentPath.eq_of_none hx).symm

/-- Installing all root edges terminates exactly when their own parent does;
no intermediate root join is required to form a proof graph. -/
theorem PGraph.rootGraft_terminating_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hroots : ∀ {x y}, q x = some y → rho.NF x ∧ rho.NF y) :
    Terminating (rho.rootGraft q) ↔ Terminating q := by
  constructor
  · intro h
    exact Subrelation.wf (fun {_ _} he => rho.rootGraft_root_edge q (hroots he).1 he) h
  · intro hq
    have main : ∀ r, ∀ x, rho.normalRoot x = r →
        Acc (fun y x => rho.rootGraft q x = some y) x := by
      intro r
      induction r using hq.induction with
      | _ r ihq =>
          intro x
          induction x using rho.term.induction with
          | _ x ihold =>
              intro hxr
              refine Acc.intro x ?_
              intro y hy
              rcases (rho.rootGraft_edge_iff q).mp hy with hold | ⟨hx, hnew⟩
              · exact ihold y hold ((rho.normalRoot_eq_of_reach
                  (Reach.head hold (Reach.refl y))).symm.trans hxr)
              · have hxeq : x = r := (rho.root_eq_self_of_nf hx).symm.trans hxr
                exact ihq y (hxeq ▸ hnew) y (rho.root_eq_self_of_nf (hroots hnew).2)
    exact ⟨fun x => main (rho.normalRoot x) x rfl⟩

theorem PGraph.rootGraft_mem
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hmem : ∀ {x y}, q x = some y → x ∈ A ∧ y ∈ A)
    {x y : Term (sigma ⊕ sigma) nu} (h : rho.rootGraft q x = some y) : x ∈ A ∧ y ∈ A := by
  rcases (rho.rootGraft_edge_iff q).mp h with hold | ⟨_, hnew⟩
  · exact rho.mem_edge hold
  · exact hmem hnew

/-- Project the complete installed path to a path between old roots. -/
theorem PGraph.rootGraft_reach_roots
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hroots : ∀ {x y}, q x = some y → rho.NF x ∧ rho.NF y)
    {x y : Term (sigma ⊕ sigma) nu} (h : Reach (rho.rootGraft q) x y) :
    Reach q (rho.normalRoot x) (rho.normalRoot y) := by
  induction h with
  | refl x => exact Reach.refl _
  | @head x z y hxz _ ih =>
      rcases (rho.rootGraft_edge_iff q).mp hxz with hold | ⟨hx, hnew⟩
      · rw [rho.normalRoot_eq_of_reach (Reach.head hold (Reach.refl _))]
        exact ih
      · rw [rho.root_eq_self_of_nf hx, rho.root_eq_self_of_nf (hroots hnew).2] at *
        exact Reach.head hnew ih

/-- The full installed equality is exactly the root-parent equality lifted
through the old normal-root map. -/
theorem PGraph.rootGraft_eqv_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hroots : ∀ {x y}, q x = some y → rho.NF x ∧ rho.NF y)
    {x y : Term (sigma ⊕ sigma) nu} :
    EqvOn A (rho.rootGraft q) x y ↔
      x ∈ A ∧ y ∈ A ∧ EqvOn A q (rho.normalRoot x) (rho.normalRoot y) := by
  constructor
  · rintro ⟨hx, hy, z, hxz, hyz⟩
    exact ⟨hx, hy, rho.normalRoot_mem hx, rho.normalRoot_mem hy, rho.normalRoot z,
      rho.rootGraft_reach_roots q hroots hxz, rho.rootGraft_reach_roots q hroots hyz⟩
  · rintro ⟨hx, hy, _, _, z, hxz, hyz⟩
    have old : ∀ {p r}, Reach rho.par p r → Reach (rho.rootGraft q) p r := by
      intro p r h
      exact (h.toParentPath.mono (fun he => rho.rootGraft_old_edge q he)).toReach
    have added : ∀ {p r}, Reach q p r → Reach (rho.rootGraft q) p r := by
      intro p r h
      exact (h.toParentPath.mono (fun he => rho.rootGraft_root_edge q (hroots he).1 he)).toReach
    exact ⟨hx, hy, z, (old (rho.normalRoot_spec x).1).trans (added hxz),
      (old (rho.normalRoot_spec y).1).trans (added hyz)⟩

/-- Every old equation survives literally retaining every old parent edge. -/
theorem PGraph.rootGraft_preserves
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    {x y : Term (sigma ⊕ sigma) nu} (h : EqvOn A rho.par x y) :
    EqvOn A (rho.rootGraft q) x y := EqvOn.mono (fun _ _ he => rho.rootGraft_old_edge q he) h

/-- Equality installed by a batch of root joins. -/
def PGraph.RootGraftEq
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)) :
    CRel sigma nu := fun x y =>
      x ∈ A ∧ y ∈ A ∧ EqvOn A q (rho.normalRoot x) (rho.normalRoot y)

/-- All newly installed constructor pairs are checked together. -/
def PGraph.RootGraftConstructorSound
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)) : Prop :=
  ∀ {x y}, ConTopped x → ConTopped y → rho.RootGraftEq q x y → DownOn A R x y

/-- Final Grey evidence is checked after every mutually dependent join is
installed. This does not infer semantic soundness from that evidence. -/
theorem PGraph.rootGraft_grey
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hroots : ∀ {x y}, q x = some y → rho.NF x ∧ rho.NF y)
    (hgrey : ∀ {x y}, q x = some y → Grey A R (rho.RootGraftEq q) x y)
    {x y : Term (sigma ⊕ sigma) nu} (he : rho.rootGraft q x = some y) :
    Grey A R (EqvOn A (rho.rootGraft q)) x y := by
  rcases (rho.rootGraft_edge_iff q).mp he with hold | ⟨_, hnew⟩
  · exact Grey.mono (fun _ _ h => rho.rootGraft_preserves q h) (rho.grey hold)
  · exact Grey.mono (fun _ _ h => (rho.rootGraft_eqv_iff q hroots).mpr h) (hgrey hnew)

theorem PGraph.rootGraft_sound_iff_constructorSound
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hR : ConstructorRules R)
    (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hroots : ∀ {x y}, q x = some y → rho.NF x ∧ rho.NF y)
    (hmem : ∀ {x y}, q x = some y → x ∈ A ∧ y ∈ A)
    (hgrey : ∀ {x y}, q x = some y → Grey A R (rho.RootGraftEq q) x y) :
    (∀ {x y}, EqvOn A (rho.rootGraft q) x y → DownOn A R x y) ↔
      rho.RootGraftConstructorSound q := by
  constructor
  · intro h x y _ _ hxy
    exact h ((rho.rootGraft_eqv_iff q hroots).mpr hxy)
  · intro h
    apply eqvOn_downOn_of_constructorSlice hR
      (fun he => rho.rootGraft_mem q hmem he) (fun he => rho.rootGraft_grey q hroots hgrey he)
    intro x y hx hy hxy
    exact h hx hy ((rho.rootGraft_eqv_iff q hroots).mp hxy)

/-- A simultaneous batch constructs one tight proof graph while preserving
every old equation and every represented root contraction. -/
theorem PGraph.exists_rootGraft
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hR : ConstructorRules R) (htight : rho.Tight)
    (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))
    (hroots : ∀ {x y}, q x = some y → rho.NF x ∧ rho.NF y)
    (hmem : ∀ {x y}, q x = some y → x ∈ A ∧ y ∈ A) (hq : Terminating q)
    (hgrey : ∀ {x y}, q x = some y → Grey A R (rho.RootGraftEq q) x y)
    (ht : ∀ {x y}, q x = some y → TightEdge R (rho.RootGraftEq q) x y)
    (hsound : rho.RootGraftConstructorSound q) :
    ∃ beta : PGraph A R, beta.par = rho.rootGraft q ∧ beta.Tight ∧
      rho.EqualityExtends beta ∧
      (∀ x y, EqvOn A beta.par x y ↔ rho.RootGraftEq q x y) ∧
      (RootStepsRepresented A R rho → RootStepsRepresented A R beta) := by
  let beta : PGraph A R := {
    par := rho.rootGraft q
    mem_edge := fun he => rho.rootGraft_mem q hmem he
    term := (rho.rootGraft_terminating_iff q hroots).mpr hq
    sub := (rho.rootGraft_sound_iff_constructorSound hR q hroots hmem hgrey).mpr hsound
    grey := fun he => rho.rootGraft_grey q hroots hgrey he }
  have hext : rho.EqualityExtends beta := fun _ _ h => rho.rootGraft_preserves q h
  have htightBeta : beta.Tight := by
    intro x y he
    rcases (rho.rootGraft_edge_iff q).mp he with hold | ⟨_, hnew⟩
    · exact (htight hold).mono (fun _ _ h => hext h)
    · exact (ht hnew).mono (fun _ _ h => (rho.rootGraft_eqv_iff q hroots).mpr h)
  exact ⟨beta, rfl, htightBeta, hext,
    fun _ _ => rho.rootGraft_eqv_iff q hroots, fun hroot => hroot.mono hext⟩

namespace PGraph

section InternalTargets

variable {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R)
    (q : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu))

/-- Compress each selected target to its old root for the termination test.
The installed graph still uses the original target. -/
noncomputable def rootRouting : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu) :=
  fun x => (q x).map rho.normalRoot

theorem rootRouting_edge_iff {x z : Term (sigma ⊕ sigma) nu} :
    rho.rootRouting q x = some z ↔ ∃ y, q x = some y ∧ rho.normalRoot y = z := by
  cases h : q x <;> simp [rootRouting, h]

theorem rootRouting_step {x y : Term (sigma ⊕ sigma) nu} (h : q x = some y) :
    rho.rootRouting q x = some (rho.normalRoot y) := by simp [rootRouting, h]

private theorem rootGraft_old_reach {x y : Term (sigma ⊕ sigma) nu} (h : Reach rho.par x y) :
    Reach (rho.rootGraft q) x y :=
  (h.toParentPath.mono (fun he => rho.rootGraft_old_edge q he)).toReach

/-- Targets may lie inside old parent paths. Termination is equivalent to
termination after compressing those targets, not to termination of q alone. -/
theorem rootGraft_terminating_iff_routing
    (hsrc : ∀ {x y}, q x = some y → rho.NF x) :
    Terminating (rho.rootGraft q) ↔ Terminating (rho.rootRouting q) := by
  constructor
  · intro hg
    apply Subrelation.wf (r := Relation.TransGen
      (fun y x => rho.rootGraft q x = some y)) ?_ hg.transGen
    intro z x h
    obtain ⟨y, hxy, rfl⟩ := (rho.rootRouting_edge_iff q).mp h
    exact Relation.TransGen.tail'
      ((rho.rootGraft_old_reach q (rho.normalRoot_spec y).1).toParentPath.toReflTransGenRev)
      (rho.rootGraft_root_edge q (hsrc hxy) hxy)
  · intro hq
    have main : ∀ r, ∀ x, rho.normalRoot x = r →
        Acc (fun y x => rho.rootGraft q x = some y) x := by
      intro r
      induction r using hq.induction with
      | _ r ihq =>
          intro x
          induction x using rho.term.induction with
          | _ x ihold =>
              intro hxr
              refine Acc.intro x ?_
              intro y hy
              rcases (rho.rootGraft_edge_iff q).mp hy with hold | ⟨hx, hnew⟩
              · exact ihold y hold ((rho.normalRoot_eq_of_reach
                  (Reach.head hold (Reach.refl y))).symm.trans hxr)
              · have hxeq : x = r := (rho.root_eq_self_of_nf hx).symm.trans hxr
                exact ihq (rho.normalRoot y) (hxeq ▸ rho.rootRouting_step q hnew) y rfl
    exact ⟨fun x => main (rho.normalRoot x) x rfl⟩

theorem rootGraft_reach_routing
    {x y : Term (sigma ⊕ sigma) nu} (h : Reach (rho.rootGraft q) x y) :
    Reach (rho.rootRouting q) (rho.normalRoot x) (rho.normalRoot y) := by
  induction h with
  | refl x => exact Reach.refl _
  | @head x z y he _ ih =>
      rcases (rho.rootGraft_edge_iff q).mp he with hold | ⟨hx, hnew⟩
      · rw [rho.normalRoot_eq_of_reach (Reach.head hold (Reach.refl _))]
        exact ih
      · rw [rho.root_eq_self_of_nf hx]
        exact Reach.head (rho.rootRouting_step q hnew) ih

/-- Every compressed edge expands to its selected edge followed by the
unchanged old path. Thus compression does not invent an executable edge. -/
theorem rootGraft_routing_reach
    (hsrc : ∀ {x y}, q x = some y → rho.NF x)
    {x y : Term (sigma ⊕ sigma) nu} (h : Reach (rho.rootRouting q) x y) :
    Reach (rho.rootGraft q) x y := by
  induction h with
  | refl x => exact Reach.refl _
  | @head x z y he _ ih =>
      obtain ⟨p, hxp, rfl⟩ := (rho.rootRouting_edge_iff q).mp he
      exact Reach.head (rho.rootGraft_root_edge q (hsrc hxp) hxp)
        ((rho.rootGraft_old_reach q (rho.normalRoot_spec p).1).trans ih)

/-- The exact represented equality for simultaneous joins with internal
targets. Neither a target-root premise nor a one-pair restriction is used. -/
theorem rootGraft_eqv_iff_routing
    (hsrc : ∀ {x y}, q x = some y → rho.NF x)
    {x y : Term (sigma ⊕ sigma) nu} :
    EqvOn A (rho.rootGraft q) x y ↔ rho.RootGraftEq (rho.rootRouting q) x y := by
  constructor
  · rintro ⟨hx, hy, z, hxz, hyz⟩
    exact ⟨hx, hy, rho.normalRoot_mem hx, rho.normalRoot_mem hy, rho.normalRoot z,
      rho.rootGraft_reach_routing q hxz, rho.rootGraft_reach_routing q hyz⟩
  · rintro ⟨hx, hy, _, _, z, hxz, hyz⟩
    exact ⟨hx, hy, z,
      (rho.rootGraft_old_reach q (rho.normalRoot_spec x).1).trans
        (rho.rootGraft_routing_reach q hsrc hxz),
      (rho.rootGraft_old_reach q (rho.normalRoot_spec y).1).trans
        (rho.rootGraft_routing_reach q hsrc hyz)⟩

/-- Grey evidence concerns each selected target, while represented argument
equality uses the proved compressed description of the complete graph. -/
theorem rootGraft_grey_of_routing
    (hsrc : ∀ {x y}, q x = some y → rho.NF x)
    (hgrey : ∀ {x y}, q x = some y →
      Grey A R (rho.RootGraftEq (rho.rootRouting q)) x y)
    {x y : Term (sigma ⊕ sigma) nu} (he : rho.rootGraft q x = some y) :
    Grey A R (EqvOn A (rho.rootGraft q)) x y := by
  rcases (rho.rootGraft_edge_iff q).mp he with hold | ⟨_, hnew⟩
  · exact Grey.mono (fun _ _ h => rho.rootGraft_preserves q h) (rho.grey hold)
  · exact Grey.mono (fun _ _ h => (rho.rootGraft_eqv_iff_routing q hsrc).mpr h) (hgrey hnew)

end InternalTargets
end PGraph

end OperatorKO7.Meta.UniqueNormalization
