import OperatorKO7.Meta.UniqueNormalization.Section7SameGraphClosure

/-!
# Section 7 joint closure

This module strengthens proof-graph completion by restricting every non-root
parent edge to a constructor or destructor congruence over the equality already
represented by that graph. Such edges can be reversed without changing the
represented equality. A finite maximal construction and a path-rerooting
construction are proved for arbitrary finite coalgebras. Local signature
closure then forces root-step representation and universality on the same
maximal tight graph of a strongly almost non-omega-overlapping constructor
system.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Tight parent edges -/

/-- A parent edge is tight when it is a root contraction or a one-layer
congruence over the equality represented by the graph itself. -/
def TightEdge (R : TRS (sigma ⊕ sigma) nu) (E : CRel sigma nu) : CRel sigma nu :=
  fun a b => rootStep R a b ∨ barRel E a b ∨ hatEq E a b

/-- Tightness is monotone in the represented relation. -/
theorem TightEdge.mono
    {R : TRS (sigma ⊕ sigma) nu}
    {E E' : CRel sigma nu} (hE : ∀ a b, E a b → E' a b)
    {a b : Term (sigma ⊕ sigma) nu} (h : TightEdge R E a b) :
    TightEdge R E' a b := by
  rcases h with hroot | hbar | hhat
  · exact Or.inl hroot
  · exact Or.inr (Or.inl (tildeOn_mono hE hbar))
  · exact Or.inr (Or.inr (hatEq.mono hE hhat))

/-- A tight edge is a grey edge of the underlying proof graph. -/
theorem TightEdge.toGrey
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (h : TightEdge R (EqvOn A rho.par) a b) :
    Grey A R (EqvOn A rho.par) a b := by
  rcases h with hroot | hbar | hhat
  · exact Or.inl hroot
  · exact Or.inr (Or.inl
      (tildeOn_mono (fun _ _ hxy => rho.sub hxy) hbar))
  · exact Or.inr (Or.inr hhat)

/-- A non-root tight edge is tight in the reverse direction. -/
theorem TightEdge.symm_of_not_root
    {R : TRS (sigma ⊕ sigma) nu}
    {E : CRel sigma nu} (hsymm : ∀ a b, E a b → E b a)
    {a b : Term (sigma ⊕ sigma) nu} (h : TightEdge R E a b)
    (hnot : ¬ rootStep R a b) : TightEdge R E b a := by
  rcases h with hroot | hbar | hhat
  · exact (hnot hroot).elim
  · apply Or.inr
    apply Or.inl
    apply tildeOn_flip
    exact tildeOn_mono (fun _ _ hxy => hsymm _ _ hxy) hbar
  · exact Or.inr (Or.inr (hatEq.symm hsymm hhat))

/-- Every non-root grey edge is reversible. This uses only symmetry of the
finite invariant and of the graph equality; tightness is unnecessary. -/
theorem Grey.symm_of_not_root
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {E : CRel sigma nu} (hE : ∀ a b, E a b → E b a)
    {a b : Term (sigma ⊕ sigma) nu} (h : Grey A R E a b)
    (hnot : ¬ rootStep R a b) : Grey A R E b a := by
  rcases h with hroot | hbar | hhat
  · exact (hnot hroot).elim
  · exact Or.inr (Or.inl
      (tildeOn_flip (tildeOn_mono (fun _ _ hxy => DownOn.symm hxy) hbar)))
  · exact Or.inr (Or.inr (hatEq.symm hE hhat))

/-- Every parent edge of a tight graph has the tight classification. -/
def PGraph.Tight
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) : Prop :=
  ∀ ⦃a b : Term (sigma ⊕ sigma) nu⦄, rho.par a = some b →
    TightEdge R (EqvOn A rho.par) a b

theorem PGraph.empty_tight
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    (PGraph.empty A R).Tight := by
  intro a b h
  cases h

/-- A root-only graph is tight. -/
theorem PGraph.RootOnly.tight
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (honly : rho.RootOnly) : rho.Tight := by
  intro a b h
  exact Or.inl (honly h)

/-- The graph equality satisfies the constructor-compatibility interface used
by the semantic critical-pair theorem. -/
theorem PGraph.constructorCompatible_eqvOn
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) : ConstructorCompatible (EqvOn A rho.par) := by
  intro a b hca hcb hab
  rcases rho.constructorCompatible hA hR hca hcb hab with hvar | hhat
  · exact Or.inl hvar
  · rcases hhat with ⟨f, as, bs, ⟨c, hfc⟩, hha, hhb, hall⟩
    subst hfc
    exact Or.inr ⟨c, as, bs, hha, hhb, hall⟩

/-! ## Tight one-edge extension -/

/-- A tight edge from a graph root can be added while preserving tightness and
all represented equalities. -/
theorem PGraph.Tight.extend_one
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hnf : rho.NF a) (hne : ¬ EqvOn A rho.par a b)
    (hedge : TightEdge R (EqvOn A rho.par) a b) :
    ∃ beta : PGraph A R, beta.Tight ∧ rho.EqualityExtends beta ∧
      beta.par a = some b ∧ EqvOn A beta.par a b := by
  obtain ⟨beta, hpar, hext, hnew⟩ :=
    rho.extend_one_exact hA hR ha hb hnf hne (hedge.toGrey rho)
  have heqMono : rho.EqualityExtends beta := by
    intro x y hxy
    exact EqvOn.mono hext hxy
  have hbetaTight : beta.Tight := by
    intro x y hxy
    rw [hpar] at hxy
    rcases extendPar_edge hxy with ⟨rfl, rfl⟩ | hold
    · exact hedge.mono (fun p q hpq => heqMono hpq)
    · exact (htight hold).mono (fun p q hpq => heqMono hpq)
  exact ⟨beta, hbetaTight, heqMono, hnew,
    EqvOn.of_reach ha hb (Reach.head hnew (Reach.refl b))⟩

/-! ## Maximal tight graphs -/

/-- No tight proof graph represents a strict superset of these equalities. -/
def PGraph.TightEqualityComplete
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) : Prop :=
  ∀ beta : PGraph A R, beta.Tight → rho.EqualityExtends beta →
    beta.EqualityExtends rho

/-- Every tight graph has a tight equality-maximal replacement on the same
finite coalgebra. -/
theorem PGraph.Tight.exists_tightEqualityComplete
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (htight : rho.Tight) :
    ∃ beta : PGraph A R, rho.EqualityExtends beta ∧ beta.Tight ∧
      beta.TightEqualityComplete := by
  classical
  have main : ∀ n : Nat, ∀ alpha : PGraph A R, alpha.Tight →
      alpha.eqvGap = n →
      ∃ beta : PGraph A R, alpha.EqualityExtends beta ∧ beta.Tight ∧
        beta.TightEqualityComplete := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro alpha hAlpha hn
        by_cases hmax : alpha.TightEqualityComplete
        · exact ⟨alpha, PGraph.EqualityExtends.refl alpha, hAlpha, hmax⟩
        · have hnext : ∃ beta : PGraph A R, beta.Tight ∧
              alpha.EqualityExtends beta ∧ ¬ beta.EqualityExtends alpha := by
            by_contra hnone
            apply hmax
            intro beta hBeta hab
            by_contra hba
            exact hnone ⟨beta, hBeta, hab, hba⟩
          obtain ⟨beta, hBeta, hab, hba⟩ := hnext
          have hlt : beta.eqvGap < n := by
            rw [← hn]
            exact PGraph.eqvGap_lt_of_strict_equality_extension hab hba
          obtain ⟨gamma, hbg, hGamma, hGammaMax⟩ :=
            ih beta.eqvGap hlt beta hBeta rfl
          exact ⟨gamma, hab.trans hbg, hGamma, hGammaMax⟩
  exact main rho.eqvGap rho htight rfl

/-- Every finite coalgebra has a tight equality-maximal graph. -/
theorem exists_tightEqualityComplete
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    ∃ rho : PGraph A R, rho.Tight ∧ rho.TightEqualityComplete := by
  obtain ⟨rho, _, htight, hmax⟩ :=
    PGraph.Tight.exists_tightEqualityComplete
      (rho := PGraph.empty A R) (PGraph.empty_tight A R)
  exact ⟨rho, htight, hmax⟩

/-- Every finite coalgebra of a strongly almost non-omega-overlapping
constructor system has one tight equality-maximal graph that already represents
every root contraction. Tight completion preserves the equations of the
root-only construction. -/
theorem exists_tightEqualityComplete_rootStepsRepresented_of_strong
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R) :
    ∃ rho : PGraph A R, rho.Tight ∧ rho.TightEqualityComplete ∧
      RootStepsRepresented A R rho := by
  obtain ⟨alpha, hrootOnly, hroot⟩ :=
    exists_rootOnly_rootStepsRepresented_of_strong hA hR hstrong
  obtain ⟨rho, hext, htight, hmax⟩ :=
    hrootOnly.tight.exists_tightEqualityComplete
  exact ⟨rho, htight, hmax, hroot.mono hext⟩

/-- A tight equality-maximal graph represents every tight edge leaving a graph
root. -/
theorem PGraph.TightEqualityComplete.eqvOn_of_nf_tightEdge
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hnf : rho.NF a) (hedge : TightEdge R (EqvOn A rho.par) a b) :
    EqvOn A rho.par a b := by
  by_contra hne
  obtain ⟨beta, hBeta, hext, _, hnew⟩ :=
    htight.extend_one hA hR ha hb hnf hne hedge
  exact hne (hmax beta hBeta hext hnew)

/-! ## Reversible prefixes -/

/-- A parent path with no root-contraction edge. Tightness makes every edge of
such a path reversible. -/
inductive TightNonRootReach
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) :
    Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop
  | refl (a) : TightNonRootReach rho a a
  | head {a b c} : rho.par a = some b → ¬ rootStep R a b →
      TightNonRootReach rho b c → TightNonRootReach rho a c

theorem TightNonRootReach.toReach
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a b : Term (sigma ⊕ sigma) nu}
    (h : TightNonRootReach rho a b) : Reach rho.par a b := by
  induction h with
  | refl => exact Reach.refl _
  | head hedge _ _ ih => exact Reach.head hedge ih

/-- A root-free parent path is reversible in every proof graph. The result is
strictly stronger than the tight-graph specialization below. -/
theorem TightNonRootReach.reversible_without_tightness
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a b : Term (sigma ⊕ sigma) nu}
    (h : TightNonRootReach rho a b) : ReversibleReach rho a b := by
  induction h with
  | refl => exact ReversibleReach.refl _
  | @head a b c hedge hnot _ ih =>
      have hreverse : Grey A R (EqvOn A rho.par) b a :=
        (rho.grey hedge).symm_of_not_root (fun _ _ hxy => EqvOn.symm hxy) hnot
      exact ReversibleReach.head hedge hreverse ih

/-- A tight root-free path is reversible. -/
theorem TightNonRootReach.reversible
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (_htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (h : TightNonRootReach rho a b) :
    ReversibleReach rho a b := by
  exact h.reversible_without_tightness

/-- A finite parent path is either root-free or has a first root-contraction
edge after a root-free prefix. -/
theorem Reach.tightNonRoot_or_firstRoot
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a z : Term (sigma ⊕ sigma) nu}
    (h : Reach rho.par a z) :
    TightNonRootReach rho a z ∨
      ∃ x y, TightNonRootReach rho a x ∧ rho.par x = some y ∧
        rootStep R x y := by
  induction h with
  | refl => exact Or.inl (TightNonRootReach.refl _)
  | @head a b z hedge htail ih =>
      by_cases hroot : rootStep R a b
      · exact Or.inr ⟨a, b, TightNonRootReach.refl a, hedge, hroot⟩
      · rcases ih with hfree | ⟨x, y, hprefix, hxy, hrootXY⟩
        · exact Or.inl (TightNonRootReach.head hedge hroot hfree)
        · exact Or.inr ⟨x, y, TightNonRootReach.head hedge hroot hprefix,
             hxy, hrootXY⟩

/-- A root-free path from a destructor-headed node is a path inside its
destructor fiber. Constructor congruence cannot leave a destructor source. -/
theorem TightNonRootReach.barReachOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hshape : ∃ d args, a = .app (.inr d) args)
    (h : TightNonRootReach rho a b) : BarReachOn A R a b := by
  induction h with
  | refl => exact BarReachOn.refl _
  | @head a b c hedge hnot htail ih =>
      rcases rho.grey hedge with hroot | hbar | hhat
      · exact (hnot hroot).elim
      · have hb : b ∈ A := (rho.mem_edge hedge).2
        obtain ⟨f, as, bs, ⟨d, hf⟩, haShape, hbShape, hall⟩ := hbar
        subst hf
        have hstep : BarStepOn A R a b :=
          ⟨ha, hb, ⟨.inr d, as, bs, ⟨d, rfl⟩, haShape, hbShape, hall⟩⟩
        have htailBar : BarReachOn A R b c :=
          ih hb ⟨d, bs, hbShape⟩
        exact BarReachOn.head hstep htailBar
      · obtain ⟨d, args, haShape⟩ := hshape
        subst haShape
        exact (not_conTopped_destructor args (ConTopped.of_hatEq hhat)).elim

/-- Reflexivity of the destructor congruence on a destructor-headed member of
a coalgebra. -/
theorem barRel_eqvOn_refl_of_destructor
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {a : Term (sigma ⊕ sigma) nu} (ha : a ∈ A)
    (hshape : ∃ d args, a = .app (.inr d) args) :
    barRel (EqvOn A rho.par) a a := by
  obtain ⟨d, args, rfl⟩ := hshape
  exact ⟨.inr d, args, args, ⟨d, rfl⟩, rfl, rfl,
    forall₂_self_of (fun x hx => EqvOn.refl (Coalgebra.arg hA ha hx))⟩

/-- A tight root-free path from a destructor-headed member carries one
destructor congruence over the represented equality. -/
theorem TightNonRootReach.barRel_eqvOn
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R} (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A)
    (hshape : ∃ d args, a = .app (.inr d) args)
    (h : TightNonRootReach rho a b) : barRel (EqvOn A rho.par) a b := by
  induction h with
  | refl => exact barRel_eqvOn_refl_of_destructor hA rho ha hshape
  | @head a b c hedge hnot htail ih =>
      rcases htight hedge with hroot | hbar | hhat
      · exact (hnot hroot).elim
      · have hbarStep : barRel (EqvOn A rho.par) a b := hbar
        obtain ⟨f, as, bs, ⟨d, hf⟩, haShape, hbShape, hall⟩ := hbar
        subst hf
        have hb : b ∈ A := (rho.mem_edge hedge).2
        have htailBar : barRel (EqvOn A rho.par) b c :=
          ih hb ⟨d, bs, hbShape⟩
        exact barRel_eqvOn_trans hbarStep htailBar
      · obtain ⟨d, args, haShape⟩ := hshape
        subst haShape
        exact (not_conTopped_destructor args (ConTopped.of_hatEq hhat)).elim

/-- A tight graph routes every root-redex source either through reversible
destructor edges to a graph root or to the first represented root contraction. -/
theorem PGraph.Tight.rootRoute
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hroot : rootStep R a b) :
    (∃ r, TightNonRootReach rho a r ∧ rho.NF r ∧
      barRel (EqvOn A rho.par) a r) ∨
    (∃ x y, TightNonRootReach rho a x ∧ rho.par x = some y ∧
      rootStep R x y ∧ barRel (EqvOn A rho.par) a x) := by
  have hshape := rootStep_source_destructor hR hroot
  rcases (rho.normalRoot_spec a).1.tightNonRoot_or_firstRoot with hfree |
      ⟨x, y, hprefix, hxy, hrootXY⟩
  · exact Or.inl ⟨rho.normalRoot a, hfree, (rho.normalRoot_spec a).2,
      hfree.barRel_eqvOn hA htight ha hshape⟩
  · exact Or.inr ⟨x, y, hprefix, hxy, hrootXY,
      hprefix.barRel_eqvOn hA htight ha hshape⟩

/-! ## Tight rerooting -/

/-- Reversing one non-root tight parent edge into a graph root preserves
tightness and the represented equality. -/
theorem PGraph.Tight.reroot_one
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (htight : rho.Tight)
    {a b : Term (sigma ⊕ sigma) nu} (hab : rho.par a = some b)
    (hbnf : rho.NF b) (hnot : ¬ rootStep R a b) :
    ∃ beta : PGraph A R, beta.Tight ∧ beta.NF a ∧
      (∀ x y, EqvOn A beta.par x y ↔ EqvOn A rho.par x y) ∧
      ∀ x, x ≠ a → x ≠ b → beta.par x = rho.par x := by
  have hreverse : TightEdge R (EqvOn A rho.par) b a :=
    (htight hab).symm_of_not_root (fun _ _ hxy => EqvOn.symm hxy) hnot
  obtain ⟨beta, hpar, hanf, _, heq, hoff⟩ :=
    rho.reroot_one hab hbnf (hreverse.toGrey rho)
  have hbetaTight : beta.Tight := by
    intro x y hxy
    rw [hpar] at hxy
    rcases extendPar_edge hxy with ⟨rfl, rfl⟩ | hcut
    · exact hreverse.mono (fun p q hpq => (heq p q).mpr hpq)
    · have hold : rho.par x = some y := (ParentReplacement.cut_edge hcut).2
      exact (htight hold).mono (fun p q hpq => (heq p q).mpr hpq)
  exact ⟨beta, hbetaTight, hanf, heq, hoff⟩

/-- Rerooting an entire tight root-free path preserves tightness and the
represented equality. -/
theorem PGraph.Tight.reroot_nonRootReach
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (htight : rho.Tight)
    {a r : Term (sigma ⊕ sigma) nu} (hpath : TightNonRootReach rho a r)
    (hr : rho.NF r) :
    ∃ beta : PGraph A R, beta.Tight ∧ beta.NF a ∧
      (∀ x y, EqvOn A beta.par x y ↔ EqvOn A rho.par x y) ∧
      ∀ x, ¬ Reach rho.par a x → beta.par x = rho.par x := by
  revert hr
  induction hpath with
  | refl a =>
      intro ha
      exact ⟨rho, htight, ha, fun _ _ => Iff.rfl, fun _ _ => rfl⟩
  | @head a b r hab hnot hbr ih =>
      intro hr
      obtain ⟨beta, hBetaTight, hbnf, heq, hoff⟩ := ih hr
      have hnoBack : ¬ Reach rho.par b a :=
        fun h => rho.term.no_parent_cycle hab h
      have hbetaAB : beta.par a = some b := (hoff a hnoBack).trans hab
      have hnotBeta : ¬ rootStep R a b := hnot
      obtain ⟨gamma, hGammaTight, hgnf, hgeq, hgoff⟩ :=
        hBetaTight.reroot_one hbetaAB hbnf hnotBeta
      refine ⟨gamma, hGammaTight, hgnf,
        fun x y => (hgeq x y).trans (heq x y), ?_⟩
      intro x hx
      have hxa : x ≠ a := by
        intro hxa
        subst x
        exact hx (Reach.refl a)
      have hxb : x ≠ b := by
        intro hxb
        subst x
        exact hx (Reach.head hab (Reach.refl b))
      exact (hgoff x hxa hxb).trans
        (hoff x (fun hbx => hx (Reach.head hab hbx)))

/-- A missing root equation can be added after a tight root-free route while
preserving all old equalities and tightness. -/
theorem PGraph.Tight.repair_rootStep_along_nonRootReach
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (htight : rho.Tight)
    {a r b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hpath : TightNonRootReach rho a r) (hr : rho.NF r)
    (hne : ¬ EqvOn A rho.par a b) (hroot : rootStep R a b) :
    ∃ beta : PGraph A R, beta.Tight ∧ rho.EqualityExtends beta ∧
      EqvOn A beta.par a b := by
  obtain ⟨gamma, hGammaTight, hgnf, heq, _⟩ :=
    htight.reroot_nonRootReach hpath hr
  have hneGamma : ¬ EqvOn A gamma.par a b :=
    fun h => hne ((heq a b).mp h)
  have hrootTight : TightEdge R (EqvOn A gamma.par) a b := Or.inl hroot
  obtain ⟨beta, hBetaTight, hGammaBeta, _, hnew⟩ :=
    hGammaTight.extend_one hA hR ha hb hgnf hneGamma hrootTight
  refine ⟨beta, hBetaTight, ?_, hnew⟩
  intro x y hxy
  exact hGammaBeta ((heq x y).mpr hxy)

/-- A missing root rewrite can be installed after any root-free parent path in
an arbitrary proof graph. The construction preserves every old represented
equality; no tightness premise is used. -/
theorem PGraph.repair_rootStep_along_rootFreeReach
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R)
    {a r b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hpath : TightNonRootReach rho a r) (hr : rho.NF r)
    (hne : ¬ EqvOn A rho.par a b) (hroot : rootStep R a b) :
    ∃ beta : PGraph A R, beta.par a = some b ∧
      rho.EqualityExtends beta ∧ EqvOn A beta.par a b :=
  rho.repair_along_reversible_path hA hR ha hb
    hpath.reversible_without_tightness hr hne (Or.inl hroot)

/-- In an equality-maximal proof graph, every unrepresented root rewrite is
blocked by an actual earlier root edge after a root-free prefix. -/
theorem PGraph.EqualityComplete.missing_rootStep_has_first_root_blocker
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (hmax : rho.EqualityComplete)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hroot : rootStep R a b) (hmissing : ¬ EqvOn A rho.par a b) :
    ∃ x y, TightNonRootReach rho a x ∧ rho.par x = some y ∧
      rootStep R x y := by
  rcases (rho.normalRoot_spec a).1.tightNonRoot_or_firstRoot with hfree |
      ⟨x, y, hprefix, hxy, hrootXY⟩
  · obtain ⟨beta, _, hext, hnew⟩ :=
      rho.repair_rootStep_along_rootFreeReach hA hR ha hb hfree
        (rho.normalRoot_spec a).2 hmissing hroot
    exact (hmissing (hmax beta hext hnew)).elim
  · exact ⟨x, y, hprefix, hxy, hrootXY⟩

/-- The blocker of a missing root rewrite lies in the same destructor fiber as
the missing source. This is the structural form used by batch repair. -/
theorem PGraph.EqualityComplete.missing_rootStep_has_fiber_blocker
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (hmax : rho.EqualityComplete)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hroot : rootStep R a b) (hmissing : ¬ EqvOn A rho.par a b) :
    ∃ x y, BarReachOn A R a x ∧ rho.par x = some y ∧
      rootStep R x y := by
  obtain ⟨x, y, hprefix, hxy, hrootXY⟩ :=
    hmax.missing_rootStep_has_first_root_blocker hA hR ha hb hroot hmissing
  exact ⟨x, y, hprefix.barReachOn ha (rootStep_source_destructor hR hroot),
    hxy, hrootXY⟩

/-! ## Root representation from local closure -/

/-- On a maximal tight graph, local signature closure represents every root
contraction of a strongly almost non-omega-overlapping constructor system. -/
theorem PGraph.TightEqualityComplete.rootStepsRepresented_of_sigmaClosedOn
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    (hclosed : SigmaClosedOn A (EqvOn A rho.par)) :
    RootStepsRepresented A R rho := by
  intro a b ha hb hroot
  rcases htight.rootRoute hA hR ha hroot with
      ⟨r, hpath, hr, _⟩ | ⟨x, y, hpath, hxy, hrootXY, hbar⟩
  · by_contra hmissing
    obtain ⟨beta, hBetaTight, hext, hnew⟩ :=
      htight.repair_rootStep_along_nonRootReach hA hR ha hb hpath hr hmissing hroot
    exact hmissing (hmax beta hBetaTight hext hnew)
  · have hax : EqvOn A rho.par a x :=
      EqvOn.of_reach ha (rho.mem_of_reach_right ha hpath.toReach) hpath.toReach
    have hxyEq : EqvOn A rho.par x y :=
      EqvOn.of_reach (rho.mem_edge hxy).1 (rho.mem_edge hxy).2
        (Reach.head hxy (Reach.refl y))
    have hcritical : CT (EqvOn A rho.par) b y :=
      thm37 (E := EqvOn A rho.par) hR hstrong
        (fun _ _ h => EqvOn.symm h)
        (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
        (rho.constructorCompatible_eqvOn hA hR) hroot hbar hrootXY
    have hby : EqvOn A rho.par b y :=
      hclosed.eq_of_CT hA hb (rho.mem_edge hxy).2 hcritical
    exact EqvOn.trans (EqvOn.trans hax hxyEq) (EqvOn.symm hby)

/-- A maximal tight locally closed graph is universal on its finite carrier. -/
theorem PGraph.TightEqualityComplete.universal_of_sigmaClosedOn
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {rho : PGraph A R} (hmax : rho.TightEqualityComplete) (htight : rho.Tight)
    (hclosed : SigmaClosedOn A (EqvOn A rho.par)) : rho.Universal :=
  rho.universal_of_rootStepsRepresented hclosed
    (hmax.rootStepsRepresented_of_sigmaClosedOn hA hR hstrong htight hclosed)

end OperatorKO7.Meta.UniqueNormalization
