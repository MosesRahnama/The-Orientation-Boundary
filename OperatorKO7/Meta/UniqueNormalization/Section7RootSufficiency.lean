import OperatorKO7.Meta.UniqueNormalization.Section7StrongRootTargets

/-!
# Proof-graph universality and root-step representation

Campaign: `Distinction_Boundary/Roadmaps/klop/ROADMAP.md`, repaired Section 7.

For every proof graph, universality is equivalent to root-step representation
and local signature closure. A complete graph that represents destructor-fiber
edges already has the second property; no target selection is required.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- Root-step representation on one finite coalgebra. -/
def RootStepsRepresented
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (rho : PGraph A R) : Prop :=
  ∀ {a b : Term (sigma ⊕ sigma) nu}, a ∈ A → b ∈ A → rootStep R a b →
    EqvOn A rho.par a b

/-- Root-step representation and local signature closure suffice for any graph. -/
theorem PGraph.universal_of_rootStepsRepresented
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hcl : SigmaClosedOn A (EqvOn A rho.par))
    (hroot : RootStepsRepresented A R rho) : rho.Universal := by
  rw [rho.universal_iff_down_subset]
  intro a b hab
  refine DownOn.induction (P := fun p q => EqvOn A rho.par p q) ?_ hab
  intro p q hpq
  obtain ⟨hp, hq, hbody⟩ := hpq
  rcases hbody with heq | hinv | ⟨c, hc, hpc, hcb⟩ |
      ⟨d, as, cs, hpShape, hall, hmid, hmb⟩ | hhat | hbar
  · subst heq
    exact EqvOn.refl hp
  · exact EqvOn.symm hinv.2
  · exact EqvOn.trans (hroot hp hc hpc) hcb.2
  · subst hpShape
    have hallEq : List.Forall₂ (EqvOn A rho.par) as cs :=
      forall₂_mono (fun _ _ hx => hx.2) hall
    have hbarEq : barRel (EqvOn A rho.par)
        (.app (.inr d) as) (.app (.inr d) cs) :=
      ⟨.inr d, as, cs, ⟨d, rfl⟩, rfl, rfl, hallEq⟩
    have hEqMid : EqvOn A rho.par (.app (.inr d) as) (.app (.inr d) cs) :=
      hcl _ _ hp hmid (tildeAll_of_barRel hbarEq)
    exact EqvOn.trans hEqMid hmb.2
  · have hhatEq : hatRel (EqvOn A rho.par) p q :=
      tildeOn_mono (fun _ _ hx => hx.2) hhat
    exact hcl p q hp hq (tildeAll_of_hatRel hhatEq)
  · have hbarEq : barRel (EqvOn A rho.par) p q :=
      tildeOn_mono (fun _ _ hx => hx.2) hbar
    exact hcl p q hp hq (tildeAll_of_barRel hbarEq)

theorem PGraph.Universal.rootStepsRepresented
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (h : rho.Universal) : RootStepsRepresented A R rho := by
  intro a b ha hb hab
  exact (h a b).mpr (DownOn.rootComp ha hb hab (DownOn.refl hb))

theorem PGraph.Universal.sigmaClosedOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (h : rho.Universal) : SigmaClosedOn A (EqvOn A rho.par) := by
  intro a b ha hb htilde
  rcases htilde with ⟨f, as, bs, _, rfl, rfl, hall⟩
  exact (h _ _).mpr (DownOn.tildeCl ha hb
    (forall₂_mono (fun _ _ he => rho.sub he) hall))

/-- No coalgebra, constructor, overlap, targeting, or completeness premise. -/
theorem PGraph.universal_iff_rootStepsRepresented_and_sigmaClosedOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) :
    rho.Universal ↔ RootStepsRepresented A R rho ∧ SigmaClosedOn A (EqvOn A rho.par) := by
  exact ⟨fun h => ⟨h.rootStepsRepresented, h.sigmaClosedOn⟩,
    fun h => rho.universal_of_rootStepsRepresented h.2 h.1⟩

theorem PGraph.Universal.barClosed
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (h : rho.Universal) : rho.BarClosed := by
  intro a b hbar
  obtain ⟨ha, hb, f, as, bs, ⟨d, hd⟩, haEq, hbEq, hall⟩ := hbar
  subst hd
  subst haEq
  subst hbEq
  exact (h _ _).mpr (DownOn.barCl ha hb hall)

theorem PGraph.Universal.equalityComplete
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (h : rho.Universal) : rho.EqualityComplete := by
  intro beta _ a b hab
  exact (h a b).mpr (beta.sub hab)

/-- Destructor closure follows from represented fiber edges; constructor closure
follows from completeness and the constructor rule laws. -/
theorem PGraph.sigmaClosedOn_of_barClosed_complete
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) (hbar : rho.BarClosed) (hcomplete : rho.Complete) :
    SigmaClosedOn A (EqvOn A rho.par) := by
  intro a b ha hb htilde
  rcases hatRel_or_barRel_of_tildeAll htilde with hhat | hdestructor
  · exact rho.constructorClosed_of_complete hA hR hcomplete ha hb (Or.inr hhat)
  · exact hbar ⟨ha, hb, tildeOn_mono (fun _ _ h => rho.sub h) hdestructor⟩

/-- For a complete constructor proof graph, the two remaining conditions are
representation of root rewrites and of destructor-fiber edges. -/
theorem PGraph.universal_iff_rootStepsRepresented_and_barClosed
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) (hcomplete : rho.Complete) :
    rho.Universal ↔ RootStepsRepresented A R rho ∧ rho.BarClosed := by
  constructor
  · intro h
    exact ⟨h.rootStepsRepresented, h.barClosed⟩
  · intro h
    exact rho.universal_of_rootStepsRepresented
      (rho.sigmaClosedOn_of_barClosed_complete hA hR h.2 hcomplete) h.1

theorem PGraph.universal_iff_rootStepsRepresented_of_barClosed_complete
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) (hbar : rho.BarClosed) (hcomplete : rho.Complete) :
    rho.Universal ↔ RootStepsRepresented A R rho := by
  exact ⟨fun h => h.rootStepsRepresented,
    rho.universal_of_rootStepsRepresented
      (rho.sigmaClosedOn_of_barClosed_complete hA hR hbar hcomplete)⟩

theorem PGraph.EqualityComplete.universal_iff_rootStepsRepresented
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (hcomplete : rho.EqualityComplete) (hbar : rho.BarClosed) :
    rho.Universal ↔ RootStepsRepresented A R rho :=
  rho.universal_iff_rootStepsRepresented_of_barClosed_complete hA hR hbar hcomplete.complete

/-- A signature-closed nonuniversal graph has an actual unrepresented root step. -/
theorem PGraph.exists_unrepresented_rootStep_of_not_universal
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hcl : SigmaClosedOn A (EqvOn A rho.par))
    (hn : ¬ rho.Universal) :
    ∃ a b, a ∈ A ∧ b ∈ A ∧ rootStep R a b ∧ ¬ EqvOn A rho.par a b := by
  classical
  by_contra hnone
  apply hn (rho.universal_of_rootStepsRepresented hcl ?_)
  intro a b ha hb hab
  by_contra hne
  exact hnone ⟨a, b, ha, hb, hab, hne⟩

theorem RootStepsRepresented.iff_normalRoot
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) :
    RootStepsRepresented A R rho ↔
      ∀ a b, a ∈ A → b ∈ A → rootStep R a b → rho.normalRoot a = rho.normalRoot b := by
  constructor
  · intro h a b ha hb hr
    exact (rho.eqvOn_iff_normalRoot_eq ha hb).mp (h ha hb hr)
  · intro h a b ha hb hr
    exact (rho.eqvOn_iff_normalRoot_eq ha hb).mpr (h a b ha hb hr)

/-- Every parent edge is an actual root contraction. -/
def PGraph.RootOnly
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) : Prop :=
  ∀ ⦃a b⦄, rho.par a = some b → rootStep R a b

theorem PGraph.empty_rootOnly
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    (PGraph.empty A R).RootOnly := by
  intro a b h
  cases h

/-- Add a missing contraction at a graph normal form without adding non-root
parent edges. Every old equality remains represented. -/
theorem PGraph.RootOnly.extend_root
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (honly : rho.RootOnly)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hnf : rho.NF a) (hne : ¬ EqvOn A rho.par a b) (hroot : rootStep R a b) :
    ∃ beta : PGraph A R, beta.RootOnly ∧ rho.EqualityExtends beta ∧
      EqvOn A beta.par a b := by
  obtain ⟨beta, hpar, hext, hedge⟩ :=
    rho.extend_one_exact hA hR ha hb hnf hne (Or.inl hroot)
  refine ⟨beta, ?_, (fun _ _ h => EqvOn.mono hext h),
    EqvOn.of_reach ha hb (Reach.head hedge (Reach.refl b))⟩
  intro x y hxy
  rw [hpar] at hxy
  rcases extendPar_edge hxy with ⟨rfl, rfl⟩ | h
  · exact hroot
  · exact honly h

theorem RootStepsRepresented.mono
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {alpha beta : PGraph A R} (h : RootStepsRepresented A R alpha)
    (hext : alpha.EqualityExtends beta) : RootStepsRepresented A R beta := by
  intro a b ha hb hr
  exact hext (h ha hb hr)

/-- Finite root-deterministic constructor systems have a root-only graph that
represents every contraction, including edges on directed cycles. -/
theorem exists_rootOnly_rootStepsRepresented
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hdet : ∀ ⦃a b c : Term (sigma ⊕ sigma) nu⦄,
      rootStep R a b → rootStep R a c → b = c) :
    ∃ rho : PGraph A R, rho.RootOnly ∧ RootStepsRepresented A R rho := by
  classical
  have hex : ∃ n : Nat, ∃ rho : PGraph A R, rho.RootOnly ∧ rho.eqvGap = n :=
    ⟨_, PGraph.empty A R, PGraph.empty_rootOnly A R, rfl⟩
  obtain ⟨rho, honly, hgap⟩ := Nat.find_spec hex
  refine ⟨rho, honly, ?_⟩
  intro a b ha hb hr
  cases hp : rho.par a with
  | some c =>
      have hcb : c = b := hdet (honly hp) hr
      subst c
      exact EqvOn.of_reach ha hb (Reach.head hp (Reach.refl b))
  | none =>
      by_contra hne
      obtain ⟨beta, hbOnly, hext, hnew⟩ := honly.extend_root hA hR ha hb hp hne hr
      have hnot : ¬ beta.EqualityExtends rho := fun h => hne (h hnew)
      have hdrop := PGraph.eqvGap_lt_of_strict_equality_extension hext hnot
      have hmin : Nat.find hex ≤ beta.eqvGap := Nat.find_min' hex ⟨beta, hbOnly, rfl⟩
      rw [hgap] at hdrop
      omega

/-- Equality completion retains every root equation of the constructed graph. -/
theorem exists_equalityComplete_rootStepsRepresented
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hdet : ∀ ⦃a b c : Term (sigma ⊕ sigma) nu⦄,
      rootStep R a b → rootStep R a c → b = c) :
    ∃ rho : PGraph A R, rho.EqualityComplete ∧ RootStepsRepresented A R rho := by
  obtain ⟨alpha, _, hr⟩ := exists_rootOnly_rootStepsRepresented hA hR hdet
  obtain ⟨rho, hext, hmax⟩ := alpha.exists_equalityComplete
  exact ⟨rho, hmax, hr.mono hext⟩

theorem exists_rootOnly_rootStepsRepresented_of_strong
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R) :
    ∃ rho : PGraph A R, rho.RootOnly ∧ RootStepsRepresented A R rho :=
  exists_rootOnly_rootStepsRepresented hA hR (root_deterministic_of_strong hstrong)

theorem exists_equalityComplete_rootStepsRepresented_of_strong
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R) :
    ∃ rho : PGraph A R, rho.EqualityComplete ∧ RootStepsRepresented A R rho :=
  exists_equalityComplete_rootStepsRepresented hA hR
    (root_deterministic_of_strong hstrong)

/-- The earlier targeted interface follows from the generic graph theorem. -/
theorem TermTargetedPGraph.universal_of_rootStepsRepresented
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete)
    (hroot : RootStepsRepresented A R rho.graph) : rho.Universal := by
  intro a b hab
  exact (rho.graph.universal_of_rootStepsRepresented
    (rho.sigmaClosedOn_of_complete hA hR hcomplete) hroot a b).mpr hab

/-! ## Context completion on the same finite carrier -/

/-- Context transitivity concerns only triples inside A. -/
def PGraph.ContextTransitive
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) : Prop :=
  ∀ a b c, a ∈ A → b ∈ A → c ∈ A →
    CT (EqvOn A rho.par) a b → CT (EqvOn A rho.par) b c →
      CT (EqvOn A rho.par) a c

/-- Compose one represented equality with one application pair inside A. -/
def PGraph.ContextAbsorbs
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) : Prop :=
  ∀ a b c, a ∈ A → b ∈ A → c ∈ A →
    EqvOn A rho.par a b → tildeAll (CT (EqvOn A rho.par)) b c →
      CT (EqvOn A rho.par) a c

theorem PGraph.contextTransitive_iff_contextAbsorbs
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) :
    rho.ContextTransitive ↔ rho.ContextAbsorbs :=
  CT.transitiveOn_iff_base_context (fun a => a ∈ A)
    (fun _ _ h _ ha => hA.arg h ha)
    (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)

/-- A context proof between carrier members stays in the actual relativized
Down relation. Its argument memberships follow from subterm closure. -/
theorem PGraph.context_subset_downOn
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hab : CT (EqvOn A rho.par) a b) : DownOn A R a b := by
  let S : CRel sigma nu := fun p q => p ∈ A → q ∈ A → DownOn A R p q
  have hsub : ∀ p q, EqvOn A rho.par p q → S p q := by
    intro p q hpq _ _
    exact rho.sub hpq
  have hclosed : SigmaClosed S := by
    rintro p q ⟨f, xs, ys, _, rfl, rfl, hargs⟩ hp hq
    apply DownOn.tildeCl hp hq
    exact forall₂_compose_of_mem hargs
      (forall₂_self (r := fun (p q : Term (sigma ⊕ sigma) nu) => p = q) (fun _ => rfl) ys)
      (fun x hx y hy z _ hxy hyz => by
        subst z
        exact hxy (hA.arg hp hx) (hA.arg hq hy))
  exact (CT.least hsub hclosed hab) ha hb

/-- Root representation and local context transitivity identify the completed
relation with DownOn; no new parent function is assumed or constructed. -/
theorem PGraph.context_iff_downOn_of_rootStepsRepresented
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    (hroot : RootStepsRepresented A R rho) (htrans : rho.ContextTransitive)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A) :
    CT (EqvOn A rho.par) a b ↔ DownOn A R a b := by
  constructor
  · exact rho.context_subset_downOn hA ha hb
  · intro hab
    refine DownOn.induction (P := fun p q => CT (EqvOn A rho.par) p q) ?_ hab
    intro p q hpq
    obtain ⟨hp, hq, hbody⟩ := hpq
    rcases hbody with heq | hinv | ⟨c, hc, hpc, hcb⟩ |
        ⟨d, xs, ys, hpShape, hargs, hmid, hmb⟩ | hhat | hbar
    · subst q
      exact CT.base (EqvOn.refl hp)
    · exact CT.symm (fun _ _ h => EqvOn.symm h) hinv.2
    · exact htrans p c q hp hc hq (CT.base (hroot hp hc hpc)) hcb.2
    · subst p
      exact htrans _ _ _ hp hmid hq
        (CT.app (forall₂_mono (fun _ _ h => h.2) hargs)) hmb.2
    · exact CT.sigmaClosed p q (tildeAll_of_hatRel
        (tildeOn_mono (fun _ _ h => h.2) hhat))
    · exact CT.sigmaClosed p q (tildeAll_of_barRel
        (tildeOn_mono (fun _ _ h => h.2) hbar))

/-- The remaining absorption property suffices directly for finite-carrier
transitivity, without a congruence-forest representation theorem. -/
theorem PGraph.downOn_transitive_of_contextAbsorbs
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    (hroot : RootStepsRepresented A R rho) (habsorb : rho.ContextAbsorbs) :
    ∀ a b c, DownOn A R a b → DownOn A R b c → DownOn A R a c := by
  have htrans := (rho.contextTransitive_iff_contextAbsorbs hA).mpr habsorb
  intro a b c hab hbc
  have hma := hab.mem
  have hmc := hbc.mem
  have hleft := (rho.context_iff_downOn_of_rootStepsRepresented hA hroot htrans
    hma.1 hma.2).mpr hab
  have hright := (rho.context_iff_downOn_of_rootStepsRepresented hA hroot htrans
    hmc.1 hmc.2).mpr hbc
  exact rho.context_subset_downOn hA hma.1 hmc.2
    (htrans a b c hma.1 hma.2 hmc.2 hleft hright)

/-- Universal graphs satisfy the local absorption property. -/
theorem PGraph.Universal.contextAbsorbs
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R}
    (h : rho.Universal) : rho.ContextAbsorbs := by
  intro a b c _ hb hc hab hbc
  have hdown := rho.context_subset_downOn hA hb hc (CT.sigmaClosed b c hbc)
  exact CT.base (EqvOn.trans hab ((h b c).mpr hdown))


/-! ## From finite context models to the global invariant -/

/-- Finite context models capture every pair of composable global derivations. -/
theorem down_transitive_of_finite_context_models
    {R : TRS (sigma ⊕ sigma) nu}
    (hmodels : ∀ A, Coalgebra A →
      ∃ rho : PGraph A R, RootStepsRepresented A R rho ∧ rho.ContextAbsorbs) :
    ∀ a b c, Down R a b → Down R b c → Down R a c := by
  apply Down.trans_of_finite_coalgebras
  intro A hA
  obtain ⟨rho, hroot, habsorb⟩ := hmodels A hA
  exact rho.downOn_transitive_of_contextAbsorbs hA hroot habsorb

theorem conv_iff_down_of_finite_context_models
    {R : TRS (sigma ⊕ sigma) nu}
    (hmodels : ∀ A, Coalgebra A →
      ∃ rho : PGraph A R, RootStepsRepresented A R rho ∧ rho.ContextAbsorbs)
    (a b : Term (sigma ⊕ sigma) nu) : conv R a b ↔ Down R a b :=
  conv_eq_down (down_transitive_of_finite_context_models hmodels) a b

/-- The finite model criterion proves constructor compatibility of conversion
for every constructor system, not only constructor translations. -/
theorem constructorCompatible_conv_of_finite_context_models
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hmodels : ∀ A, Coalgebra A →
      ∃ rho : PGraph A R, RootStepsRepresented A R rho ∧ rho.ContextAbsorbs) :
    ConstructorCompatible (conv R) := by
  intro a b hca hcb hab
  have hdown := (conv_iff_down_of_finite_context_models hmodels a b).mp hab
  rcases Down.constructorCompatible hR a b hca hcb hdown with
      hvar | ⟨f, xs, ys, hax, hby, hargs⟩
  · exact Or.inl hvar
  · exact Or.inr ⟨f, xs, ys, hax, hby,
      forall₂_mono (fun _ _ h => Down.to_conv h) hargs⟩


end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.RootStepsRepresented
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.universal_of_rootStepsRepresented

#print axioms OperatorKO7.Meta.UniqueNormalization.RootStepsRepresented
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.universal_of_rootStepsRepresented
