import OperatorKO7.Meta.UniqueNormalization.Section7FiberReduction

/-!
# Section 7 same-graph closure

Local signature closure already forces context absorption on the same proof
graph. Every complete targeted graph therefore has the absorption property.
The remaining finite-coalgebra condition is root-step representation on that
same graph. Under the strong overlap hypothesis, failure of that condition has
an explicit root, fiber path, and unrepresented aligned argument.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- All members follow destructor-guided graph paths to their selected targets. -/
def TermTargetedPGraph.AllGuided
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TermTargetedPGraph A R) : Prop :=
  ∀ t, t ∈ A → GuidedReach rho.graph t (rho.target.pick t)

/-- Local signature closure of the represented equality proves context
absorption on the same graph. -/
theorem PGraph.contextAbsorbs_of_sigmaClosedOn
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    (hclosed : SigmaClosedOn A (EqvOn A rho.par)) : rho.ContextAbsorbs := by
  intro a b c _ hb hc hab hbc
  have hbcCT : CT (EqvOn A rho.par) b c := CT.sigmaClosed b c hbc
  have hbcEq : EqvOn A rho.par b c := hclosed.eq_of_CT hA hb hc hbcCT
  exact CT.base (EqvOn.trans hab hbcEq)

/-- Completeness of a targeted graph proves context absorption without a root,
overlap, or universality premise. -/
theorem TermTargetedPGraph.contextAbsorbs_of_complete
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete) :
    rho.graph.ContextAbsorbs :=
  rho.graph.contextAbsorbs_of_sigmaClosedOn hA
    (rho.sigmaClosedOn_of_complete hA hR hcomplete)

/-- On a complete targeted graph, universality is equivalent to root-step
representation together with context absorption on that graph. The absorption
conjunct is derived from completeness in both directions. -/
theorem TermTargetedPGraph.universal_iff_sameGraph_root_and_absorption
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete) :
    rho.graph.Universal ↔
      RootStepsRepresented A R rho.graph ∧ rho.graph.ContextAbsorbs := by
  constructor
  · intro huniv
    exact ⟨huniv.rootStepsRepresented,
      rho.contextAbsorbs_of_complete hA hR hcomplete⟩
  · rintro ⟨hroot, _⟩
    exact rho.graph.universal_of_rootStepsRepresented
      (rho.sigmaClosedOn_of_complete hA hR hcomplete) hroot

/-- The complete-target construction yields an equality-maximal graph, guided
paths, and context absorption simultaneously. -/
theorem exists_equalityComplete_contextAbsorbing_targeted
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) :
    ∃ rho : TermTargetedPGraph A R,
      rho.graph.EqualityComplete ∧ rho.graph.Complete ∧ rho.AllGuided ∧
        rho.graph.ContextAbsorbs := by
  obtain ⟨old, hmax, hcomplete, hall⟩ := exists_equalityComplete_targeted hA hR
  let rho : TermTargetedPGraph A R := old.toTermTargeted
  have hall' : rho.AllGuided := by
    intro t ht
    change GuidedReach old.graph t ((Section7Target.ofTarget old.target).pick t)
    rw [Section7Target.ofTarget_pick old.target ht]
    exact hall t ht
  exact ⟨rho, hmax, hcomplete, hall',
    rho.contextAbsorbs_of_complete hA hR hcomplete⟩

/-- A concrete missing root equation. -/
def RootRepresentationFailure
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (rho : PGraph A R) : Prop :=
  ∃ a b, a ∈ A ∧ b ∈ A ∧ rootStep R a b ∧ ¬ EqvOn A rho.par a b

/-- For a locally signature-closed graph, nonuniversality is exactly the
existence of a missing root equation. -/
theorem PGraph.not_universal_iff_rootRepresentationFailure_of_sigmaClosedOn
    {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    (hclosed : SigmaClosedOn A (EqvOn A rho.par)) :
    ¬ rho.Universal ↔ RootRepresentationFailure A R rho := by
  constructor
  · exact rho.exists_unrepresented_rootStep_of_not_universal hclosed
  · rintro ⟨a, b, ha, hb, hroot, hmissing⟩ huniv
    exact hmissing ((huniv a b).mpr
      (DownOn.rootComp ha hb hroot (DownOn.refl hb)))

/-- Data supplied by an unrepresented root rewrite after the strong-overlap
analysis: an outgoing selected-target rewrite and an aligned argument pair that
the graph equality does not represent. -/
def MissingRootArgumentWitness
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TermTargetedPGraph A R)
    (a b : Term (sigma ⊕ sigma) nu) : Prop :=
  ∃ d, rho.graph.par (rho.target.pick a) = some d ∧
    rootStep R (rho.target.pick a) d ∧ EqvOn A rho.graph.par a d ∧
    ¬ EqvOn A rho.graph.par b d ∧
    ∃ p q, BarReachOn A R a p ∧ BarStepOn A R p q ∧
      BarReachOn A R q (rho.target.pick a) ∧
      ∃ f preP preQ x y postP postQ,
        p = .app (.inr f) (preP ++ x :: postP) ∧
        q = .app (.inr f) (preQ ++ y :: postQ) ∧
        preP.length = preQ.length ∧ DownOn A R x y ∧
        ¬ EqvOn A rho.graph.par x y

/-- The complete strong-system failure object includes both the missing root
rewrite and the aligned argument obstruction forced by it. -/
def RootArgumentFailure
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (rho : TermTargetedPGraph A R) : Prop :=
  ∃ a b, a ∈ A ∧ b ∈ A ∧ rootStep R a b ∧
    ¬ EqvOn A rho.graph.par a b ∧ MissingRootArgumentWitness rho a b

/-- On an equality-complete targeted graph for a strong constructor system,
nonuniversality is equivalent to the full root-and-argument failure object. -/
theorem TermTargetedPGraph.not_universal_iff_rootArgumentFailure
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete) :
    ¬ rho.graph.Universal ↔ RootArgumentFailure A R rho := by
  constructor
  · intro hnot
    have hclosed := rho.sigmaClosedOn_of_complete hA hR hmax.complete
    obtain ⟨a, b, ha, hb, hroot, hmissing⟩ :=
      (rho.graph.not_universal_iff_rootRepresentationFailure_of_sigmaClosedOn
        hclosed).mp hnot
    have hwitness := rho.missing_root_has_unrepresented_argument
      hA hR hstrong hmax ha hb hroot hmissing
    exact ⟨a, b, ha, hb, hroot, hmissing, hwitness⟩
  · rintro ⟨a, b, ha, hb, hroot, hmissing, _⟩ huniv
    exact hmissing ((huniv a b).mpr
      (DownOn.rootComp ha hb hroot (DownOn.refl hb)))

/-- Root-step representation on an equality-complete targeted graph is exactly
the absence of its strong-system failure object. -/
theorem TermTargetedPGraph.rootStepsRepresented_iff_no_rootArgumentFailure
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete) :
    RootStepsRepresented A R rho.graph ↔ ¬ RootArgumentFailure A R rho := by
  constructor
  · intro hroot hfailure
    have huniv := rho.graph.universal_of_rootStepsRepresented
      (rho.sigmaClosedOn_of_complete hA hR hmax.complete) hroot
    exact ((rho.not_universal_iff_rootArgumentFailure hA hR hstrong hmax).mpr
      hfailure) huniv
  · intro hnone
    by_contra hroot
    have hnotUniversal : ¬ rho.graph.Universal := fun huniv =>
      hroot huniv.rootStepsRepresented
    exact hnone ((rho.not_universal_iff_rootArgumentFailure hA hR hstrong hmax).mp
      hnotUniversal)

/-- Every finite strong constructor coalgebra has one same-graph construction
whose positive case is universal and whose negative case carries the complete
root-and-argument obstruction. -/
theorem exists_sameGraph_section7_classification
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R) :
    ∃ rho : TermTargetedPGraph A R,
      rho.graph.EqualityComplete ∧ rho.graph.Complete ∧ rho.AllGuided ∧
      rho.graph.ContextAbsorbs ∧
      ((RootStepsRepresented A R rho.graph ∧ rho.graph.Universal) ∨
        (¬ RootStepsRepresented A R rho.graph ∧ ¬ rho.graph.Universal ∧
          RootArgumentFailure A R rho)) := by
  obtain ⟨rho, hmax, hcomplete, hall, habsorb⟩ :=
    exists_equalityComplete_contextAbsorbing_targeted hA hR
  refine ⟨rho, hmax, hcomplete, hall, habsorb, ?_⟩
  by_cases hroot : RootStepsRepresented A R rho.graph
  · exact Or.inl ⟨hroot, rho.graph.universal_of_rootStepsRepresented
      (rho.sigmaClosedOn_of_complete hA hR hcomplete) hroot⟩
  · have hnotUniversal : ¬ rho.graph.Universal := fun huniv =>
      hroot huniv.rootStepsRepresented
    exact Or.inr ⟨hroot, hnotUniversal,
      (rho.not_universal_iff_rootArgumentFailure hA hR hstrong hmax).mp
        hnotUniversal⟩

/-- The global transitivity criterion needs only complete targeted graphs that
represent root steps; context absorption follows internally on each carrier. -/
theorem down_transitive_of_finite_complete_targeted_root_models
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hmodels : ∀ A, Coalgebra A →
      ∃ rho : TermTargetedPGraph A R,
        rho.graph.Complete ∧ RootStepsRepresented A R rho.graph) :
    ∀ a b c, Down R a b → Down R b c → Down R a c := by
  apply down_transitive_of_finite_context_models
  intro A hA
  obtain ⟨rho, hcomplete, hroot⟩ := hmodels A hA
  exact ⟨rho.graph, hroot, rho.contextAbsorbs_of_complete hA hR hcomplete⟩

theorem conv_iff_down_of_finite_complete_targeted_root_models
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hmodels : ∀ A, Coalgebra A →
      ∃ rho : TermTargetedPGraph A R,
        rho.graph.Complete ∧ RootStepsRepresented A R rho.graph)
    (a b : Term (sigma ⊕ sigma) nu) : conv R a b ↔ Down R a b :=
  conv_eq_down (down_transitive_of_finite_complete_targeted_root_models hR hmodels) a b

theorem constructorCompatible_conv_of_finite_complete_targeted_root_models
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hmodels : ∀ A, Coalgebra A →
      ∃ rho : TermTargetedPGraph A R,
        rho.graph.Complete ∧ RootStepsRepresented A R rho.graph) :
    ConstructorCompatible (conv R) := by
  apply constructorCompatible_conv_of_finite_context_models hR
  intro A hA
  obtain ⟨rho, hcomplete, hroot⟩ := hmodels A hA
  exact ⟨rho.graph, hroot, rho.contextAbsorbs_of_complete hA hR hcomplete⟩

end OperatorKO7.Meta.UniqueNormalization
