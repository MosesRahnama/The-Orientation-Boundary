import OperatorKO7.Meta.UniqueNormalization.Section7Targeting

/-!
# Section 7 completion bridge

Campaign: `Distinction_Boundary/Roadmaps/klop/ROADMAP.md`, Section 7 of Kahrs and
Smith, FSCD 2016.

This module isolates the exact load-bearing content of Lemma 62.  The source works
with relations between nodes of one strongly finite coalgebra, so Sigma-closure
is relativized to endpoint membership in `A`.  The repository-wide `SigmaClosed`
predicate is global over all finite terms and is therefore strictly stronger for
a finite coalgebra; using it directly here would silently change the source
carrier.

The first theorem proves Lemma 62 from the property the published proof invokes:
every node has a graph path to the selected target of its destructor fiber.  The
next step of the campaign is to derive that path property from completeness and
targetedness, rather than assume it.

Trust: kernel checked.  No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! `SigmaClosedOn` (the typed reading of source Definition 24 on `E ⊆ A × A`)
and `GuidedReach.toReach` are declared in `Lemma52` and imported here. -/

/-- A destructor-tilde edge of the represented graph equivalence is one step in
the destructor fiber. -/
theorem barStepOn_of_barRel_eqvOn {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R}
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (h : barRel (EqvOn A rho.par) a b) : BarStepOn A R a b := by
  refine ⟨ha, hb, ?_⟩
  exact tildeOn_mono (fun _ _ hxy => rho.sub hxy) h

/-- **Lemma 62, load-bearing form.**  If a complete targeted proof graph really
routes every coalgebra node to its chosen target, then its represented
equivalence is Sigma-closed on the coalgebra.

The constructor-root case is Lemma 56.  In the destructor-root case, a one-step
destructor tilde puts the two endpoints in the same destructor fiber, so the
target function chooses the same node.  The two parent paths then meet at that
target. -/
theorem TermTargetedPGraph.sigmaClosedOn_of_all_guided
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete)
    (hall : ∀ t : Term (sigma ⊕ sigma) nu, t ∈ A →
      GuidedReach rho.graph t (rho.target.pick t)) :
    SigmaClosedOn A (EqvOn A rho.graph.par) := by
  intro t u ht hu htilde
  rcases htilde with ⟨f, as, bs, -, rfl, rfl, hab⟩
  cases f with
  | inl c =>
      apply rho.graph.constructorClosed_of_complete hA hR hcomplete ht hu
      exact Or.inr ⟨.inl c, as, bs, ⟨c, rfl⟩, rfl, rfl, hab⟩
  | inr d =>
      have hbar : barRel (EqvOn A rho.graph.par)
          (.app (.inr d) as) (.app (.inr d) bs) :=
        ⟨.inr d, as, bs, ⟨d, rfl⟩, rfl, rfl, hab⟩
      have hstep : BarStepOn A R (.app (.inr d) as) (.app (.inr d) bs) :=
        barStepOn_of_barRel_eqvOn ht hu hbar
      have hsame :
          rho.target.pick (.app (.inr d) as) = rho.target.pick (.app (.inr d) bs) :=
        rho.target.respectsFiber ht hu (BarReachOn.single hstep)
      have hleft := (hall (.app (.inr d) as) ht).toReach
      have hright := (hall (.app (.inr d) bs) hu).toReach
      refine ⟨ht, hu, rho.target.pick (.app (.inr d) as), hleft, ?_⟩
      rw [hsame]
      exact hright

/-- **Lemma 62, unconditional source statement on the finite coalgebra.**  A
complete targeted proof graph represents a Sigma-closed relation on its
coalgebra.

This proof does not use the published shortcut that completeness turns every
`guided_or_nf` disjunction into a target path.  For a destructor-root tilde the
two endpoints themselves form one admissible grey edge.  If either endpoint is
a graph normal form, completeness and Corollary 53 force the two endpoints into
the same represented class.  Otherwise both targeted paths exist and meet at
the common fiber target.  The constructor-root case remains Lemma 56. -/
theorem TermTargetedPGraph.sigmaClosedOn_of_complete
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete) :
    SigmaClosedOn A (EqvOn A rho.graph.par) := by
  intro t u ht hu htilde
  rcases htilde with ⟨f, as, bs, -, rfl, rfl, hab⟩
  cases f with
  | inl c =>
      apply rho.graph.constructorClosed_of_complete hA hR hcomplete ht hu
      exact Or.inr ⟨.inl c, as, bs, ⟨c, rfl⟩, rfl, rfl, hab⟩
  | inr d =>
      have hbar : barRel (EqvOn A rho.graph.par)
          (.app (.inr d) as) (.app (.inr d) bs) :=
        ⟨.inr d, as, bs, ⟨d, rfl⟩, rfl, rfl, hab⟩
      have hstep : BarStepOn A R (.app (.inr d) as) (.app (.inr d) bs) :=
        barStepOn_of_barRel_eqvOn ht hu hbar
      by_cases heq : EqvOn A rho.graph.par (.app (.inr d) as) (.app (.inr d) bs)
      · exact heq
      · rcases rho.guided_or_nf ht with hleft | hleftNF
        · rcases rho.guided_or_nf hu with hright | hrightNF
          · have hsame :
                rho.target.pick (.app (.inr d) as) =
                  rho.target.pick (.app (.inr d) bs) :=
              rho.target.respectsFiber ht hu (BarReachOn.single hstep)
            have hleftReach := hleft.toReach
            have hrightReach := hright.toReach
            refine ⟨ht, hu, rho.target.pick (.app (.inr d) as), hleftReach, ?_⟩
            rw [hsame]
            exact hrightReach
          · have hrevStep :
                BarStepOn A R (.app (.inr d) bs) (.app (.inr d) as) :=
              BarStepOn.symm hstep
            have hgrey : Grey A R (EqvOn A rho.graph.par)
                (.app (.inr d) bs) (.app (.inr d) as) :=
              Or.inr (Or.inl hrevStep.2.2)
            have hneRev :
                ¬ EqvOn A rho.graph.par (.app (.inr d) bs) (.app (.inr d) as) :=
              fun h => heq (EqvOn.symm h)
            obtain ⟨beta, hExt, hedge⟩ :=
              rho.graph.extend_one hA hR hu ht hrightNF hneRev hgrey
            have hBack : beta.Extends rho.graph := hcomplete beta hExt
            have hOld : rho.graph.par (.app (.inr d) bs) = some (.app (.inr d) as) :=
              hBack hedge
            rw [hrightNF] at hOld
            contradiction
        · have hgrey : Grey A R (EqvOn A rho.graph.par)
              (.app (.inr d) as) (.app (.inr d) bs) :=
            Or.inr (Or.inl hstep.2.2)
          obtain ⟨beta, hExt, hedge⟩ :=
            rho.graph.extend_one hA hR ht hu hleftNF heq hgrey
          have hBack : beta.Extends rho.graph := hcomplete beta hExt
          have hOld : rho.graph.par (.app (.inr d) as) = some (.app (.inr d) bs) :=
            hBack hedge
          rw [hleftNF] at hOld
          contradiction

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.SigmaClosedOn
#check @OperatorKO7.Meta.UniqueNormalization.GuidedReach.toReach
#check @OperatorKO7.Meta.UniqueNormalization.barStepOn_of_barRel_eqvOn
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.sigmaClosedOn_of_all_guided
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.sigmaClosedOn_of_complete

#print axioms OperatorKO7.Meta.UniqueNormalization.SigmaClosedOn
#print axioms OperatorKO7.Meta.UniqueNormalization.GuidedReach.toReach
#print axioms OperatorKO7.Meta.UniqueNormalization.barStepOn_of_barRel_eqvOn
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.sigmaClosedOn_of_all_guided
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.sigmaClosedOn_of_complete
