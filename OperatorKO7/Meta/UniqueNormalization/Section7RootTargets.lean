import OperatorKO7.Meta.UniqueNormalization.Section7Completion

/-!
# Section 7 target-redex closure

Campaign: `Distinction_Boundary/Roadmaps/klop/ROADMAP.md`, repair of the proof
spine around Kahrs-Smith Lemma 64.

The published Lemma 64 uses the sentence that, once `targ(E_t)` is a root redex,
its contractum is in the proof-graph equivalence class of that target.  This
module proves that sentence on the live finite-coalgebra carrier.

The key point is Definition 59.  If a selected target has an outgoing graph edge,
that edge must leave its destructor fiber.  Hence it cannot be a destructor-tilde
edge.  A root redex of a Constructor TRS is destructor-topped, so it cannot carry
a constructor-tilde edge either.  The only remaining grey-edge case is a root
rewrite.  Root determinism identifies that parent with any chosen root contractum.
If the target has no graph parent, completeness plus Corollary 53 adds the root
edge unless target and contractum are already graph-equivalent.

Trust: kernel checked.  No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- An existing proof-graph parent of a selected target redex is necessarily a
root rewrite.  Destructor-tilde is excluded by the target-exits-fiber condition;
constructor-tilde is excluded because a root redex in a Constructor TRS has a
destructor-headed source. -/
theorem TermTargetedPGraph.target_parent_is_rootStep
    {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TermTargetedPGraph A R)
    {t q v : Term (sigma ⊕ sigma) nu}
    (ht : t ∈ A)
    (hpar : rho.graph.par (rho.target.pick t) = some q)
    (hroot : rootStep R (rho.target.pick t) v) :
    rootStep R (rho.target.pick t) q := by
  have hpA : rho.target.pick t ∈ A := rho.target.pick_mem ht
  have hqA : q ∈ A := (rho.graph.mem_edge hpar).2
  rcases rho.graph.grey hpar with hrootParent | hbar | hhat
  · exact hrootParent
  · have hstep : BarStepOn A R (rho.target.pick t) q := ⟨hpA, hqA, hbar⟩
    have hfiber : BarReachOn A R t q :=
      BarReachOn.trans (rho.target.inFiber ht) (BarReachOn.single hstep)
    exact False.elim ((rho.target_edge_exits_fiber ht hpar) hfiber)
  · have hcon : ConTopped (rho.target.pick t) := ConTopped.of_hatEq hhat
    obtain ⟨d, args, hp⟩ := rootStep_source_destructor hR hroot
    rw [hp] at hcon
    exact False.elim ((not_conTopped_destructor args) hcon)

/-- The selected target of a destructor fiber is graph-equivalent to every one
of its root contracta, provided the root relation is deterministic and the
targeted proof graph is complete.  This is the exact target-redex equality used
inside the source proof of Lemma 64. -/
theorem TermTargetedPGraph.target_rootStep_eqvOn_of_complete
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hdet : Deterministic R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete)
    {t v : Term (sigma ⊕ sigma) nu}
    (ht : t ∈ A) (hv : v ∈ A)
    (hroot : rootStep R (rho.target.pick t) v) :
    EqvOn A rho.graph.par (rho.target.pick t) v := by
  have hpA : rho.target.pick t ∈ A := rho.target.pick_mem ht
  cases hpar : rho.graph.par (rho.target.pick t) with
  | none =>
      by_cases heq : EqvOn A rho.graph.par (rho.target.pick t) v
      · exact heq
      · have hgrey : Grey A R (EqvOn A rho.graph.par) (rho.target.pick t) v :=
          Or.inl hroot
        obtain ⟨beta, hExt, hedge⟩ :=
          rho.graph.extend_one hA hR hpA hv hpar heq hgrey
        have hBack : beta.Extends rho.graph := hcomplete beta hExt
        have hOld : rho.graph.par (rho.target.pick t) = some v := hBack hedge
        rw [hpar] at hOld
        contradiction
  | some q =>
      have hparentRoot : rootStep R (rho.target.pick t) q :=
        rho.target_parent_is_rootStep hR ht hpar hroot
      have hqv : q = v := hdet _ _ _ hparentRoot hroot
      have hreach : Reach rho.graph.par (rho.target.pick t) q :=
        Reach.head hpar (Reach.refl q)
      exact EqvOn.of_reach hpA hv (hqv ▸ hreach)

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.target_parent_is_rootStep
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.target_rootStep_eqvOn_of_complete

#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.target_parent_is_rootStep
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.target_rootStep_eqvOn_of_complete
