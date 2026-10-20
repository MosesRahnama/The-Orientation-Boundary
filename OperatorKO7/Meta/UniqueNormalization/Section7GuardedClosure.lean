import OperatorKO7.Meta.UniqueNormalization.Section7RootTargets

/-!
# Section 7 guarded congruence closure

Campaign: `Distinction_Boundary/Roadmaps/klop/ROADMAP.md`, finite-coalgebra
foundation for the Lemma 64 repair.

The repository's `SigmaClosed` and `CT` APIs are global over all finite terms.
Section 7 of the source works with a relation `E ⊆ A × A` on one strongly finite
coalgebra.  We must not silently promote `SigmaClosedOn A E` to global
`SigmaClosed E`.

The safe bridge is the guarded relation

  `OnGuard A E a b := a ∈ A → b ∈ A → E a b`.

Subterm closure of `A` makes this guard globally Sigma-closed whenever `E` is
Sigma-closed on `A`.  Consequently `CT E` collapses back to `E` whenever both
endpoints lie in `A`.  This is the exact carrier bridge needed to consume the
global Theorem-37 `CT` conclusion inside the finite proof-graph argument.

Trust: kernel checked.  No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- The global guard of a relation that is semantically intended only on `A`. -/
def OnGuard (A : List (Term (sigma ⊕ sigma) nu)) (E : CRel sigma nu) : CRel sigma nu :=
  fun a b => a ∈ A → b ∈ A → E a b

/-- Eliminate an `OnGuard` argumentwise relation when membership of every paired
argument is known. -/
theorem forall₂_onGuard_elim
    {A : List (Term (sigma ⊕ sigma) nu)} {E : CRel sigma nu} :
    ∀ {as bs : List (Term (sigma ⊕ sigma) nu)},
      (∀ a ∈ as, a ∈ A) → (∀ b ∈ bs, b ∈ A) →
      List.Forall₂ (OnGuard A E) as bs → List.Forall₂ E as bs := by
  intro as bs ha hb hall
  induction hall with
  | nil => exact List.Forall₂.nil
  | @cons a b as bs hab htail ih =>
      exact List.Forall₂.cons
        (hab (ha a (List.mem_cons_self ..)) (hb b (List.mem_cons_self ..)))
        (ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))
          (fun y hy => hb y (List.mem_cons_of_mem _ hy)))

/-- A relation that is Sigma-closed on a subterm-closed finite coalgebra has a
globally Sigma-closed guarded extension. -/
theorem SigmaClosedOn.onGuard_sigmaClosed
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {E : CRel sigma nu} (hcl : SigmaClosedOn A E) : SigmaClosed (OnGuard A E) := by
  intro t u htilde ht hu
  rcases htilde with ⟨f, as, bs, -, rfl, rfl, hall⟩
  apply hcl _ _ ht hu
  refine ⟨f, as, bs, trivial, rfl, rfl, ?_⟩
  exact forall₂_onGuard_elim
    (fun a ha => Coalgebra.arg hA ht ha)
    (fun b hb => Coalgebra.arg hA hu hb) hall

/-- `CT E` cannot create a new pair between members of `A` once `E` is
Sigma-closed on `A`.  This is the finite-carrier elimination principle for the
global congruence-closure API. -/
theorem SigmaClosedOn.eq_of_CT
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {E : CRel sigma nu} (hcl : SigmaClosedOn A E)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (h : CT E a b) : E a b := by
  have hguard : OnGuard A E a b :=
    CT.least (fun x y hxy _ _ => hxy) (hcl.onGuard_sigmaClosed hA) h
  exact hguard ha hb

/-- Specialization of the guarded-closure bridge to the equality represented by
a complete targeted proof graph. -/
theorem TermTargetedPGraph.eqvOn_of_CT_of_complete
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (h : CT (EqvOn A rho.graph.par) a b) : EqvOn A rho.graph.par a b :=
  (rho.sigmaClosedOn_of_complete hA hR hcomplete).eq_of_CT hA ha hb h

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.OnGuard
#check @OperatorKO7.Meta.UniqueNormalization.forall₂_onGuard_elim
#check @OperatorKO7.Meta.UniqueNormalization.SigmaClosedOn.onGuard_sigmaClosed
#check @OperatorKO7.Meta.UniqueNormalization.SigmaClosedOn.eq_of_CT
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.eqvOn_of_CT_of_complete

#print axioms OperatorKO7.Meta.UniqueNormalization.OnGuard
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_onGuard_elim
#print axioms OperatorKO7.Meta.UniqueNormalization.SigmaClosedOn.onGuard_sigmaClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.SigmaClosedOn.eq_of_CT
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.eqvOn_of_CT_of_complete
