import OperatorKO7.Meta.UniqueNormalization.Section7GuardedClosure
import OperatorKO7.Meta.UniqueNormalization.Theorem37

/-!
# Root determinism and target-redex closure

Common generalisations of finitely unifiable rule pairs prove root determinism
over every signature. The strong omega-overlap condition supplies them, without
constructor, graph or finite-coalgebra premises. The existing constructor and
target-redex theorem types are unchanged.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- Common generalisations are needed only for rule pairs that admit a finite
unifier when the target is root determinism. -/
theorem root_deterministic_of_finite_common_generalisations
    {R : TRS sigma nu}
    (hcommon : ∀ r ∈ R, ∀ s ∈ R, Unifiable r.lhs s.lhs →
      Nonempty (CommonGeneralisation r s)) : Deterministic R := by
  rintro a b c ⟨r, hr, s, has, hbs⟩ ⟨r', hr', t, hat, hct⟩
  have hu : Unifiable r.lhs r'.lhs := ⟨s, t, has.symm.trans hat⟩
  obtain ⟨g⟩ := hcommon r hr r' hr' hu
  exact rootStep_eq_of_commonGeneralisation g s t has hat hbs hct

/-- The strong overlap condition implies root determinism over every signature;
constructor rules and a finite coalgebra are unnecessary. -/
theorem StronglyAlmostNonOmegaOverlapping.deterministic
    {R : TRS sigma nu} (h : StronglyAlmostNonOmegaOverlapping R) : Deterministic R := by
  apply root_deterministic_of_finite_common_generalisations
  intro r hr s hs hu
  obtain ⟨g, _⟩ := h.2 r hr s hs (OmegaUnifiable.of_unifiable hu)
  exact ⟨g⟩

/-- Root determinism itself determines each right-hand side from its match. -/
theorem Deterministic.rhsDetermined {R : TRS sigma nu} (h : Deterministic R) :
    TRS.RhsDetermined R := by
  intro r hr s t hst
  exact h _ _ _ ⟨r, hr, s, rfl, rfl⟩ ⟨r, hr, t, hst, rfl⟩

theorem StronglyAlmostNonOmegaOverlapping.rhsDetermined
    {R : TRS sigma nu} (h : StronglyAlmostNonOmegaOverlapping R) :
    TRS.RhsDetermined R :=
  h.deterministic.rhsDetermined

theorem StronglyAlmostNonOmegaOverlapping.almost
    {R : TRS sigma nu} (h : StronglyAlmostNonOmegaOverlapping R) :
    AlmostNonOmegaOverlapping R :=
  ⟨h.1, h.deterministic⟩

/-- Syntactic equality satisfies constructor compatibility on every signature. -/
theorem constructorCompatible_equality :
    ConstructorCompatible ((· = ·) : Term (sigma ⊕ sigma) nu →
      Term (sigma ⊕ sigma) nu → Prop) := by
  intro a b hca _ hab
  rcases hca with ⟨x, ha⟩ | ⟨f, xs, ha⟩
  · exact Or.inl ⟨x, ha, hab.symm.trans ha⟩
  · exact Or.inr ⟨f, xs, xs, ha, hab.symm.trans ha,
      forall₂_self_of (fun _ _ => rfl)⟩

theorem sigmaClosed_equality :
    SigmaClosed ((· = ·) : Term (sigma ⊕ sigma) nu →
      Term (sigma ⊕ sigma) nu → Prop) := by
  rintro a b ⟨f, xs, ys, _, ha, hb, hall⟩
  have hxy : xs = ys := by simpa only [List.forall₂_eq_eq_eq] using hall
  exact ha.trans ((congrArg (Term.app f) hxy).trans hb.symm)

/-- Closing equality under applications adds no pair. -/
theorem CT_equality_iff (a b : Term (sigma ⊕ sigma) nu) :
    CT ((· = ·) : Term (sigma ⊕ sigma) nu →
      Term (sigma ⊕ sigma) nu → Prop) a b ↔ a = b :=
  ⟨CT.least (fun _ _ h => h) sigmaClosed_equality, CT.base⟩

/-- Strongly almost non-omega-overlapping rules determine the contractum of
every root rewrite. The conclusion needs no constructor-shape, finite-carrier,
or graph hypothesis. -/
theorem root_deterministic_of_strong
    {R : TRS (sigma ⊕ sigma) nu}
    (hstrong : StronglyAlmostNonOmegaOverlapping R) : Deterministic R :=
  hstrong.deterministic


/-- A selected target root redex is graph-equivalent to every one of its root
contracta under the exact strong Constructor-TRS condition consumed by Theorem
37.  No root-determinism premise is required. -/
theorem TermTargetedPGraph.target_rootStep_eqvOn_of_complete_strong
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete)
    {t v : Term (sigma ⊕ sigma) nu}
    (ht : t ∈ A) (hv : v ∈ A)
    (hroot : rootStep R (rho.target.pick t) v) :
    EqvOn A rho.graph.par (rho.target.pick t) v :=
  rho.target_rootStep_eqvOn_of_complete hA hR
    (root_deterministic_of_strong hstrong) hcomplete ht hv hroot

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.target_rootStep_eqvOn_of_complete_strong
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.target_rootStep_eqvOn_of_complete_strong
