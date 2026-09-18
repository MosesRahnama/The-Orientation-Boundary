import OperatorKO7.Meta.UniqueNormalization.Section7SupportKernel

/-!
# Constructor compatibility of the Section 7 support kernel

The finite support construction preserves constructor compatibility without a
transitivity premise.  A constructor-topped source cannot perform a root peel,
and subterm closure supplies the carrier membership needed to reinsert aligned
constructor arguments into the next finite support stage.

Relation: the finite diagonal support kernel.
Closure: constructor decomposition and finite support saturation.
Strategy: full rewriting.
Trust: kernel checked; no external certificate or new axiom.
Scope: arbitrary constructor TRSs and finite coalgebras.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- A root-peel path starting at a constructor-topped term is reflexive. -/
theorem RootPeelPath.eq_of_conTopped
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (hR : ConstructorRules R) {a b : Term (sigma ⊕ sigma) nu}
    (hcon : ConTopped a) (h : RootPeelPath A R a b) : a = b := by
  cases h with
  | refl => rfl
  | head _ hab _ =>
      exact (not_conTopped_peel (A := A) hR (Or.inl hab) hcon).elim

/-- Root peeling preserves constructor compatibility of its independently
supplied seed on a subterm-closed carrier. -/
theorem RootPeeledSeed.constructorCompatible
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {seed : CRel sigma nu} (hseed : ConstructorCompatible seed) :
    ConstructorCompatible (RootPeeledSeed A R seed) := by
  intro a b hca hcb hab
  have hmem := RootPeeledSeed.mem hab
  obtain ⟨r, s, har, hbs, hrs⟩ := hab
  have harEq : a = r := RootPeelPath.eq_of_conTopped hR hca har
  have hbsEq : b = s := RootPeelPath.eq_of_conTopped hR hcb hbs
  subst r
  subst s
  rcases CT.constructorCompatible hseed a b hca hcb hrs with hvar |
      ⟨c, xs, ys, ha, hb, hargs⟩
  · exact Or.inl hvar
  · have hax : Term.app (.inl c) xs ∈ A := by rw [← ha]; exact hmem.1
    have hby : Term.app (.inl c) ys ∈ A := by rw [← hb]; exact hmem.2
    have hargsMem := forall₂_and_mem hargs
      (fun x hx => hA.arg hax hx) (fun y hy => hA.arg hby hy)
    refine Or.inr ⟨c, xs, ys, ha, hb, ?_⟩
    exact forall₂_mono (fun x y h =>
      RootPeeledSeed.of_context h.1 h.2.1 h.2.2) hargsMem

/-- One finite support round preserves constructor compatibility. -/
theorem PGraph.pairSetRel_supportSuccSet_constructorCompatible
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : ConstructorCompatible (PGraph.pairSetRel S)) :
    ConstructorCompatible (PGraph.pairSetRel (PGraph.supportSuccSet A R S)) := by
  intro a b hca hcb hab
  rcases PGraph.mem_supportSuccSet_iff.mp hab with hold | ⟨hpair, hctx⟩
  · rcases hS a b hca hcb hold with hvar | ⟨c, xs, ys, ha, hb, hargs⟩
    · exact Or.inl hvar
    · refine Or.inr ⟨c, xs, ys, ha, hb, ?_⟩
      exact forall₂_mono (fun _ _ h =>
        PGraph.mem_supportSuccSet_iff.mpr (Or.inl h)) hargs
  · have hm := PGraph.mem_residualPairUniverse_iff.mp hpair
    rcases CT.constructorCompatible
        (RootPeeledSeed.constructorCompatible hA hR hS)
        a b hca hcb hctx with hvar | ⟨c, xs, ys, ha, hb, hargs⟩
    · exact Or.inl hvar
    · have hax : Term.app (.inl c) xs ∈ A := by rw [← ha]; exact hm.1
      have hby : Term.app (.inl c) ys ∈ A := by rw [← hb]; exact hm.2
      have hargsMem := forall₂_and_mem hargs
        (fun x hx => hA.arg hax hx) (fun y hy => hA.arg hby hy)
      refine Or.inr ⟨c, xs, ys, ha, hb, ?_⟩
      exact forall₂_mono (fun x y h =>
        PGraph.mem_supportSuccSet_iff.mpr
          (Or.inr ⟨PGraph.mem_residualPairUniverse_iff.mpr ⟨h.1, h.2.1⟩,
            h.2.2⟩)) hargsMem

/-- Every finite support stage preserves constructor compatibility. -/
theorem PGraph.pairSetRel_supportIter_constructorCompatible
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {S : Finset (PGraph.ResidualPair sigma nu)}
    (hS : ConstructorCompatible (PGraph.pairSetRel S)) :
    ∀ n, ConstructorCompatible (PGraph.pairSetRel (PGraph.supportIter A R S n)) := by
  intro n
  induction n with
  | zero => exact hS
  | succ n ih =>
      change ConstructorCompatible
        (PGraph.pairSetRel (PGraph.supportSuccSet A R (PGraph.supportIter A R S n)))
      exact PGraph.pairSetRel_supportSuccSet_constructorCompatible hA hR ih

/-- The finite diagonal seed is constructor-compatible on a coalgebra. -/
theorem PGraph.diagonalSupportSeed_constructorCompatible
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A) :
    ConstructorCompatible (PGraph.pairSetRel (PGraph.diagonalSupportSeed A)) := by
  intro a b hca _ hab
  have hm := PGraph.mem_diagonalSupportSeed_iff.mp hab
  have heq : a = b := hm.2.2
  subst b
  rcases hca with ⟨x, ha⟩ | ⟨c, xs, ha⟩
  · exact Or.inl ⟨x, ha, ha⟩
  · have happ : Term.app (.inl c) xs ∈ A := by rw [← ha]; exact hm.1
    refine Or.inr ⟨c, xs, xs, ha, ha, ?_⟩
    exact forall₂_self_of (fun x hx =>
      PGraph.mem_diagonalSupportSeed_iff.mpr
        ⟨hA.arg happ hx, hA.arg happ hx, rfl⟩)

/-- The stabilized diagonal support kernel is constructor-compatible without any
transitivity hypothesis. -/
theorem PGraph.section7SupportKernel_constructorCompatible
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) :
    ConstructorCompatible (PGraph.section7SupportKernel A R) := by
  exact PGraph.pairSetRel_supportIter_constructorCompatible hA hR
    (PGraph.diagonalSupportSeed_constructorCompatible hA)
    (PGraph.residualPairUniverse A).card

/-- Constructor-headed kernel pairs have the same constructor and pairwise
kernel-related arguments. The reverse direction uses carrier membership. -/
theorem PGraph.section7SupportKernel_constructor_apps_iff
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {f g : sigma} {xs ys : List (Term (sigma ⊕ sigma) nu)}
    (hx : Term.app (.inl f) xs ∈ A) (hy : Term.app (.inl g) ys ∈ A) :
    PGraph.section7SupportKernel A R (.app (.inl f) xs) (.app (.inl g) ys) ↔
      f = g ∧ List.Forall₂ (PGraph.section7SupportKernel A R) xs ys := by
  constructor
  · intro hxy
    have h := (CT.constructor_apps_iff
      (PGraph.section7SupportKernel_constructorCompatible hA hR)).mp (CT.base hxy)
    have hargsMem := forall₂_and_mem h.2
      (fun x hx' => hA.arg hx hx') (fun y hy' => hA.arg hy hy')
    exact ⟨h.1, forall₂_mono (fun x y hxy =>
      (PGraph.section7SupportKernel_context_iff hxy.1 hxy.2.1).mp hxy.2.2) hargsMem⟩
  · rintro ⟨rfl, hargs⟩
    apply (PGraph.section7SupportKernel_context_iff hx hy).mp
    exact CT.app (forall₂_mono (fun _ _ h => CT.base h) hargs)

end OperatorKO7.Meta.UniqueNormalization
