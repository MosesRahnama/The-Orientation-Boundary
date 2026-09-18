import OperatorKO7.Meta.UniqueNormalization.Lemma36

/-!
# Theorem 37 and Corollary 45

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 5. Source: Kahrs and Smith, FSCD 2016,
Definition 20, Definition 30, Theorem 37, Corollary 45.

## Fidelity block (frozen `definitions.md`, D8, Definition 20)

> "A TRS is called strongly almost non-omega-overlapping iff (i) all omega-overlaps
> are in root position, (ii) whenever two left-hand sides are omega-unifiable then
> their rules have a common generalisation."

> "Two rewrite rules l_1 -> r_1 and l_2 -> r_2 have a common generalisation
> l_3 -> r_3 iff there are substitutions s_1, s_2 such that s_1(l_3) = l_1 and
> s_2(l_3) = l_2, and s_1(r_3) = r_1 and s_2(r_3) = r_2, all variables in r_3
> occur in l_3."

The last clause is carried in its literal occurrence form, which is what
Corollary 35 consumes.

## Fidelity block (frozen `definitions.md`, D12, Definition 30 with amendment A3)

> "Given a Constructor TRS over a signature Sigma, a consistency invariant is a
> consistent and Sigma-closed relation S on a term-coalgebra A such that for any
> constructor-compatible equivalence =_S contained in S we have
> root-step-inverse . (=_S)-underline . root-step contained in CT(=_S)."

The underline on the middle factor is amendment A3, forced by the paper's own
gloss that the two redexes "share their root symbol and are semantically equal
below the root". `ConsistencyInvariant` below uses `barRel`, the destructor
tilde, for that factor.

## What is proved

`thm37` is Theorem 37: in a strongly almost non-omega-overlapping Constructor
TRS, a semantical critical pair lands inside `CT` of the equivalence. Both
branches of the source proof appear. Two contractions of one rule are Corollary
35. Two contractions of different rules go through Lemma 36 to an
omega-unification of the two left-hand sides, then through Definition 20 to a
common generalisation, and then through Corollary 35 applied to that
generalisation.

`cor45` is Corollary 45: `⇓` is a consistency invariant. Its three parts are
Proposition 43, Proposition 42, and Theorem 37.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Definition 20 -/

/-- **Definition 20.** Every omega-overlap is at the root, and omega-unifiable
left-hand sides come from rules with a common generalisation whose right-hand
side uses only variables of its left-hand side. -/
def StronglyAlmostNonOmegaOverlapping (R : TRS sigma nu) : Prop :=
  (∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ s : Term sigma nu,
      ProperSubterm s r₁.lhs → s.isApp = true → ¬ OmegaUnifiable s r₂.lhs)
  ∧ (∀ r₁ ∈ R, ∀ r₂ ∈ R, OmegaUnifiable r₁.lhs r₂.lhs →
      ∃ g : CommonGeneralisation r₁ r₂, ∀ x : nu, VarOccurs x g.gr → VarOccurs x g.gl)

/-! ## Definition 30 with amendment A3 -/

/-- **Definition 30.** A consistency invariant: a consistent and Sigma-closed
relation whose semantical critical pairs, formed around the **destructor tilde**
of any constructor-compatible equivalence below it, stay inside `CT` of that
equivalence. -/
def ConsistencyInvariant (R : TRS (sigma ⊕ sigma) nu) (S : CRel sigma nu) : Prop :=
  (∀ x y : nu, S (.var x) (.var y) → x = y)
  ∧ SigmaClosed S
  ∧ ∀ E : CRel sigma nu, (∀ a b, E a b → S a b) →
      (∀ x y : Term (sigma ⊕ sigma) nu, E x y → E y x) →
      (∀ x y z : Term (sigma ⊕ sigma) nu, E x y → E y z → E x z) →
      ConstructorCompatible E →
      ∀ t₁ t₂ t₃ t₄ : Term (sigma ⊕ sigma) nu,
        rootStep R t₂ t₁ → barRel E t₂ t₃ → rootStep R t₃ t₄ → CT E t₁ t₄

/-! ## A term whose instance is a constructor term is a constructor term -/

/-- Substitution adds symbols, so a term with a constructor-only instance is
itself constructor-only. This is the part of Lemma 19 that Theorem 37 uses: the
left-hand side of a common generalisation of two Constructor rules has
constructor direct subterms. -/
theorem ConOnly.of_apply {s : Subst (sigma ⊕ sigma) nu} :
    ∀ {t : Term (sigma ⊕ sigma) nu}, ConOnly (Subst.apply s t) → ConOnly t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro _; exact ConOnly.var x
  | happ f args ih =>
      intro h
      simp only [Subst.apply_app, Subst.applyList_eq_map] at h
      obtain ⟨c, rfl, hargs⟩ := h.app_inv
      refine ConOnly.app c _ ?_
      intro q hq
      exact ih q hq (hargs _ (List.mem_map_of_mem hq))

/-! ## Theorem 37 -/

/-- **Theorem 37.** In a strongly almost non-omega-overlapping Constructor TRS,
every semantical critical pair of a constructor-compatible equivalence lands
inside `CT` of that equivalence.

The relation `S` of Definition 30 plays no part in this argument, so the theorem
is stated for the equivalence alone and `cor45` supplies the rest. -/
theorem thm37 {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    {E : CRel sigma nu}
    (hsymm : ∀ x y : Term (sigma ⊕ sigma) nu, E x y → E y x)
    (htrans : ∀ x y z : Term (sigma ⊕ sigma) nu, E x y → E y z → E x z)
    (hCC : ConstructorCompatible E)
    {t₁ t₂ t₃ t₄ : Term (sigma ⊕ sigma) nu}
    (h₁ : rootStep R t₂ t₁) (h₂ : barRel E t₂ t₃) (h₃ : rootStep R t₃ t₄) :
    CT E t₁ t₄ := by
  obtain ⟨rule₁, hm₁, s, ht₂, ht₁⟩ := h₁
  obtain ⟨rule₂, hm₂, r, ht₃, ht₄⟩ := h₃
  obtain ⟨F₁, ps, hlhs₁, hps⟩ := hR rule₁ hm₁
  obtain ⟨F₂, qs, hlhs₂, hqs⟩ := hR rule₂ hm₂
  obtain ⟨fsym, As, Bs, ⟨dd, hfd⟩, hAt₂, hBt₃, hAB⟩ := h₂
  subst hfd
  -- Both redexes in application form.
  have ht₂' : t₂ = Term.app (Sum.inr F₁) (ps.map (Subst.apply s)) := by
    rw [ht₂, hlhs₁]; simp [Subst.applyList_eq_map]
  have ht₃' : t₃ = Term.app (Sum.inr F₂) (qs.map (Subst.apply r)) := by
    rw [ht₃, hlhs₂]; simp [Subst.applyList_eq_map]
  rw [ht₂'] at hAt₂
  rw [ht₃'] at hBt₃
  simp only [Term.app.injEq] at hAt₂ hBt₃
  obtain ⟨hd₁, hAs⟩ := hAt₂
  obtain ⟨hd₂, hBs⟩ := hBt₃
  subst hAs
  subst hBs
  have hF₁ : F₁ = dd := by simpa using hd₁
  have hF₂ : F₂ = dd := by simpa using hd₂
  have hFF : F₂ = F₁ := by rw [hF₂, hF₁]
  rw [hFF] at hlhs₂
  -- Lemma 36: the two left-hand sides omega-unify.
  have hOU : OmegaUnifiable rule₁.lhs rule₂.lhs := by
    rw [hlhs₁, hlhs₂]
    exact lemma36 hsymm htrans hCC hps hqs hAB
  obtain ⟨g, hgvar⟩ := hstrong.2 rule₁ hm₁ rule₂ hm₂ hOU
  -- Both contracta are instances of the generalised right-hand side.
  have hgt₁ : t₁ = Subst.apply (Subst.comp s g.s₁) g.gr := by
    rw [Subst.apply_comp, g.apply_gr₁, ht₁]
  have hgt₄ : t₄ = Subst.apply (Subst.comp r g.s₂) g.gr := by
    rw [Subst.apply_comp, g.apply_gr₂, ht₄]
  rw [hgt₁, hgt₄]
  -- The two redexes are `CT`-related, used in the variable branch.
  have hCTroot : CT E (Term.app (Sum.inr F₁) (ps.map (Subst.apply s)))
      (Term.app (Sum.inr F₁) (qs.map (Subst.apply r))) :=
    CT.app (forall₂_mono (fun _ _ hx => CT.base hx) hAB)
  have hgl₁ := g.apply_gl₁
  have hgl₂ := g.apply_gl₂
  cases hgl : g.gl with
  | var x =>
      -- The generalised left-hand side is a variable: both contracta reduce to
      -- the two redexes themselves.
      rw [hgl] at hgl₁ hgl₂
      simp only [Subst.apply_var] at hgl₁ hgl₂
      refine lemma34 CT.sigmaClosed g.gr ?_
      intro y hy
      have hyx : y = x := by
        have hocc := hgvar y hy
        rw [hgl] at hocc
        cases hocc with
        | here => rfl
      subst hyx
      show CT E (Subst.apply s (g.s₁ y)) (Subst.apply r (g.s₂ y))
      rw [hgl₁, hgl₂, hlhs₁, hlhs₂]
      simpa [Subst.applyList_eq_map] using hCTroot
  | app G rs =>
      -- The generalised left-hand side is an application: Corollary 35 applies
      -- to the common generalisation.
      rw [hgl, hlhs₁] at hgl₁
      rw [hgl, hlhs₂] at hgl₂
      simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq] at hgl₁ hgl₂
      obtain ⟨hG, hrs₁⟩ := hgl₁
      obtain ⟨-, hrs₂⟩ := hgl₂
      have hrsCon : ∀ p ∈ rs, ConOnly p := by
        intro p hp
        refine ConOnly.of_apply (s := g.s₁) ?_
        exact hps _ (by rw [← hrs₁]; exact List.mem_map_of_mem hp)
      have hvarcond : ∀ x : nu, VarOccurs x g.gr →
          VarOccurs x (Term.app (Sum.inr F₁) rs) := by
        intro x hx
        have hocc := hgvar x hx
        rw [hgl, hG] at hocc
        exact hocc
      have hmapl : rs.map (Subst.apply (Subst.comp s g.s₁)) = ps.map (Subst.apply s) := by
        rw [← hrs₁, List.map_map]
        exact List.map_congr_left (fun a _ => Subst.apply_comp s g.s₁ a)
      have hmapr : rs.map (Subst.apply (Subst.comp r g.s₂)) = qs.map (Subst.apply r) := by
        rw [← hrs₂, List.map_map]
        exact List.map_congr_left (fun a _ => Subst.apply_comp r g.s₂ a)
      refine cor35 hCC hrsCon hvarcond ?_
      rw [hmapl, hmapr]
      exact hAB

/-! ## Corollary 45 -/

/-- **Corollary 45.** In a strongly almost non-omega-overlapping Constructor TRS,
`⇓` is a consistency invariant. -/
theorem cor45 {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R) :
    ConsistencyInvariant R (Down R) :=
  ⟨fun _ _ h => Down.consistent hR h, Down.sigmaClosed R,
    fun _ _ hsymm htrans hCC _ _ _ _ h₁ h₂ h₃ =>
      thm37 hR hstrong hsymm htrans hCC h₁ h₂ h₃⟩

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.StronglyAlmostNonOmegaOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.ConsistencyInvariant

#print axioms OperatorKO7.Meta.UniqueNormalization.ConOnly.of_apply
#print axioms OperatorKO7.Meta.UniqueNormalization.thm37
#print axioms OperatorKO7.Meta.UniqueNormalization.cor45
