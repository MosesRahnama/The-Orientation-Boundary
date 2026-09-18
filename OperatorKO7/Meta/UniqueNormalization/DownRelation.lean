import OperatorKO7.Meta.UniqueNormalization.ConsistencyCore

/-!
# The relation `⇓`, and its consistency

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 5. Source: Kahrs and Smith, FSCD 2016,
Section 6, transcribed in `Roadmaps\klop\definitions.md` at D13.

## Fidelity block (frozen `definitions.md`, D13, Definition 38 with amendment A2)

> "The unary function Ind_A on binary relations over a term-coalgebra A is
> defined as follows: Ind_A(x) = (root-step union x-underline) . x"

Amendment A2 records that the second occurrence carries a destructor-tilde
underline the PDF text extractor drops. `DownStep` below uses the corrected form:
its fourth clause composes the **destructor tilde** of the relation with the
relation, never the relation with itself. Taking the extracted form would make
`⇓` transitive by construction, which is the one thing Section 7 exists to prove.

## Fidelity block (frozen `definitions.md`, D13, Definition 40)

> "Given a TRS with signature Sigma, and a term-coalgebra A, the relation down_A
> is a relation on A defined as follows: down_A = mu x. f_A(x), f_A(x) = x-inverse
> union Ind_A(x) union id_A union [hat x] union [bar x]."

> "f_A has no transitivity clause; that omission is the whole point."

`Down` is that least fixed point, presented by its universal property: it is
contained in every relation closed under `DownStep`. That gives the induction
principle `Down.induction` and the six introduction rules, with no recursor and
no transitivity.

`Down` ranges over the finite terms of the doubled signature, while the source's
unindexed relation ranges over `Ter^∞(Σ+X, ∅)`. The finite reading is the one
Theorem 66 consumes, since that theorem restricts to strongly finite coalgebras.
Lemma 41, monotonicity of `⇓` in the coalgebra, is `DownOn.toDown` in
`Coalgebra.lean`.

## What this module proves

`Down.sigmaClosed` is Proposition 42. `Down.constructorCompatible` is
Proposition 44, and with Lemma 28 it gives `Down.consistent`, which is
Proposition 43. Lemma 39 appears as `not_conTopped_destructor` together with
`rootStep_source_destructor`: root contraction and the destructor tilde both
leave constructor-topped terms alone, which is what makes the induction go
through.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Constructor systems -/

/-- A **Constructor TRS** in the sense of frozen definition D5: every left-hand
side is a destructor symbol applied to constructor terms. -/
def ConstructorRules (R : TRS (sigma ⊕ sigma) nu) : Prop :=
  ∀ rule ∈ R, ∃ (F : sigma) (ps : List (Term (sigma ⊕ sigma) nu)),
    rule.lhs = .app (Sum.inr F) ps ∧ ∀ p ∈ ps, ConOnly p

/-- A destructor-headed application is not constructor-topped. -/
theorem not_conTopped_destructor {d : sigma} (args : List (Term (sigma ⊕ sigma) nu)) :
    ¬ ConTopped (Term.app (Sum.inr d) args) := by
  rintro (⟨x, hx⟩ | ⟨f, as, hf⟩)
  · exact absurd hx (by simp)
  · simp only [Term.app.injEq] at hf
    exact absurd hf.1 (by simp)

/-- **Lemma 39, first half.** In a Constructor TRS the source of a root
contraction is destructor-headed, hence never constructor-topped. -/
theorem rootStep_source_destructor {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {a c : Term (sigma ⊕ sigma) nu} (h : rootStep R a c) :
    ∃ (d : sigma) (args : List (Term (sigma ⊕ sigma) nu)), a = .app (Sum.inr d) args := by
  obtain ⟨rule, hmem, s, ha, -⟩ := h
  obtain ⟨F, ps, hlhs, -⟩ := hR rule hmem
  refine ⟨F, ps.map (Subst.apply s), ?_⟩
  rw [ha, hlhs]
  simp [Subst.applyList_eq_map]

/-! ## Definition 38 with amendment A2, and Definition 40 -/

/-- One unfolding of the operator whose least fixed point is `⇓`.

The five clauses are, in order: the identity, the converse, root contraction
followed by the relation, the **destructor tilde** of the relation followed by
the relation, and the two tildes. The fourth clause is amendment A2: the first
factor is `x-underline`, never `x`, so no transitivity is built in. -/
def DownStep (R : TRS (sigma ⊕ sigma) nu) (E : CRel sigma nu) : CRel sigma nu :=
  fun a b =>
    a = b
    ∨ E b a
    ∨ (∃ c : Term (sigma ⊕ sigma) nu, rootStep R a c ∧ E c b)
    ∨ (∃ (d : sigma) (as cs : List (Term (sigma ⊕ sigma) nu)),
        a = .app (Sum.inr d) as ∧ List.Forall₂ E as cs ∧ E (.app (Sum.inr d) cs) b)
    ∨ hatRel E a b
    ∨ barRel E a b

/-- The operator is monotone. -/
theorem DownStep_mono {R : TRS (sigma ⊕ sigma) nu} {E E' : CRel sigma nu}
    (h : ∀ a b, E a b → E' a b) {p q : Term (sigma ⊕ sigma) nu}
    (hpq : DownStep R E p q) : DownStep R E' p q := by
  rcases hpq with heq | hinv | ⟨c, hc, hcb⟩ | ⟨d, as, cs, ha, hall, hcb⟩ | hhat | hbar
  · exact Or.inl heq
  · exact Or.inr (Or.inl (h _ _ hinv))
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, h _ _ hcb⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, as, cs, ha, forall₂_mono h hall, h _ _ hcb⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (tildeOn_mono h hhat)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (tildeOn_mono h hbar)))))

/-- **Definition 40.** The relation `⇓`, as the least relation closed under
`DownStep`. There is no transitivity clause. -/
def Down (R : TRS (sigma ⊕ sigma) nu) : CRel sigma nu :=
  fun a b => ∀ E : CRel sigma nu, (∀ p q, DownStep R E p q → E p q) → E a b

/-- `⇓` is contained in every relation closed under the operator. -/
theorem Down.least {R : TRS (sigma ⊕ sigma) nu} {E : CRel sigma nu}
    (hE : ∀ p q, DownStep R E p q → E p q) {a b : Term (sigma ⊕ sigma) nu}
    (h : Down R a b) : E a b :=
  h E hE

/-- `⇓` is closed under the operator. -/
theorem Down.closed {R : TRS (sigma ⊕ sigma) nu} (p q : Term (sigma ⊕ sigma) nu)
    (h : DownStep R (Down R) p q) : Down R p q := by
  intro E hE
  exact hE p q (DownStep_mono (fun x y hxy => hxy E hE) h)

/-! ### The six introduction rules -/

/-- Reflexivity. -/
theorem Down.refl {R : TRS (sigma ⊕ sigma) nu} (a : Term (sigma ⊕ sigma) nu) :
    Down R a a :=
  Down.closed a a (Or.inl rfl)

/-- Symmetry. -/
theorem Down.symm {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : Down R a b) : Down R b a :=
  Down.closed b a (Or.inr (Or.inl h))

/-- Root contraction composed with the relation. -/
theorem Down.rootComp {R : TRS (sigma ⊕ sigma) nu} {a c b : Term (sigma ⊕ sigma) nu}
    (h₁ : rootStep R a c) (h₂ : Down R c b) : Down R a b :=
  Down.closed a b (Or.inr (Or.inr (Or.inl ⟨c, h₁, h₂⟩)))

/-- The destructor tilde composed with the relation, amendment A2's clause. -/
theorem Down.barComp {R : TRS (sigma ⊕ sigma) nu} {d : sigma}
    {as cs : List (Term (sigma ⊕ sigma) nu)} {b : Term (sigma ⊕ sigma) nu}
    (h₁ : List.Forall₂ (Down R) as cs) (h₂ : Down R (.app (Sum.inr d) cs) b) :
    Down R (.app (Sum.inr d) as) b :=
  Down.closed _ b (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, as, cs, rfl, h₁, h₂⟩))))

/-- The constructor tilde. -/
theorem Down.hatCl {R : TRS (sigma ⊕ sigma) nu} {c : sigma}
    {as bs : List (Term (sigma ⊕ sigma) nu)} (h : List.Forall₂ (Down R) as bs) :
    Down R (.app (Sum.inl c) as) (.app (Sum.inl c) bs) :=
  Down.closed _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨.inl c, as, bs, ⟨c, rfl⟩, rfl, rfl, h⟩)))))

/-- The destructor tilde. -/
theorem Down.barCl {R : TRS (sigma ⊕ sigma) nu} {d : sigma}
    {as bs : List (Term (sigma ⊕ sigma) nu)} (h : List.Forall₂ (Down R) as bs) :
    Down R (.app (Sum.inr d) as) (.app (Sum.inr d) bs) :=
  Down.closed _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨.inr d, as, bs, ⟨d, rfl⟩, rfl, rfl, h⟩)))))

/-- Either tilde, chosen by the root symbol. -/
theorem Down.tildeCl {R : TRS (sigma ⊕ sigma) nu} {f : sigma ⊕ sigma}
    {as bs : List (Term (sigma ⊕ sigma) nu)} (h : List.Forall₂ (Down R) as bs) :
    Down R (.app f as) (.app f bs) := by
  cases f with
  | inl c => exact Down.hatCl h
  | inr d => exact Down.barCl h

/-! ### The induction principle -/

/-- Induction over `⇓`: a property closed under the operator, with the relation
itself available in each hypothesis, holds of every related pair. -/
theorem Down.induction {R : TRS (sigma ⊕ sigma) nu} {P : CRel sigma nu}
    (hstep : ∀ p q, DownStep R (fun x y => Down R x y ∧ P x y) p q → P p q)
    {a b : Term (sigma ⊕ sigma) nu} (h : Down R a b) : P a b := by
  have hclosed : ∀ p q, DownStep R (fun x y => Down R x y ∧ P x y) p q →
      (Down R p q ∧ P p q) := by
    intro p q hpq
    exact ⟨Down.closed p q (DownStep_mono (fun x y hxy => hxy.1) hpq), hstep p q hpq⟩
  exact (Down.least hclosed h).2

/-! ## Proposition 42: `⇓` is Sigma-closed -/

/-- **Proposition 42.** `⇓` is Sigma-closed. Both tilde clauses are introduction
rules, and every symbol of the doubled signature is a constructor or a
destructor. -/
theorem Down.sigmaClosed (R : TRS (sigma ⊕ sigma) nu) : SigmaClosed (Down R) := by
  intro t u ht
  obtain ⟨f, as, bs, -, rfl, rfl, hall⟩ := ht
  exact Down.tildeCl hall

/-! ## `⇓` contains the rewrite relation -/

/-- A reflexive relation relates a one-position replacement argumentwise. -/
theorem forall₂_append_middle {alpha : Type u} {r : alpha → alpha → Prop}
    (hrefl : ∀ x, r x x) (pre post : List alpha) {a b : alpha} (hab : r a b) :
    List.Forall₂ r (pre ++ a :: post) (pre ++ b :: post) := by
  induction pre with
  | nil => exact List.Forall₂.cons hab (forall₂_self hrefl post)
  | cons p ps ih => exact List.Forall₂.cons (hrefl p) ih

/-- Root contraction is part of `⇓`. -/
theorem Down.of_rootStep {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : rootStep R a b) : Down R a b :=
  Down.rootComp h (Down.refl b)

/-- Every rewrite step is part of `⇓`. Reflexivity and the two tilde clauses give
the context closure; the composition clause gives the root case. -/
theorem Down.of_step {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : Step R a b) : Down R a b := by
  induction h with
  | root hr => exact Down.of_rootStep hr
  | arg f pre post _ ih =>
      exact Down.tildeCl (forall₂_append_middle Down.refl pre post ih)

/-! ## Proposition 44: `⇓` is constructor-compatible -/

/-- **Proposition 44.** In a Constructor TRS, `⇓` is constructor-compatible.

The induction is the one the operator supplies. Reflexivity and the converse
clause are immediate. Root contraction and the two destructor clauses cannot
apply, because their source is destructor-headed while a constructor-topped term
is not; that is Lemma 39. The constructor tilde clause is the conclusion
itself. -/
theorem Down.constructorCompatible {R : TRS (sigma ⊕ sigma) nu}
    (hR : ConstructorRules R) : ConstructorCompatible (Down R) := by
  intro a b hca hcb hab
  revert hca hcb
  refine Down.induction (P := fun p q => ConTopped p → ConTopped q →
    (∃ x : nu, p = .var x ∧ q = .var x) ∨
    (∃ (f : sigma) (xs ys : List (Term (sigma ⊕ sigma) nu)),
      p = .app (.inl f) xs ∧ q = .app (.inl f) ys ∧ List.Forall₂ (Down R) xs ys)) ?_ hab
  intro p q hpq
  rcases hpq with heq | hinv | ⟨c, hroot, -⟩ | ⟨d, as, cs, hpd, -, -⟩ | hhat | hbar
  · -- identity
    subst heq
    intro hcp _
    rcases hcp with ⟨x, rfl⟩ | ⟨f, args, rfl⟩
    · exact Or.inl ⟨x, rfl, rfl⟩
    · exact Or.inr ⟨f, args, args, rfl, rfl, forall₂_self Down.refl args⟩
  · -- converse
    intro hcp hcq
    rcases hinv.2 hcq hcp with ⟨x, hq, hp⟩ | ⟨f, xs, ys, hq, hp, hall⟩
    · exact Or.inl ⟨x, hp, hq⟩
    · exact Or.inr ⟨f, ys, xs, hp, hq, forall₂_swap (fun _ _ hx => Down.symm hx) hall⟩
  · -- root contraction: the source is destructor-headed
    intro hcp _
    obtain ⟨d, args, rfl⟩ := rootStep_source_destructor hR hroot
    exact absurd hcp (not_conTopped_destructor args)
  · -- destructor tilde composed with the relation: same obstruction
    intro hcp _
    subst hpd
    exact absurd hcp (not_conTopped_destructor as)
  · -- constructor tilde: this is the conclusion
    obtain ⟨f, as, bs, ⟨c, rfl⟩, rfl, rfl, hall⟩ := hhat
    intro _ _
    exact Or.inr ⟨c, as, bs, rfl, rfl, forall₂_mono (fun _ _ hx => hx.1) hall⟩
  · -- destructor tilde: the source is destructor-headed
    obtain ⟨f, as, bs, ⟨d, rfl⟩, rfl, rfl, -⟩ := hbar
    intro hcp _
    exact absurd hcp (not_conTopped_destructor as)

/-! ## Proposition 43: `⇓` is consistent -/

/-- **Proposition 43.** In a Constructor TRS, `⇓` relates two variables only when
they are the same variable. This is Lemma 28 applied to Proposition 44. -/
theorem Down.consistent {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {x y : nu} (h : Down R (.var x) (.var y)) : x = y := by
  rcases Down.constructorCompatible hR _ _ (ConTopped.var x) (ConTopped.var y) h with
    ⟨z, hx, hy⟩ | ⟨f, xs, ys, hx, -, -⟩
  · have hxz : x = z := by simpa using hx
    have hyz : y = z := by simpa using hy
    rw [hxz, hyz]
  · exact absurd hx (by simp)

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.ConstructorRules
#check @OperatorKO7.Meta.UniqueNormalization.DownStep
#check @OperatorKO7.Meta.UniqueNormalization.Down

#print axioms OperatorKO7.Meta.UniqueNormalization.Down.closed
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.induction
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.sigmaClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.of_step
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.Down.consistent
#print axioms OperatorKO7.Meta.UniqueNormalization.rootStep_source_destructor
