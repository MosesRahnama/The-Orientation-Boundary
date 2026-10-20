import OperatorKO7.Meta.UniqueNormalization.Coalgebra

/-!
# Section 7: the invariant as joinability modulo the constructor tilde

Write `⊳` for `JoinStep R`: a root contraction, or the replacement of the arguments of
a destructor-topped term by `Down`-related arguments (`barRel (Down R)`). The terminal
relation is equality or the constructor tilde of `Down` (`hatRel (Down R)`).

`down_iff_join` proves, for every rewrite system over the doubled signature,

  `Down R t u ↔ ∃ t' u', t ⊳* t' ∧ u ⊳* u' ∧ (t' = u' ∨ hatRel (Down R) t' u')`.

Both directions use only the six generating clauses of `Down`: no overlap hypothesis,
no determinism of root steps, and no transitivity. `downOn_iff_join` is the same
statement on a finite carrier `A`: every path node, every edge endpoint and both
terminal witnesses are members of `A`. It needs no subterm closure of `A`, because each
membership it uses is stated explicitly.

The terminal relation is reflexive and symmetric. It is not claimed transitive: with a
unary constructor, its transitivity implies transitivity of `Down` on arguments.

Relation: `Down R`, `DownOn A R`.
Closure: reflexive-transitive closure of `JoinStep`, then one terminal step.
Strategy: full rewriting.
Trust: kernel checked; no external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## The global relation -/

/-- `⊳`: a root contraction, or a destructor-topped term whose arguments are replaced
by `Down`-related arguments. -/
def JoinStep (R : TRS (sigma ⊕ sigma) nu) : CRel sigma nu :=
  fun a b => rootStep R a b ∨ barRel (Down R) a b

/-- The terminal relation, equality or the constructor tilde of `Down`, is symmetric. -/
theorem eq_or_hatRel_down_symm {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : a = b ∨ hatRel (Down R) a b) :
    b = a ∨ hatRel (Down R) b a := by
  rcases h with rfl | hhat
  · exact Or.inl rfl
  · exact Or.inr (tildeOn_flip (tildeOn_mono (fun _ _ hxy => Down.symm hxy) hhat))

/-- The terminal relation is part of `Down`. -/
theorem Down.of_eq_or_hatRel {R : TRS (sigma ⊕ sigma) nu}
    {a b : Term (sigma ⊕ sigma) nu} (h : a = b ∨ hatRel (Down R) a b) : Down R a b := by
  rcases h with rfl | hhat
  · exact Down.refl _
  · obtain ⟨f, as, bs, ⟨c, rfl⟩, rfl, rfl, hall⟩ := hhat
    exact Down.hatCl hall

/-- `Down` absorbs a `⊳` path at its left endpoint: the root clause and the destructor
composition clause of `Down` each consume one edge. -/
theorem Down.of_joinStep_reach {R : TRS (sigma ⊕ sigma) nu}
    {a a' b : Term (sigma ⊕ sigma) nu}
    (hpath : Relation.ReflTransGen (JoinStep R) a a') (h : Down R a' b) : Down R a b := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hstep _ ih =>
      rcases hstep with hroot | hbar
      · exact Down.rootComp hroot ih
      · obtain ⟨f, as, cs, ⟨d, rfl⟩, rfl, rfl, hall⟩ := hbar
        exact Down.barComp hall ih

/-- **Joinability characterization.** `Down R t u` holds exactly when `t` and `u` reach,
by root contractions and destructor argument replacements, two terms that are equal or
related by the constructor tilde of `Down`. -/
theorem down_iff_join {R : TRS (sigma ⊕ sigma) nu} {t u : Term (sigma ⊕ sigma) nu} :
    Down R t u ↔ ∃ t' u', Relation.ReflTransGen (JoinStep R) t t' ∧
      Relation.ReflTransGen (JoinStep R) u u' ∧ (t' = u' ∨ hatRel (Down R) t' u') := by
  constructor
  · intro h
    refine Down.induction (P := fun p q => ∃ p' q', Relation.ReflTransGen (JoinStep R) p p' ∧
      Relation.ReflTransGen (JoinStep R) q q' ∧ (p' = q' ∨ hatRel (Down R) p' q')) ?_ h
    intro p q hpq
    rcases hpq with rfl | hinv | ⟨c, hroot, hcb⟩ | ⟨d, as, cs, rfl, hall, hcb⟩ | hhat | hbar
    · exact ⟨_, _, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, Or.inl rfl⟩
    · obtain ⟨q', p', hq, hp, hend⟩ := hinv.2
      exact ⟨p', q', hp, hq, eq_or_hatRel_down_symm hend⟩
    · obtain ⟨c', q', hc, hq, hend⟩ := hcb.2
      exact ⟨c', q', Relation.ReflTransGen.head (Or.inl hroot) hc, hq, hend⟩
    · obtain ⟨c', q', hc, hq, hend⟩ := hcb.2
      refine ⟨c', q', Relation.ReflTransGen.head (Or.inr ?_) hc, hq, hend⟩
      exact ⟨.inr d, as, cs, ⟨d, rfl⟩, rfl, rfl, forall₂_mono (fun _ _ hx => hx.1) hall⟩
    · exact ⟨p, q, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl,
        Or.inr (tildeOn_mono (fun _ _ hx => hx.1) hhat)⟩
    · exact ⟨q, q, Relation.ReflTransGen.single (Or.inr (tildeOn_mono (fun _ _ hx => hx.1) hbar)),
        Relation.ReflTransGen.refl, Or.inl rfl⟩
  · rintro ⟨t', u', ht, hu, hend⟩
    exact Down.symm (Down.of_joinStep_reach hu
      (Down.symm (Down.of_joinStep_reach ht (Down.of_eq_or_hatRel hend))))

/-! ## The relation on a finite carrier -/

/-- `⊳` on a carrier `A`: both endpoints are members, and the replaced arguments are
related by the relativized invariant. -/
def JoinStepOn (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    CRel sigma nu :=
  fun a b => a ∈ A ∧ b ∈ A ∧ (rootStep R a b ∨ barRel (DownOn A R) a b)

/-- The carrier terminal relation is symmetric. -/
theorem eq_or_hatRel_downOn_symm {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : a = b ∨ hatRel (DownOn A R) a b) : b = a ∨ hatRel (DownOn A R) b a := by
  rcases h with rfl | hhat
  · exact Or.inl rfl
  · exact Or.inr (tildeOn_flip (tildeOn_mono (fun _ _ hxy => DownOn.symm hxy) hhat))

/-- The carrier terminal relation between members is part of `DownOn`. -/
theorem DownOn.of_eq_or_hatRel {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (h : a = b ∨ hatRel (DownOn A R) a b) : DownOn A R a b := by
  rcases h with rfl | hhat
  · exact DownOn.refl ha
  · obtain ⟨f, as, bs, ⟨c, rfl⟩, rfl, rfl, hall⟩ := hhat
    exact DownOn.hatCl ha hb hall

/-- `DownOn` absorbs a carrier `⊳` path at its left endpoint. -/
theorem DownOn.of_joinStepOn_reach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a a' b : Term (sigma ⊕ sigma) nu}
    (hpath : Relation.ReflTransGen (JoinStepOn A R) a a') (h : DownOn A R a' b) :
    DownOn A R a b := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hstep _ ih =>
      obtain ⟨hx, hy, hroot | hbar⟩ := hstep
      · exact DownOn.rootComp hx hy hroot ih
      · obtain ⟨f, as, cs, ⟨d, rfl⟩, rfl, rfl, hall⟩ := hbar
        exact DownOn.barComp hx hall ih

/-- **Joinability characterization on a carrier.** Every path node, every edge endpoint
and both terminal witnesses are members of `A`. -/
theorem downOn_iff_join {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {t u : Term (sigma ⊕ sigma) nu} :
    DownOn A R t u ↔ t ∈ A ∧ u ∈ A ∧ ∃ t' u', t' ∈ A ∧ u' ∈ A ∧
      Relation.ReflTransGen (JoinStepOn A R) t t' ∧
      Relation.ReflTransGen (JoinStepOn A R) u u' ∧
      (t' = u' ∨ hatRel (DownOn A R) t' u') := by
  constructor
  · intro h
    refine DownOn.induction (P := fun p q => p ∈ A ∧ q ∈ A ∧ ∃ p' q', p' ∈ A ∧ q' ∈ A ∧
      Relation.ReflTransGen (JoinStepOn A R) p p' ∧
      Relation.ReflTransGen (JoinStepOn A R) q q' ∧
      (p' = q' ∨ hatRel (DownOn A R) p' q')) ?_ h
    intro p q hpq
    obtain ⟨hp, hq, hbody⟩ := hpq
    refine ⟨hp, hq, ?_⟩
    rcases hbody with rfl | hinv | ⟨c, hc, hroot, hcb⟩ |
        ⟨d, as, cs, rfl, hall, hmem, hcb⟩ | hhat | hbar
    · exact ⟨_, _, hp, hp, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, Or.inl rfl⟩
    · obtain ⟨-, -, q', p', hq', hp', hqq, hpp, hend⟩ := hinv.2
      exact ⟨p', q', hp', hq', hpp, hqq, eq_or_hatRel_downOn_symm hend⟩
    · obtain ⟨-, -, c', q', hc', hq', hcc, hqq, hend⟩ := hcb.2
      exact ⟨c', q', hc', hq', Relation.ReflTransGen.head ⟨hp, hc, Or.inl hroot⟩ hcc, hqq, hend⟩
    · obtain ⟨-, -, c', q', hc', hq', hcc, hqq, hend⟩ := hcb.2
      refine ⟨c', q', hc', hq', Relation.ReflTransGen.head ⟨hp, hmem, Or.inr ?_⟩ hcc, hqq, hend⟩
      exact ⟨.inr d, as, cs, ⟨d, rfl⟩, rfl, rfl, forall₂_mono (fun _ _ hx => hx.1) hall⟩
    · exact ⟨p, q, hp, hq, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl,
        Or.inr (tildeOn_mono (fun _ _ hx => hx.1) hhat)⟩
    · exact ⟨q, q, hq, hq,
        Relation.ReflTransGen.single ⟨hp, hq, Or.inr (tildeOn_mono (fun _ _ hx => hx.1) hbar)⟩,
        Relation.ReflTransGen.refl, Or.inl rfl⟩
  · rintro ⟨_, _, t', u', ht', hu', htt, huu, hend⟩
    exact DownOn.symm (DownOn.of_joinStepOn_reach huu
      (DownOn.symm (DownOn.of_joinStepOn_reach htt (DownOn.of_eq_or_hatRel ht' hu' hend))))

end OperatorKO7.Meta.UniqueNormalization
