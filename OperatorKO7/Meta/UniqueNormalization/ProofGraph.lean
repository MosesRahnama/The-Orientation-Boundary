import OperatorKO7.Meta.UniqueNormalization.Forest
import Mathlib.Data.Finset.Card

/-!
# Proof graphs and Lemma 52

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 6. Source: Kahrs and Smith, FSCD 2016,
Definitions 46 and 51 and Lemma 52, transcribed in `Roadmaps\klop\definitions.md`
at D14 with amendment A4.

## Fidelity block (frozen `definitions.md`, D14, Definition 46)

> "A proof graph rho = (->_rho, =_rho) is given by a binary relation ->_rho on A
> with the following properties: 1. (->_rho union <-_rho)* = =_rho subset of
> down_A; 2. ->_rho is deterministic, i.e. <-_rho . ->_rho subset of id_A;
> 3. ->_rho is terminating; 4. ->_rho subset of ->_eps^A union down-bar_A union
> hat(=_rho)"

Amendment A4: the middle term of condition 4 carries the Sigma_d tilde. That is
what makes every edge out of a constructor-topped node a constructor-tilde edge,
which Lemma 47 and Lemma 52 both use.

`PGraph` carries condition 2 by construction, since a deterministic relation is a
partial function. Conditions 1, 3 and 4 are the fields `sub`, `term` and `grey`.

## Fidelity block (frozen `definitions.md`, D14, Definition 51 and Lemma 52)

> "Given a proof graph rho the grey edge relation on nodes is defined as
> rho-grey = ->_eps^A union down-bar_A union hat(=_rho)."

> "Let rho be a proof graph. Let ->_beta subset of rho-grey such that ->_beta is
> deterministic and terminating, and let =_beta be the equivalence closure of
> ->_beta. Then =_beta subset of down_A."

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Argumentwise transitivity, and the constructor tilde's -/

theorem forall₂_trans {alpha : Type u} {r : alpha → alpha → Prop}
    (htr : ∀ x y z, r x y → r y z → r x z) :
    ∀ {l₁ l₂ l₃ : List alpha}, List.Forall₂ r l₁ l₂ → List.Forall₂ r l₂ l₃ →
      List.Forall₂ r l₁ l₃ := by
  intro l₁ l₂ l₃ h₁
  induction h₁ generalizing l₃ with
  | nil => intro h₂; cases h₂; exact List.Forall₂.nil
  | cons hab _ ih =>
      intro h₂
      cases h₂ with
      | cons hbc htail => exact List.Forall₂.cons (htr _ _ _ hab hbc) (ih htail)

/-- The frozen-variable constructor tilde of a transitive relation is
transitive. -/
theorem hatEq.trans {E : CRel sigma nu} (htr : ∀ x y z, E x y → E y z → E x z)
    {a b c : Term (sigma ⊕ sigma) nu} (h₁ : hatEq E a b) (h₂ : hatEq E b c) :
    hatEq E a c := by
  rcases h₁ with ⟨x, rfl, rfl⟩ | ⟨f, as, bs, ⟨cf, rfl⟩, rfl, hb, hall⟩
  · exact h₂
  · rcases h₂ with ⟨y, hby, -⟩ | ⟨f', bs', cs, ⟨cf', rfl⟩, hb', hc, hall'⟩
    · exact absurd (hb.symm.trans hby) (by simp)
    · have heq : Term.app (Sum.inl cf) bs = Term.app (Sum.inl cf') bs' := hb.symm.trans hb'
      simp only [Term.app.injEq] at heq
      obtain ⟨hcc, hbs⟩ := heq
      have hcc' : cf = cf' := by simpa using hcc
      subst hcc'
      subst hbs
      exact Or.inr ⟨.inl cf, as, cs, ⟨cf, rfl⟩, rfl, hc, forall₂_trans htr hall hall'⟩

/-- Both endpoints of a frozen-variable constructor tilde are
constructor-topped. -/
theorem ConTopped.of_hatEq_right {E : CRel sigma nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : hatEq E a b) : ConTopped b := by
  rcases h with ⟨x, -, rfl⟩ | ⟨f, as, bs, ⟨c, rfl⟩, -, rfl, -⟩
  · exact ConTopped.var x
  · exact ConTopped.app c bs

/-! ## Chains with a step count -/

/-- The parent chain with its length, so Lemma 52 can induct on it. -/
inductive ReachN (g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)) :
    Nat → Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop
  | refl (a : Term (sigma ⊕ sigma) nu) : ReachN g 0 a a
  | head {n : Nat} {a b c : Term (sigma ⊕ sigma) nu} :
      g a = some b → ReachN g n b c → ReachN g (n + 1) a c

theorem ReachN.toReach {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {n : Nat} {a b : Term (sigma ⊕ sigma) nu} (h : ReachN g n a b) : Reach g a b := by
  induction h with
  | refl a => exact Reach.refl a
  | head hedge _ ih => exact Reach.head hedge ih

theorem Reach.toReachN {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} (h : Reach g a b) : ∃ n, ReachN g n a b := by
  induction h with
  | refl a => exact ⟨0, ReachN.refl a⟩
  | head hedge _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, ReachN.head hedge hn⟩

/-! ## Grey edges and proof graphs -/

/-- **Definition 51 with amendment A4.** A grey edge is a root contraction, a
destructor tilde of the invariant, or a constructor tilde of the graph's own
equivalence. -/
def Grey (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (E : CRel sigma nu) : CRel sigma nu :=
  fun a b => rootStep R a b ∨ barRel (DownOn A R) a b ∨ hatEq E a b

/-- **Definition 46.** Determinism is built in: the edge relation is a partial
function. -/
structure PGraph (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) where
  /-- The parent of a node, when it has one. -/
  par : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)
  /-- Edges stay inside the coalgebra. -/
  mem_edge : ∀ {a b : Term (sigma ⊕ sigma) nu}, par a = some b → a ∈ A ∧ b ∈ A
  /-- Condition 3. -/
  term : Terminating par
  /-- Condition 1. -/
  sub : ∀ {a b : Term (sigma ⊕ sigma) nu}, EqvOn A par a b → DownOn A R a b
  /-- Condition 4, with amendment A4. -/
  grey : ∀ {a b : Term (sigma ⊕ sigma) nu}, par a = some b → Grey A R (EqvOn A par) a b

/-! ## Valley form equals the source's equivalence closure

`EqvOn` was introduced in `Forest.lean` in valley form because that is the form
consumed by Lemma 52. Definition 46 of the source instead defines the graph
equality as the equivalence closure of the parent edges. For an actual `PGraph`
the two presentations are exactly equal: `mem_edge` keeps every edge inside
`A`, and determinism is already built into the parent function. No termination
hypothesis is needed for this representation theorem. -/

/-- Membership in the coalgebra is invariant under the equivalence closure of
parent edges of a proof graph. -/
theorem PGraph.eqvGen_up_mem_iff {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} (h : Relation.EqvGen (Up rho.par) a b) :
    a ∈ A ↔ b ∈ A := by
  induction h with
  | rel x y hxy =>
      have hm := rho.mem_edge hxy
      exact ⟨fun _ => hm.2, fun _ => hm.1⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Every directed parent chain lies in the equivalence closure of the parent
edge relation. -/
theorem PGraph.reach_to_eqvGen_up {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} (h : Reach rho.par a b) :
    Relation.EqvGen (Up rho.par) a b := by
  induction h with
  | refl a => exact Relation.EqvGen.refl a
  | @head a b c hab _ ih =>
      exact Relation.EqvGen.trans a b c (Relation.EqvGen.rel a b hab) ih

/-- **Definition-46 representation theorem.** On a proof graph, the valley
relation `EqvOn` is exactly the equivalence closure of the parent edge relation,
restricted to members of the coalgebra. This discharges the representation gap
between the implementation used by Lemma 52 and the source definition. -/
theorem PGraph.eqvOn_iff_eqvGen_up {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} :
    EqvOn A rho.par a b ↔
      a ∈ A ∧ b ∈ A ∧ Relation.EqvGen (Up rho.par) a b := by
  constructor
  · rintro ⟨ha, hb, s, has, hbs⟩
    exact ⟨ha, hb, Relation.EqvGen.trans a s b
      (rho.reach_to_eqvGen_up has)
      (Relation.EqvGen.symm b s (rho.reach_to_eqvGen_up hbs))⟩
  · rintro ⟨ha, hb, h⟩
    induction h with
    | rel x y hxy =>
        exact EqvOn.of_reach (rho.mem_edge hxy).1 (rho.mem_edge hxy).2
          (Reach.head hxy (Reach.refl y))
    | refl x => exact EqvOn.refl ha
    | symm x y _ ih => exact EqvOn.symm (ih hb ha)
    | trans x y z hxy hyz ihxy ihyz =>
        have hy : y ∈ A := (rho.eqvGen_up_mem_iff hxy).1 ha
        exact EqvOn.trans (ihxy ha hy) (ihyz hy hb)

/-- A node with no parent is a normal form of the graph. -/
def PGraph.NF {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a : Term (sigma ⊕ sigma) nu) : Prop :=
  rho.par a = none

/-! ## Constructor-topped nodes carry only constructor-tilde edges

This is Lemma 47's engine, and amendment A4 is what supplies it: a root
contraction and a destructor tilde both have destructor-headed sources. -/

/-- Out of a constructor-topped node, every grey edge is a constructor tilde. -/
theorem hatEq_of_grey_of_conTopped {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) {E : CRel sigma nu}
    {a b : Term (sigma ⊕ sigma) nu} (hca : ConTopped a) (h : Grey A R E a b) :
    hatEq E a b := by
  rcases h with hroot | hbar | hhat
  · obtain ⟨d, args, rfl⟩ := rootStep_source_destructor hR hroot
    exact absurd hca (not_conTopped_destructor args)
  · obtain ⟨f, as, bs, ⟨d, rfl⟩, rfl, -, -⟩ := hbar
    exact absurd hca (not_conTopped_destructor as)
  · exact hhat

/-- A chain out of a constructor-topped node stays constructor-topped. -/
theorem conTopped_of_reach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) {E : CRel sigma nu}
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hg : ∀ {x y : Term (sigma ⊕ sigma) nu}, g x = some y → Grey A R E x y)
    {a s : Term (sigma ⊕ sigma) nu} (h : Reach g a s) : ConTopped a → ConTopped s := by
  induction h with
  | refl a => exact id
  | head hedge _ ih =>
      intro hca
      exact ih (ConTopped.of_hatEq_right (hatEq_of_grey_of_conTopped hR hca (hg hedge)))

/-! ## Lemma 47: constructor compatibility of the represented equivalence -/

/-- The constructor tilde of a symmetric relation is symmetric. This belongs at
proof-graph level because Lemma 47 needs it before Lemma 52. -/
theorem hatEq.symm {E : CRel sigma nu} (hsy : ∀ x y, E x y → E y x)
    {a b : Term (sigma ⊕ sigma) nu} (h : hatEq E a b) : hatEq E b a := by
  rcases h with ⟨x, rfl, rfl⟩ | ⟨f, as, bs, hP, rfl, rfl, hall⟩
  · exact Or.inl ⟨x, rfl, rfl⟩
  · exact Or.inr ⟨f, bs, as, hP, rfl, rfl, forall₂_swap hsy hall⟩

/-- Along a proof-graph parent chain, a constructor-topped source remains related
to the endpoint by the constructor tilde of the graph equivalence. -/
theorem PGraph.hatEq_of_reach {A : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) {a s : Term (sigma ⊕ sigma) nu} (h : Reach rho.par a s)
    (haA : a ∈ A) (hca : ConTopped a) : hatEq (EqvOn A rho.par) a s := by
  induction h with
  | refl a =>
      rcases hca with ⟨x, rfl⟩ | ⟨f, args, rfl⟩
      · exact Or.inl ⟨x, rfl, rfl⟩
      · exact Or.inr ⟨.inl f, args, args, ⟨f, rfl⟩, rfl, rfl,
          forall₂_self_of (fun z hz => EqvOn.refl (Coalgebra.arg hA haA hz))⟩
  | @head a b s hab hbs ih =>
      have habHat := hatEq_of_grey_of_conTopped hR hca (rho.grey hab)
      have hcb : ConTopped b := ConTopped.of_hatEq_right habHat
      have hbA : b ∈ A := (rho.mem_edge hab).2
      have hbsHat := ih hbA hcb
      exact hatEq.trans (E := EqvOn A rho.par)
        (fun _ _ _ h1 h2 => EqvOn.trans h1 h2) habHat hbsHat

/-- **Lemma 47.** The equivalence represented by a proof graph is
constructor-compatible on its coalgebra. -/
theorem PGraph.constructorCompatible {A : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} (hca : ConTopped a) (hcb : ConTopped b)
    (h : EqvOn A rho.par a b) : hatEq (EqvOn A rho.par) a b := by
  obtain ⟨haA, hbA, s, has, hbs⟩ := h
  have ha := rho.hatEq_of_reach hA hR has haA hca
  have hb := rho.hatEq_of_reach hA hR hbs hbA hcb
  exact hatEq.trans (E := EqvOn A rho.par)
    (fun _ _ _ h1 h2 => EqvOn.trans h1 h2) ha
    (hatEq.symm (E := EqvOn A rho.par) (fun _ _ hxy => EqvOn.symm hxy) hb)

/-! ## Monotonicity under graph extension -/

/-- Parent reachability is monotone when every old edge is retained. -/
theorem Reach.mono {g h : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hedge : ∀ ⦃a b⦄, g a = some b → h a = some b)
    {a b : Term (sigma ⊕ sigma) nu} (hr : Reach g a b) : Reach h a b := by
  induction hr with
  | refl a => exact Reach.refl a
  | head hab _ ih => exact Reach.head (hedge hab) ih

/-- The forest equivalence is monotone under retention of all parent edges. -/
theorem EqvOn.mono {A : List (Term (sigma ⊕ sigma) nu)}
    {g h : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hedge : ∀ ⦃a b⦄, g a = some b → h a = some b)
    {a b : Term (sigma ⊕ sigma) nu} (heq : EqvOn A g a b) : EqvOn A h a b := by
  obtain ⟨ha, hb, s, has, hbs⟩ := heq
  exact ⟨ha, hb, s, has.mono hedge, hbs.mono hedge⟩

/-- Grey-edge admissibility is monotone in the represented equivalence. -/
theorem Grey.mono {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {E E' : CRel sigma nu} (hE : ∀ a b, E a b → E' a b)
    {a b : Term (sigma ⊕ sigma) nu} (h : Grey A R E a b) : Grey A R E' a b := by
  rcases h with hroot | hbar | hhat
  · exact Or.inl hroot
  · exact Or.inr (Or.inl hbar)
  · exact Or.inr (Or.inr (hatEq.mono hE hhat))

/-! ## Definitions 48, 49, 54 and Proposition 55 -/

/-- Definition 49. `beta` extends `alpha` when every parent edge of `alpha`
remains a parent edge of `beta`. -/
def PGraph.Extends {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (alpha beta : PGraph A R) : Prop :=
  ∀ ⦃a b : Term (sigma ⊕ sigma) nu⦄, alpha.par a = some b → beta.par a = some b

namespace PGraph.Extends

/-- Extension is reflexive. -/
theorem refl {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) : rho.Extends rho := by
  intro a b h
  exact h

/-- Extension is transitive. -/
theorem trans {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {alpha beta gamma : PGraph A R} (hab : alpha.Extends beta) (hbg : beta.Extends gamma) :
    alpha.Extends gamma := by
  intro a b h
  exact hbg (hab h)

end PGraph.Extends

/-- Definition 54. A proof graph is complete when it has no proper extension.
Equality is extensional at the edge relation, which is the data relevant to the
source definition. -/
def PGraph.Complete {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) : Prop :=
  ∀ beta : PGraph A R, rho.Extends beta → beta.Extends rho

/-- Definition 48. A normal form of a proof graph is a node with no parent edge. -/
theorem PGraph.nf_iff {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    (a : Term (sigma ⊕ sigma) nu) : rho.NF a ↔ rho.par a = none :=
  Iff.rfl

/-- The finite set of graph normal forms inside the strongly finite coalgebra. -/
noncomputable def PGraph.roots {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) :
    Finset (Term (sigma ⊕ sigma) nu) := by
  classical
  exact A.toFinset.filter (fun a => rho.par a = none)

/-- A proper extension strictly decreases the finite set of graph normal forms.
This is the finite measure behind Proposition 55. -/
theorem PGraph.roots_ssubset_of_proper {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {alpha beta : PGraph A R}
    (hab : alpha.Extends beta) (hproper : ¬ beta.Extends alpha) :
    beta.roots ⊂ alpha.roots := by
  classical
  have hsub : beta.roots ⊆ alpha.roots := by
    intro a ha
    simp only [PGraph.roots, Finset.mem_filter, List.mem_toFinset] at ha ⊢
    refine ⟨ha.1, ?_⟩
    cases hpa : alpha.par a with
    | none => rfl
    | some b =>
        have hpb := hab hpa
        rw [ha.2] at hpb
        contradiction
  refine ⟨hsub, ?_⟩
  intro hrev
  apply hproper
  intro a b hbeta
  have haA : a ∈ A := (beta.mem_edge hbeta).1
  cases halpha : alpha.par a with
  | none =>
      have haRootAlpha : a ∈ alpha.roots := by
        simp [PGraph.roots, haA, halpha]
      have haRootBeta := hrev haRootAlpha
      simp [PGraph.roots, hbeta] at haRootBeta
  | some c =>
      have hbetac := hab halpha
      have hcb : c = b := Option.some.inj (hbetac.symm.trans hbeta)
      exact congrArg some hcb

/-- **Proposition 55.** Every proof graph over a strongly finite coalgebra has a
complete extension. Each proper extension consumes at least one graph normal
form, so strong induction on the finite root count terminates the construction. -/
theorem PGraph.exists_complete_extension {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) :
    ∃ beta : PGraph A R, rho.Extends beta ∧ beta.Complete := by
  classical
  have main : ∀ n : Nat, ∀ alpha : PGraph A R, alpha.roots.card = n →
      ∃ beta : PGraph A R, alpha.Extends beta ∧ beta.Complete := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro alpha hcount
        by_cases hcomplete : alpha.Complete
        · exact ⟨alpha, PGraph.Extends.refl alpha, hcomplete⟩
        · have hnext : ∃ beta : PGraph A R,
              alpha.Extends beta ∧ ¬ beta.Extends alpha := by
            by_contra hnone
            apply hcomplete
            intro beta hab
            by_contra hba
            exact hnone ⟨beta, hab, hba⟩
          obtain ⟨beta, hab, hba⟩ := hnext
          have hlt : beta.roots.card < n := by
            rw [← hcount]
            exact Finset.card_lt_card (PGraph.roots_ssubset_of_proper hab hba)
          obtain ⟨gamma, hbg, hgc⟩ := ih beta.roots.card hlt beta rfl
          exact ⟨gamma, PGraph.Extends.trans hab hbg, hgc⟩
  exact main rho.roots.card rho rfl

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.Grey
#check @OperatorKO7.Meta.UniqueNormalization.PGraph
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.eqvGen_up_mem_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.reach_to_eqvGen_up
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.eqvOn_iff_eqvGen_up
#check @OperatorKO7.Meta.UniqueNormalization.hatEq.symm
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.hatEq_of_reach
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.constructorCompatible
#check @OperatorKO7.Meta.UniqueNormalization.Reach.mono
#check @OperatorKO7.Meta.UniqueNormalization.EqvOn.mono
#check @OperatorKO7.Meta.UniqueNormalization.Grey.mono
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.Extends
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.Extends.refl
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.Extends.trans
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.Complete
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.nf_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.roots
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.roots_ssubset_of_proper
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.exists_complete_extension

#print axioms OperatorKO7.Meta.UniqueNormalization.hatEq.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.eqvGen_up_mem_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.reach_to_eqvGen_up
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.eqvOn_iff_eqvGen_up
#print axioms OperatorKO7.Meta.UniqueNormalization.hatEq_of_grey_of_conTopped
#print axioms OperatorKO7.Meta.UniqueNormalization.conTopped_of_reach
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.toReachN
#print axioms OperatorKO7.Meta.UniqueNormalization.hatEq.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.hatEq_of_reach
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.constructorCompatible
#print axioms OperatorKO7.Meta.UniqueNormalization.Reach.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.EqvOn.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.Grey.mono
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.Extends.refl
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.Extends.trans
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.nf_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.roots_ssubset_of_proper
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.exists_complete_extension
