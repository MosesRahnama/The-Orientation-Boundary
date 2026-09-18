import OperatorKO7.Meta.UniqueNormalization.Section7SimultaneousClosure

/-!
# Section 7: the critical-pair dichotomy for the constructor translation

Let `R` be non-omega-overlapping and meet the variable condition. Two root redexes `a`
and `c` of `constructorTranslation R` whose arguments are related by a
constructor-compatible seed `S` (`barRel S a c`) have contracta `b` and `d` of one of
three kinds:

1. collapsing: both steps use the translated rule of one source rule whose right-hand
   side is a variable `x`; the contracta are the instances `s x` and `t x`, and one
   argument position `i` of the left-hand side, in which `x` occurs, supplies
   `S (s x) (t x)` through its own `S`-related instances (`VariableWitness`);
2. non-collapsing: both steps use the translated rule of one source rule with an
   application right-hand side; the contracta are related by `barRel (DCT S)`, and every
   right-hand-side variable has an argument position that supplies its witness;
3. pattern rules: both steps use pattern rules with one head symbol, and the contracta
   are related by `hatRel S`.

Identifying the two rules uses the union-find certificate of Lemma 36, which needs an
ambient constructor-compatible equivalence `E` containing `S`. That input is the named
hypothesis `ArgumentChainComposition S E`. For a seed read off a chain of destructor
argument replacements it is the composition of the argument chains, which steps 3 and 4
of the plan in `klop-status-assessment.md` must supply.

Relation: `rootStep (constructorTranslation R)`, `barRel`, `hatRel`, `DCT`.
Closure: one root step on each side of one destructor tilde.
Strategy: root rewriting.
Trust: kernel checked; no external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-- The ambient input of the dichotomy: a symmetric, transitive, constructor-compatible
relation `E` that contains the seed `S`. -/
def ArgumentChainComposition (S E : CRel sigma nu) : Prop :=
  (∀ x y, E x y → E y x) ∧ (∀ x y z, E x y → E y z → E x z) ∧
    ConstructorCompatible E ∧ ∀ x y, S x y → E x y

/-- Equality supplies the ambient input for the equality seed, so the hypothesis is
satisfiable. -/
theorem argumentChainComposition_eq :
    ArgumentChainComposition ((· = ·) : CRel sigma nu) ((· = ·) : CRel sigma nu) :=
  ⟨fun _ _ h => h.symm, fun _ _ _ h₁ h₂ => h₁.trans h₂, constructorCompatible_equality,
    fun _ _ h => h⟩

/-- One argument pair of two instances of a destructor pattern, read off the destructor
tilde between the instances. -/
theorem argument_related_of_constructor_bar {E : CRel sigma nu} {F : sigma}
    {ps : List (Term (sigma ⊕ sigma) nu)} {s t : Subst (sigma ⊕ sigma) nu}
    (hbar : barRel E (Subst.apply s (.app (.inr F) ps)) (Subst.apply t (.app (.inr F) ps)))
    {p : Term (sigma ⊕ sigma) nu} (hp : p ∈ ps) :
    E (Subst.apply s p) (Subst.apply t p) := by
  obtain ⟨f, xs, ys, _, hleft, hright, hargs⟩ := hbar
  simp only [Subst.apply_app, Subst.applyList_eq_map, Term.app.injEq] at hleft hright
  obtain ⟨_, hxs⟩ := hleft
  obtain ⟨_, hys⟩ := hright
  rw [← hxs, ← hys] at hargs
  exact pointwise_of_forall₂ hargs p hp

/-- Variable `x` occurs in argument `i` of the pattern list `ps`; that argument's two
instances are `S`-related, and so are the two instances of `x`. -/
def VariableWitness (S : CRel sigma nu) (ps : List (Term (sigma ⊕ sigma) nu))
    (s t : Subst (sigma ⊕ sigma) nu) (x : nu) (i : Nat) : Prop :=
  ∃ p, ps[i]? = some p ∧ VarOccurs x p ∧ S (Subst.apply s p) (Subst.apply t p) ∧
    S (s x) (t x)

/-- Every variable of a destructor pattern over constructor arguments has a witness
position: Lemma 33 applied to the argument that contains it. -/
theorem exists_variableWitness_of_constructor_bar {S : CRel sigma nu}
    (hSCC : ConstructorCompatible S) {F : sigma} {ps : List (Term (sigma ⊕ sigma) nu)}
    (hps : ∀ p ∈ ps, ConOnly p) {s t : Subst (sigma ⊕ sigma) nu}
    (hbar : barRel S (Subst.apply s (.app (.inr F) ps)) (Subst.apply t (.app (.inr F) ps)))
    {x : nu} (hx : VarOccurs x (.app (.inr F) ps)) : ∃ i, VariableWitness S ps s t x i := by
  obtain ⟨p, hp, hxp⟩ := hx.app_inv
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  have hsp := argument_related_of_constructor_bar hbar hp
  exact ⟨i, p, hi, hxp, hsp, lemma33 hSCC p (hps p hp) hsp x hxp⟩

/-- The destructor labelling of an application right-hand side carries a destructor
tilde of `DCT E` between two instances whose variables are `E`-related. -/
theorem barRel_DCT_destructorLabel_app {E : CRel sigma nu} {s t : Subst (sigma ⊕ sigma) nu}
    (f : sigma) (args : List (Term sigma nu))
    (hvars : ∀ x, VarOccurs x (Term.app f args) → E (s x) (t x)) :
    barRel (DCT E) (Subst.apply s (destructorLabel (.app f args)))
      (Subst.apply t (destructorLabel (.app f args))) := by
  simp only [destructorLabel_app, Subst.apply_app, Subst.applyList_eq_map,
    Term.mapSymList_eq_map, List.map_map]
  exact ⟨.inr f, _, _, ⟨f, rfl⟩, rfl, rfl, forall₂_of_pointwise (fun q hq =>
    DCT.destructorLabel_instances q (fun x hx => hvars x (.arg hq hx)))⟩

/-- **Critical-pair dichotomy.** The contracta of two root redexes of the constructor
translation, whose arguments are related by a constructor-compatible seed, are collapsing
instances of one variable, a destructor tilde of `DCT S`, or a constructor tilde of `S`.
The collapsing and non-collapsing cases record the argument position that supplies each
variable's witness. -/
theorem translated_critical_pair_dichotomy
    {R : TRS sigma nu} (hno : NonOmegaOverlapping R) (hvar : TRS.RhsDetermined R)
    {S E : CRel sigma nu} (hchain : ArgumentChainComposition S E)
    (hSCC : ConstructorCompatible S)
    {a b c d : Term (sigma ⊕ sigma) nu}
    (hab : rootStep (constructorTranslation R) a b)
    (hac : barRel S a c) (hcd : rootStep (constructorTranslation R) c d) :
    (∃ r ∈ R, ∃ (F : sigma) (ps : List (Term (sigma ⊕ sigma) nu))
        (s t : Subst (sigma ⊕ sigma) nu) (x : nu) (i : Nat),
        (transRule r).lhs = .app (.inr F) ps ∧ r.rhs = .var x ∧
        a = Subst.apply s (transRule r).lhs ∧ c = Subst.apply t (transRule r).lhs ∧
        b = s x ∧ d = t x ∧ VariableWitness S ps s t x i) ∨
    (∃ r ∈ R, ∃ (F : sigma) (ps : List (Term (sigma ⊕ sigma) nu))
        (s t : Subst (sigma ⊕ sigma) nu),
        (transRule r).lhs = .app (.inr F) ps ∧ r.rhs.isApp = true ∧
        a = Subst.apply s (transRule r).lhs ∧ c = Subst.apply t (transRule r).lhs ∧
        b = Subst.apply s (transRule r).rhs ∧ d = Subst.apply t (transRule r).rhs ∧
        barRel (DCT S) b d ∧ ∀ x, VarOccurs x r.rhs → ∃ i, VariableWitness S ps s t x i) ∨
    (∃ n ∈ patternNodes R, ∃ m ∈ patternNodes R, ∃ s t : Subst (sigma ⊕ sigma) nu,
        a = Subst.apply s (patternRuleOf n).lhs ∧ c = Subst.apply t (patternRuleOf m).lhs ∧
        b = Subst.apply s (patternRuleOf n).rhs ∧ d = Subst.apply t (patternRuleOf m).rhs ∧
        hatRel S b d) := by
  obtain ⟨hsymm, htrans, hCC, hSE⟩ := hchain
  obtain ⟨r₁, hr₁, s, ha, hb⟩ := hab
  obtain ⟨r₂, hr₂, t, hc, hd⟩ := hcd
  rw [ha, hc] at hac
  have hou := omegaUnifiable_of_constructor_bar
    (constructorRules_constructorTranslation R) hsymm htrans hCC hr₁ hr₂
      (tildeOn_mono hSE hac)
  rcases mem_constructorTranslation hr₁ with ⟨r, hr, rfl⟩ | ⟨n, hn, rfl⟩
  · rcases mem_constructorTranslation hr₂ with ⟨r', hr', rfl⟩ | ⟨m, hm, rfl⟩
    · have hOU : OmegaUnifiable r.lhs r'.lhs := omegaUnifiable_of_destructorPattern hou
      obtain ⟨heq, _⟩ := hno r hr r' hr' r.lhs (Subterm.refl _) r.lhs_isApp hOU
      subst r'
      obtain ⟨F, ps, hl, hps⟩ :=
        constructorRules_constructorTranslation R (transRule r) (transRule_mem hr)
      have hbar : barRel S (Subst.apply s (.app (.inr F) ps))
          (Subst.apply t (.app (.inr F) ps)) := by
        simpa only [hl] using hac
      have hwit : ∀ x, VarOccurs x r.rhs → ∃ i, VariableWitness S ps s t x i := by
        intro x hx
        have hxl : VarOccurs x (transRule r).lhs :=
          transRule_occurs (hvar r hr) (hx.mapSym Sum.inr)
        rw [hl] at hxl
        exact exists_variableWitness_of_constructor_bar hSCC hps hbar hxl
      cases hrhs : r.rhs with
      | var x =>
          obtain ⟨i, hi⟩ := hwit x (by rw [hrhs]; exact VarOccurs.here)
          refine Or.inl ⟨r, hr, F, ps, s, t, x, i, hl, hrhs, ha, hc, ?_, ?_, hi⟩
          · rw [hb]
            show Subst.apply s (destructorLabel r.rhs) = s x
            rw [hrhs]
            rfl
          · rw [hd]
            show Subst.apply t (destructorLabel r.rhs) = t x
            rw [hrhs]
            rfl
      | app f args =>
          have hvars : ∀ y, VarOccurs y (Term.app f args) → S (s y) (t y) := by
            intro y hy
            obtain ⟨_, _, _, _, _, hsy⟩ := hwit y (by rw [hrhs]; exact hy)
            exact hsy
          refine Or.inr (Or.inl ⟨r, hr, F, ps, s, t, hl, by rw [hrhs]; rfl, ha, hc, hb, hd,
            ?_, hwit⟩)
          rw [hb, hd]
          show barRel (DCT S) (Subst.apply s (destructorLabel r.rhs))
            (Subst.apply t (destructorLabel r.rhs))
          rw [hrhs]
          exact barRel_DCT_destructorLabel_app f args hvars
    · exact (prop22_rule_pattern hno hr hm hou).elim
  · rcases mem_constructorTranslation hr₂ with ⟨r, hr, rfl⟩ | ⟨m, hm, rfl⟩
    · exact (prop22_rule_pattern hno hr hn hou.symm).elim
    · refine Or.inr (Or.inr ⟨n, hn, m, hm, s, t, ha, hc, hb, hd, ?_⟩)
      rw [hb, hd]
      exact patternRule_instances_hat n m hac

end OperatorKO7.Meta.UniqueNormalization
