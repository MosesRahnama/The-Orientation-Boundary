import Init

/-!
# The three-term counterexample to Kahrs and Smith, Lemma 64

All definitions are restricted to the carrier {c, d(c), d(d(c))}.
Source correspondence and the proof graph are in README.md.
Only Lean's bundled core is imported. No general UN result is assumed.
-/

set_option autoImplicit false

namespace Lemma64

/-- The signature has a nullary constructor, a unary destructor, and frozen variables. -/
inductive Term where
  | c : Term
  | d : Term → Term
  | var : Nat → Term

/-- Exactly the three members of the paper's coalgebra. -/
inductive Node where
  | t0 | t1 | t2

open Node

/-- Interpretation of the finite carrier in the term syntax. -/
def term : Node → Term
  | t0 => .c
  | t1 => .d .c
  | t2 => .d (.d .c)

/-- Relations in this package have endpoints in the carrier by their type. -/
abbrev Rel := Node → Node → Prop

/-- The restricted root steps of the sole rule d(x) -> x. -/
def Root (a b : Node) : Prop :=
  (a = t1 ∧ b = t0) ∨ (a = t2 ∧ b = t1)

private theorem node_exists (P : Node → Prop) :
    (∃ a, P a) ↔ P t0 ∨ P t1 ∨ P t2 := by
  constructor
  · intro ⟨a, h⟩
    cases a with
    | t0 => exact Or.inl h
    | t1 => exact Or.inr (Or.inl h)
    | t2 => exact Or.inr (Or.inr h)
  · intro h
    rcases h with h | h | h
    · exact ⟨t0, h⟩
    · exact ⟨t1, h⟩
    · exact ⟨t2, h⟩

/-- The interpretation is injective and closed under immediate subterms;
root steps have the promised rule semantics, and no carrier node is a variable. -/
theorem carrier_model :
    (∀ a b, term a = term b → a = b) ∧
    (∀ a u, term a = Term.d u → ∃ b, term b = u) ∧
    (∀ a b, Root a b ↔ term a = Term.d (term b)) ∧
    (∀ a n, term a ≠ Term.var n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    cases a <;> cases b <;> simp_all [term]
  · intro a u h
    cases a <;> simp_all [term, node_exists]
  · intro a b
    cases a <;> cases b <;> simp [Root, term]
  · intro a n
    cases a <;> simp [term]

private theorem root_functional {a b c : Node}
    (h : Root a b) (k : Root a c) : b = c := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Root]

/-- Destructor lifting: matching destructor heads, with E-related arguments. -/
def Bar (E : Rel) (a b : Node) : Prop :=
  ∃ u v, Root a u ∧ Root b v ∧ E u v

/-- Constructor lifting: c is the carrier's only constructor-topped node. -/
def Hat (_E : Rel) (a b : Node) : Prop := a = t0 ∧ b = t0

/-- Definition 24: closure under both parts of the signature lift. -/
def SignatureClosed (E : Rel) : Prop :=
  ∀ a b, Bar E a b ∨ Hat E a b → E a b

/-- Definition 25: the least signature-closed extension, without equivalence closure. -/
inductive CT (E : Rel) : Rel where
  | base {a b : Node} : E a b → CT E a b
  | constructor : CT E t0 t0
  | destructor {a b u v : Node} :
      Root a u → Root b v → CT E u v → CT E a b

/-- The inductive CT is closed and is contained in every eligible extension. -/
theorem ct_spec (E : Rel) :
    SignatureClosed (CT E) ∧
    ∀ S : Rel, (∀ a b, E a b → S a b) → SignatureClosed S →
      ∀ a b, CT E a b → S a b := by
  constructor
  · intro a b h
    rcases h with ⟨u, v, ha, hb, huv⟩ | ⟨rfl, rfl⟩
    · exact CT.destructor ha hb huv
    · exact CT.constructor
  · intro S hbase hclosed a b h
    induction h with
    | base h => exact hbase _ _ h
    | constructor => exact hclosed _ _ (Or.inr ⟨rfl, rfl⟩)
    | destructor ha hb _ ih => exact hclosed _ _ (Or.inl ⟨_, _, ha, hb, ih⟩)

/-- Definitions 38 and 40 on this carrier. There is no transitivity constructor.
The nullary-constructor clause is already supplied by reflexivity. -/
inductive Down : Rel where
  | refl (a : Node) : Down a a
  | symm {a b : Node} : Down a b → Down b a
  | root {a m b : Node} : Root a m → Down m b → Down a b
  | destructor {a m b u v : Node} :
      Root a u → Root m v → Down u v → Down m b → Down a b

/-- The exact closure operator in Definition 40, with path-order composition. -/
def DownStep (X : Rel) (a b : Node) : Prop :=
  X b a ∨ (∃ m, (Root a m ∨ Bar X a m) ∧ X m b) ∨
  a = b ∨ Hat X a b ∨ X a b

/-- Down is a fixed point of the printed operator and is its least pre-fixed point. -/
theorem down_least_fixed_point :
    (∀ a b, DownStep Down a b ↔ Down a b) ∧
    ∀ X : Rel, (∀ a b, DownStep X a b → X a b) →
      ∀ a b, Down a b → X a b := by
  constructor
  · intro a b
    constructor
    · intro h
      rcases h with h | ⟨m, hm, hmb⟩ | rfl | ⟨rfl, rfl⟩ | h
      · exact Down.symm h
      · rcases hm with hm | ⟨u, v, ha, hv, huv⟩
        · exact Down.root hm hmb
        · exact Down.destructor ha hv huv hmb
      · exact Down.refl _
      · exact Down.refl _
      · exact h
    · intro h
      exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · intro X hclosed a b h
    induction h with
    | refl a => exact hclosed a a (Or.inr (Or.inr (Or.inl rfl)))
    | symm _ ih => exact hclosed _ _ (Or.inl ih)
    | root h _ ih => exact hclosed _ _ (Or.inr (Or.inl ⟨_, Or.inl h, ih⟩))
    | destructor ha hm _ _ ihuv ihmb =>
        exact hclosed _ _ (Or.inr (Or.inl ⟨_, Or.inr ⟨_, _, ha, hm, ihuv⟩, ihmb⟩))

private theorem down10 : Down t1 t0 :=
  Down.root (Or.inl ⟨rfl, rfl⟩) (Down.refl t0)

private theorem down21 : Down t2 t1 :=
  Down.root (Or.inr ⟨rfl, rfl⟩) (Down.refl t1)

private theorem down20 : Down t2 t0 :=
  Down.root (Or.inr ⟨rfl, rfl⟩) down10

/-- All nine pairs have derivations using only the printed closure clauses. -/
theorem down_universal (a b : Node) : Down a b := by
  cases a <;> cases b
  · exact Down.refl _
  · exact Down.symm down10
  · exact Down.symm down20
  · exact down10
  · exact Down.refl _
  · exact Down.symm down21
  · exact down20
  · exact down21
  · exact Down.refl _

/-- Consistency forbids identifying distinct frozen variables present in the carrier. -/
def Consistent (S : Rel) : Prop :=
  ∀ a b m n, term a = Term.var m → term b = Term.var n → S a b → m = n

/-- Definition 27: Hat(id) followed by E followed by Hat(id) is contained in Hat(E). -/
def ConstructorCompatible (E : Rel) : Prop :=
  ∀ a b c d, Hat Eq a b → E b c → Hat Eq c d → Hat E a d

/-- Definition 30 with the barred middle relation and the full equivalence quantifier. -/
def ConsistencyInvariant (S : Rel) : Prop :=
  Consistent S ∧ SignatureClosed S ∧
  ∀ E : Rel, (∀ a b, E a b → S a b) → Equivalence E →
    ConstructorCompatible E → ∀ u a b v,
      Root a u → Bar E a b → Root b v → CT E u v

/-- For the rule d(x) -> x, the fork premise exposes E-related contracta directly. -/
theorem semantic_fork (E : Rel) (u a b v : Node)
    (ha : Root a u) (hab : Bar E a b) (hb : Root b v) : CT E u v := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hab
  have hux := root_functional ha hx
  have hvy := root_functional hb hy
  subst x
  subst y
  exact CT.base hxy

/-- The invariant hypothesis of Lemma 64 holds, including its semantic fork. -/
theorem down_consistencyInvariant : ConsistencyInvariant Down := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b m n ha _ _
    exact False.elim (carrier_model.2.2.2 a m ha)
  · intro a b _
    exact down_universal a b
  · intro E _ _ _ u a b v ha hab hb
    exact semantic_fork E u a b v ha hab hb

/-- Reflexive-transitive closure with explicit finite path constructors. -/
inductive Star (R : Rel) : Rel where
  | refl (a : Node) : Star R a a
  | step {a b c : Node} : R a b → Star R b c → Star R a c

/-- Definition 46(1): equivalence generated by parent edges and their converses. -/
def Eqv (rho : Rel) : Rel := Star (fun a b => rho a b ∨ rho b a)

/-- Definition 51: the constructor contribution depends on this graph's equivalence. -/
def Grey (rho : Rel) (a b : Node) : Prop :=
  Root a b ∨ Bar Down a b ∨ Hat (Eqv rho) a b

/-- Definition 46. Well-foundedness uses the converse of the forward parent relation. -/
structure ProofGraph (rho : Rel) : Prop where
  deterministic : ∀ a b c, rho a b → rho a c → b = c
  terminating : WellFounded (fun b a => rho a b)
  sound : ∀ a b, Eqv rho a b → Down a b
  admissible : ∀ a b, rho a b → Grey rho a b

/-- Definitions 49 and 54: every valid edge-preserving extension is equal pointwise. -/
def Complete (rho : Rel) : Prop :=
  ∀ beta : Rel, ProofGraph beta → (∀ a b, rho a b → beta a b) →
    ∀ a b, beta a b ↔ rho a b

/-- Definition 57: destructor fibers use the closure of Bar Down, not of Down. -/
def Fiber : Rel := Star (Bar Down)

/-- Definition 58 in node-indexed form, with explicit constancy on equal fibers. -/
structure Target (q : Node → Node) : Prop where
  member : ∀ a, Fiber a (q a)
  constant : ∀ a b, Fiber a b → q a = q b
  redex : ∀ a, (∃ u v, Fiber a u ∧ Root u v) → ∃ v, Root (q a) v

/-- Definition 59, including the underlying proof graph and both targeting clauses. -/
structure Targeted (rho : Rel) (q : Node → Node) : Prop where
  graph : ProofGraph rho
  target : Target q
  guided_or_nf : ∀ a,
    Star (fun x y => Bar Down x y ∧ rho x y) a (q a) ∨ ∀ b, ¬ rho a b
  exits : ∀ a b, rho (q a) b → ¬ Fiber a b

/-- Definition 63: exactly the equations in Down are represented. -/
def Universal (rho : Rel) : Prop := ∀ a b, Eqv rho a b ↔ Down a b

/-- The counterexample's only parent edge. -/
def trap (a b : Node) : Prop := a = t1 ∧ b = t2

/-- The paper's choice of the higher destructor node as target. -/
def target : Node → Node
  | t0 => t0
  | t1 => t2
  | t2 => t2

/-- The partition {t0}, {t1,t2}, written without a quotient representation. -/
def SameBlock (a b : Node) : Prop := (a = t0 ↔ b = t0)

private theorem star_preserves_block (R : Rel)
    (hR : ∀ a b, R a b → SameBlock a b) {a b : Node}
    (h : Star R a b) : SameBlock a b := by
  induction h with
  | refl a => exact Iff.rfl
  | step hab _ ih => exact Iff.trans (hR _ _ hab) ih

/-- The destructor lift has exactly four pairs, all between destructor nodes. -/
theorem bar_down_exact (a b : Node) :
    Bar Down a b ↔ a ≠ t0 ∧ b ≠ t0 := by
  cases a <;> cases b <;> simp [Bar, Root, down_universal]

/-- The represented equivalence has exactly the two stated classes. -/
theorem trap_eqv_exact (a b : Node) : Eqv trap a b ↔ SameBlock a b := by
  constructor
  · intro h
    apply star_preserves_block _ (fun x y hxy => ?_) h
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [SameBlock]
  · intro h
    cases a <;> cases b
    · exact Star.refl _
    · simp [SameBlock] at h
    · simp [SameBlock] at h
    · simp [SameBlock] at h
    · exact Star.refl _
    · exact Star.step (Or.inl ⟨rfl, rfl⟩) (Star.refl _)
    · simp [SameBlock] at h
    · exact Star.step (Or.inr ⟨rfl, rfl⟩) (Star.refl _)
    · exact Star.refl _

/-- The destructor fibers have exactly the same two classes. -/
theorem fiber_exact (a b : Node) : Fiber a b ↔ SameBlock a b := by
  constructor
  · intro h
    apply star_preserves_block _ (fun x y hxy => ?_) h
    obtain ⟨hx, hy⟩ := (bar_down_exact x y).1 hxy
    simp [SameBlock, hx, hy]
  · intro h
    cases a <;> cases b
    · exact Star.refl _
    · simp [SameBlock] at h
    · simp [SameBlock] at h
    · simp [SameBlock] at h
    · exact Star.refl _
    · exact Star.step ((bar_down_exact _ _).2 (by simp)) (Star.refl _)
    · simp [SameBlock] at h
    · exact Star.step ((bar_down_exact _ _).2 (by simp)) (Star.refl _)
    · exact Star.refl _

private theorem trap_terminating : WellFounded (fun b a => trap a b) := by
  constructor
  intro a
  have h0 : Acc (fun b a => trap a b) t0 := by
    constructor
    intro b h
    simp [trap] at h
  have h2 : Acc (fun b a => trap a b) t2 := by
    constructor
    intro b h
    simp [trap] at h
  cases a with
  | t0 => exact h0
  | t2 => exact h2
  | t1 =>
      constructor
      intro b h
      have hb : b = t2 := h.2
      subst b
      exact h2

/-- The witness meets all four proof-graph conditions. -/
theorem trap_proofGraph : ProofGraph trap := by
  constructor
  · intro a b c h k
    exact h.2.trans k.2.symm
  · exact trap_terminating
  · intro a b _
    exact down_universal a b
  · intro a b h
    rcases h with ⟨rfl, rfl⟩
    exact Or.inr (Or.inl ((bar_down_exact _ _).2 (by simp)))

private theorem no_two_cycle {R : Rel}
    (wf : WellFounded (fun b a => R a b)) {a b : Node}
    (hab : R a b) (hba : R b a) : False := by
  have h : ∀ x, Acc (fun y x => R x y) x → ∀ y, R x y → R y x → False := by
    intro x acc
    induction acc with
    | intro x _ ih =>
        intro y hxy hyx
        exact ih y hxy x hyx hxy
  exact h a (wf.apply a) b hab hba

/-- Completeness against all proof graphs beta, using beta's own grey relation. -/
theorem trap_complete : Complete trap := by
  intro beta hg hext a b
  constructor
  · intro hab
    have h12 : beta t1 t2 := hext _ _ ⟨rfl, rfl⟩
    cases a with
    | t0 =>
        have hb : b = t0 := by
          have hgrey := hg.admissible _ _ hab
          simp [Grey, Root, Bar, Hat] at hgrey
          exact hgrey
        subst b
        exact False.elim (no_two_cycle hg.terminating hab hab)
    | t1 =>
        exact ⟨rfl, hg.deterministic _ _ _ hab h12⟩
    | t2 =>
        cases b with
        | t0 =>
            have hgrey := hg.admissible _ _ hab
            simp [Grey, Root, Bar, Hat] at hgrey
        | t1 => exact False.elim (no_two_cycle hg.terminating hab h12)
        | t2 => exact False.elim (no_two_cycle hg.terminating hab hab)
  · exact hext a b

/-- The higher target is a valid target and satisfies both targeting conditions. -/
theorem trap_targeted : Targeted trap target := by
  refine ⟨trap_proofGraph, ?_, ?_, ?_⟩
  · constructor
    · intro a
      apply (fiber_exact _ _).2
      cases a <;> simp [SameBlock, target]
    · intro a b h
      have hblock := (fiber_exact a b).1 h
      cases a <;> cases b <;> simp_all [SameBlock, target]
    · intro a h
      cases a with
      | t0 =>
          obtain ⟨u, v, hu, huv⟩ := h
          have hu0 : u = t0 := ((fiber_exact t0 u).1 hu).mp rfl
          subst u
          simp [Root] at huv
      | t1 => exact ⟨t1, Or.inr ⟨rfl, rfl⟩⟩
      | t2 => exact ⟨t1, Or.inr ⟨rfl, rfl⟩⟩
  · intro a
    apply Or.inl
    cases a with
    | t0 => exact Star.refl _
    | t2 => exact Star.refl _
    | t1 =>
        exact Star.step ⟨(bar_down_exact _ _).2 (by simp), rfl, rfl⟩ (Star.refl _)
  · intro a b h
    cases a <;> simp [target, trap] at h

/-- The missing root equation is in Down but outside the graph equivalence. -/
theorem trap_not_universal : ¬ Universal trap := by
  intro h
  have h10 := (trap_eqv_exact t1 t0).1 ((h t1 t0).2 down10)
  simp [SameBlock] at h10

/-- Main result: one fixed witness satisfies every hypothesis and fails universality. -/
theorem lemma64_counterexample :
    ConsistencyInvariant Down ∧ ProofGraph trap ∧ Targeted trap target ∧
      Complete trap ∧ ¬ Universal trap :=
  ⟨down_consistencyInvariant, trap_proofGraph, trap_targeted,
    trap_complete, trap_not_universal⟩

/-- The printed Lemma 64 implication fails already on this finite carrier. -/
theorem lemma64_fails :
    ¬ (ConsistencyInvariant Down → ∀ (rho : Rel) (q : Node → Node),
      Targeted rho q → Complete rho → Universal rho) := by
  intro h
  exact trap_not_universal
    (h down_consistencyInvariant trap target trap_targeted trap_complete)

/-- Section 3: an argument relation in Down cannot be promoted to graph equality. -/
theorem induction_promotion_fails :
    Bar Down t1 t2 ∧ ¬ Bar (Eqv trap) t1 t2 := by
  constructor
  · exact (bar_down_exact _ _).2 (by simp)
  · simp [Bar, Root, trap_eqv_exact, SameBlock]

/-- Section 3: signature closure still holds; it supplies no destructor cancellation. -/
theorem trap_signatureClosed : SignatureClosed (Eqv trap) := by
  intro a b h
  apply (trap_eqv_exact a b).2
  rcases h with h | ⟨rfl, rfl⟩
  · obtain ⟨u, v, ha, hb, huv⟩ := h
    cases a <;> cases b <;> simp_all [Root, SameBlock]
  · exact Iff.rfl

end Lemma64

/-! ## Public declaration and axiom check
These commands check the entire explicit public surface in the same file.
-/

#check @Lemma64.Term
#print axioms Lemma64.Term
#check @Lemma64.Node
#print axioms Lemma64.Node
#check @Lemma64.term
#print axioms Lemma64.term
#check @Lemma64.Rel
#print axioms Lemma64.Rel
#check @Lemma64.Root
#print axioms Lemma64.Root
#check @Lemma64.carrier_model
#print axioms Lemma64.carrier_model
#check @Lemma64.Bar
#print axioms Lemma64.Bar
#check @Lemma64.Hat
#print axioms Lemma64.Hat
#check @Lemma64.SignatureClosed
#print axioms Lemma64.SignatureClosed
#check @Lemma64.CT
#print axioms Lemma64.CT
#check @Lemma64.ct_spec
#print axioms Lemma64.ct_spec
#check @Lemma64.Down
#print axioms Lemma64.Down
#check @Lemma64.DownStep
#print axioms Lemma64.DownStep
#check @Lemma64.down_least_fixed_point
#print axioms Lemma64.down_least_fixed_point
#check @Lemma64.down_universal
#print axioms Lemma64.down_universal
#check @Lemma64.Consistent
#print axioms Lemma64.Consistent
#check @Lemma64.ConstructorCompatible
#print axioms Lemma64.ConstructorCompatible
#check @Lemma64.ConsistencyInvariant
#print axioms Lemma64.ConsistencyInvariant
#check @Lemma64.semantic_fork
#print axioms Lemma64.semantic_fork
#check @Lemma64.down_consistencyInvariant
#print axioms Lemma64.down_consistencyInvariant
#check @Lemma64.Star
#print axioms Lemma64.Star
#check @Lemma64.Eqv
#print axioms Lemma64.Eqv
#check @Lemma64.Grey
#print axioms Lemma64.Grey
#check @Lemma64.ProofGraph
#print axioms Lemma64.ProofGraph
#check @Lemma64.Complete
#print axioms Lemma64.Complete
#check @Lemma64.Fiber
#print axioms Lemma64.Fiber
#check @Lemma64.Target
#print axioms Lemma64.Target
#check @Lemma64.Targeted
#print axioms Lemma64.Targeted
#check @Lemma64.Universal
#print axioms Lemma64.Universal
#check @Lemma64.trap
#print axioms Lemma64.trap
#check @Lemma64.target
#print axioms Lemma64.target
#check @Lemma64.SameBlock
#print axioms Lemma64.SameBlock
#check @Lemma64.bar_down_exact
#print axioms Lemma64.bar_down_exact
#check @Lemma64.trap_eqv_exact
#print axioms Lemma64.trap_eqv_exact
#check @Lemma64.fiber_exact
#print axioms Lemma64.fiber_exact
#check @Lemma64.trap_proofGraph
#print axioms Lemma64.trap_proofGraph
#check @Lemma64.trap_complete
#print axioms Lemma64.trap_complete
#check @Lemma64.trap_targeted
#print axioms Lemma64.trap_targeted
#check @Lemma64.trap_not_universal
#print axioms Lemma64.trap_not_universal
#check @Lemma64.lemma64_counterexample
#print axioms Lemma64.lemma64_counterexample
#check @Lemma64.lemma64_fails
#print axioms Lemma64.lemma64_fails
#check @Lemma64.induction_promotion_fails
#print axioms Lemma64.induction_promotion_fails
#check @Lemma64.trap_signatureClosed
#print axioms Lemma64.trap_signatureClosed
#check @Lemma64.Term.c
#print axioms Lemma64.Term.c
#check @Lemma64.Term.d
#print axioms Lemma64.Term.d
#check @Lemma64.Term.var
#print axioms Lemma64.Term.var
#check @Lemma64.Node.t0
#print axioms Lemma64.Node.t0
#check @Lemma64.Node.t1
#print axioms Lemma64.Node.t1
#check @Lemma64.Node.t2
#print axioms Lemma64.Node.t2
#check @Lemma64.CT.base
#print axioms Lemma64.CT.base
#check @Lemma64.CT.constructor
#print axioms Lemma64.CT.constructor
#check @Lemma64.CT.destructor
#print axioms Lemma64.CT.destructor
#check @Lemma64.Down.refl
#print axioms Lemma64.Down.refl
#check @Lemma64.Down.symm
#print axioms Lemma64.Down.symm
#check @Lemma64.Down.root
#print axioms Lemma64.Down.root
#check @Lemma64.Down.destructor
#print axioms Lemma64.Down.destructor
#check @Lemma64.Star.refl
#print axioms Lemma64.Star.refl
#check @Lemma64.Star.step
#print axioms Lemma64.Star.step
#check @Lemma64.ProofGraph.deterministic
#print axioms Lemma64.ProofGraph.deterministic
#check @Lemma64.ProofGraph.terminating
#print axioms Lemma64.ProofGraph.terminating
#check @Lemma64.ProofGraph.sound
#print axioms Lemma64.ProofGraph.sound
#check @Lemma64.ProofGraph.admissible
#print axioms Lemma64.ProofGraph.admissible
#check @Lemma64.Target.member
#print axioms Lemma64.Target.member
#check @Lemma64.Target.constant
#print axioms Lemma64.Target.constant
#check @Lemma64.Target.redex
#print axioms Lemma64.Target.redex
#check @Lemma64.Targeted.graph
#print axioms Lemma64.Targeted.graph
#check @Lemma64.Targeted.target
#print axioms Lemma64.Targeted.target
#check @Lemma64.Targeted.guided_or_nf
#print axioms Lemma64.Targeted.guided_or_nf
#check @Lemma64.Targeted.exits
#print axioms Lemma64.Targeted.exits
