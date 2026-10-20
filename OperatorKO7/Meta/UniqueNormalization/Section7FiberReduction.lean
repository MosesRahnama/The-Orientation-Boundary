import OperatorKO7.Meta.UniqueNormalization.Section7RootSufficiency

/-!
# Section 7 argument representation

For complete targeted proof graphs on finite coalgebras of strongly almost
non-omega-overlapping constructor systems, universality is equivalent to
argument representation on destructor-fiber steps. The equivalence reduces the
general proof obligation; it does not prove its argument-representation premise
or refute an external proof.

A separate common-reduct theorem proves completeness and universality directly.
The three-term example for d(x) → x constructs a complete universal targeted
proof graph, satisfies the overlap assumptions, and contains both a root rewrite
and a nonidentity destructor-fiber step. Its argument representation is derived
from the constructed graph.

Relation: finite-coalgebra DownOn and the represented parent-forest equality.
Closure: the existing root, constructor and destructor clauses of DownOn.
Trust: Lean kernel with source and axiom checks in Section7FiberReductionReach.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## The argument-level residual -/

/-- Argument representation on one destructor step.  A single
`\bar{\Downarrow_A}` edge inside the coalgebra already carries a destructor
tilde of the equality the proof graph represents. -/
def FiberArgsRepresented (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) (rho : PGraph A R) : Prop :=
  ∀ {a b : Term (sigma ⊕ sigma) nu}, BarStepOn A R a b →
    barRel (EqvOn A rho.par) a b

/-- Destructor tildes of the graph equality compose, because that equality is
transitive and both tildes carry the same root symbol. -/
theorem barRel_eqvOn_trans {A : List (Term (sigma ⊕ sigma) nu)}
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b c : Term (sigma ⊕ sigma) nu}
    (hab : barRel (EqvOn A g) a b) (hbc : barRel (EqvOn A g) b c) :
    barRel (EqvOn A g) a c := by
  obtain ⟨f, as, bs, hf, rfl, hb, hall₁⟩ := hab
  obtain ⟨f', bs', cs, -, hb', rfl, hall₂⟩ := hbc
  rw [hb] at hb'
  simp only [Term.app.injEq] at hb'
  obtain ⟨hff, hbb⟩ := hb'
  subst hff
  subst hbb
  exact ⟨f, as, cs, hf, rfl, rfl,
    forall₂_trans (r := EqvOn A g) (fun _ _ _ hxy hyz => EqvOn.trans hxy hyz) hall₁ hall₂⟩

/-- A destructor path of any length carries a destructor tilde of the graph
equality, unless it is the empty path. -/
theorem FiberArgsRepresented.barRel_of_barReachOn
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hfib : FiberArgsRepresented A R rho)
    {a b : Term (sigma ⊕ sigma) nu} (h : BarReachOn A R a b) :
    a = b ∨ barRel (EqvOn A rho.par) a b := by
  induction h with
  | refl a => exact Or.inl rfl
  | @head a b c hstep _ ih =>
      have hab : barRel (EqvOn A rho.par) a b := hfib hstep
      rcases ih with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (barRel_eqvOn_trans hab hbc)

/-- A root redex carries the reflexive destructor tilde of the graph equality on
its own arguments. -/
theorem barRel_eqvOn_refl_of_rootStep
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a v : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hroot : rootStep R a v) :
    barRel (EqvOn A g) a a := by
  obtain ⟨d, args, haShape⟩ := rootStep_source_destructor hR hroot
  have hargsA : Term.app (Sum.inr d) args ∈ A := by rw [← haShape]; exact ha
  rw [haShape]
  exact ⟨.inr d, args, args, ⟨d, rfl⟩, rfl, rfl,
    forall₂_self_of (fun z hz => EqvOn.refl (Coalgebra.arg hA hargsA hz))⟩

/-! ## The root-step residual follows from the argument residual -/

/-- The graph equality of a proof graph is constructor-compatible in the shape
Theorem 37 consumes. -/
theorem TermTargetedPGraph.constructorCompatible_eqvOn
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TermTargetedPGraph A R) :
    ConstructorCompatible (EqvOn A rho.graph.par) := by
  intro a b hca hcb hab
  rcases rho.graph.constructorCompatible hA hR hca hcb hab with hvar | hhat
  · exact Or.inl hvar
  · rcases hhat with ⟨f, as, bs, ⟨c, hfc⟩, hha, hhb, hall⟩
    subst hfc
    exact Or.inr ⟨c, as, bs, hha, hhb, hall⟩

/-- **The Section 7 residual, moved off the rewrite relation.** For a complete
targeted proof graph on a finite coalgebra of a strongly almost
non-omega-overlapping Constructor TRS, argument representation on destructor
steps implies representation of every root rewrite inside the coalgebra. -/
theorem TermTargetedPGraph.rootStepsRepresented_of_fiberArgs
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete)
    (hfib : FiberArgsRepresented A R rho.graph) :
    RootStepsRepresented A R rho.graph := by
  intro a b ha hb hroot
  rcases rho.guided_or_nf ha with hguided | hnf
  · -- The source is guided to its fiber target, and redex priority makes that
    -- target a root redex as well.
    have htA : rho.target.pick a ∈ A := rho.target.pick_mem ha
    have hfiber : HasRootRedexInFiber A R a :=
      ⟨a, b, ha, hb, BarReachOn.refl a, hroot⟩
    obtain ⟨v, hv, hrootT⟩ := rho.target.redex_if_available ha hfiber
    have hat : EqvOn A rho.graph.par a (rho.target.pick a) :=
      EqvOn.of_reach ha htA hguided.toReach
    have htv : EqvOn A rho.graph.par (rho.target.pick a) v :=
      rho.target_rootStep_eqvOn_of_complete_strong hA hR hstrong hcomplete ha hv hrootT
    have hbar : barRel (EqvOn A rho.graph.par) a (rho.target.pick a) := by
      rcases hfib.barRel_of_barReachOn (rho.target.inFiber ha) with heq | hbar
      · rw [← heq]
        exact barRel_eqvOn_refl_of_rootStep hA hR ha hroot
      · exact hbar
    have hCT : CT (EqvOn A rho.graph.par) b v :=
      thm37 (E := EqvOn A rho.graph.par) hR hstrong (fun _ _ hxy => EqvOn.symm hxy)
        (fun _ _ _ hxy hyz => EqvOn.trans hxy hyz)
        (rho.constructorCompatible_eqvOn hA hR) hroot hbar hrootT
    have hbv : EqvOn A rho.graph.par b v :=
      rho.eqvOn_of_CT_of_complete hA hR hcomplete hb hv hCT
    exact EqvOn.trans (EqvOn.trans hat htv) (EqvOn.symm hbv)
  · -- A graph normal form would accept the root edge as a proper extension.
    by_cases heq : EqvOn A rho.graph.par a b
    · exact heq
    · have hgrey : Grey A R (EqvOn A rho.graph.par) a b := Or.inl hroot
      obtain ⟨beta, hExt, hedge⟩ := rho.graph.extend_one hA hR ha hb hnf heq hgrey
      have hBack : beta.Extends rho.graph := hcomplete beta hExt
      have hOld : rho.graph.par a = some b := hBack hedge
      rw [hnf] at hOld
      contradiction

/-! ## The equivalence -/

/-- Universality gives argument representation at once, since the graph equality
then contains the invariant. -/
theorem TermTargetedPGraph.fiberArgsRepresented_of_universal
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TermTargetedPGraph A R) (huniv : rho.Universal) :
    FiberArgsRepresented A R rho.graph := by
  intro a b hstep
  exact tildeOn_mono (fun _ _ hxy => huniv hxy) hstep.2.2

/-- **The remaining content of Section 7, exactly.** For a complete targeted
proof graph on a finite coalgebra of a strongly almost non-omega-overlapping
Constructor TRS, universality and argument representation on destructor steps
are the same statement. -/
theorem TermTargetedPGraph.universal_iff_fiberArgsRepresented
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hcomplete : rho.graph.Complete) :
    rho.Universal ↔ FiberArgsRepresented A R rho.graph := by
  constructor
  · exact rho.fiberArgsRepresented_of_universal
  · intro hfib
    exact rho.universal_of_rootStepsRepresented hA hR hcomplete
      (rho.rootStepsRepresented_of_fiberArgs hA hR hstrong hcomplete hfib)

/-! ## Non-vacuity of the residual predicate -/

/-- On the empty coalgebra the residual holds, because it has no destructor
step. -/
theorem fiberArgsRepresented_nil {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph ([] : List (Term (sigma ⊕ sigma) nu)) R) :
    FiberArgsRepresented ([] : List (Term (sigma ⊕ sigma) nu)) R rho := by
  intro a b hstep
  exact absurd hstep.1 (List.not_mem_nil)

/-- A coalgebra of constructor-topped members satisfies the residual, because a
destructor step has a destructor-topped source. -/
theorem fiberArgsRepresented_of_all_conTopped
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (hcon : ∀ t ∈ A, ConTopped t) :
    FiberArgsRepresented A R rho := by
  intro a b hstep
  exact absurd (hcon a hstep.1) (not_conTopped_barStepOn_source hstep)


/-! ## Complete graphs with a common reduct -/

/-- A terminating proof graph whose members reach one node has no proper extension. -/
theorem PGraph.complete_of_common_reduct
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (sink : Term (sigma ⊕ sigma) nu)
    (hreach : ∀ a ∈ A, Reach rho.par a sink) : rho.Complete := by
  intro beta hExt a b hab
  cases hOld : rho.par a with
  | none =>
      have ha := (beta.mem_edge hab).1
      have hb := (beta.mem_edge hab).2
      rcases (hreach a ha).head_inv with hEq | ⟨c, hac, _⟩
      · subst a
        exact (beta.term.no_parent_cycle hab (Reach.mono hExt (hreach b hb))).elim
      · rw [hOld] at hac
        contradiction
  | some c =>
      have hcb : c = b := Option.some.inj ((hExt hOld).symm.trans hab)
      exact congrArg some hcb

/-- A common graph reduct represents every invariant pair without an overlap premise. -/
theorem TermTargetedPGraph.universal_of_common_reduct
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TermTargetedPGraph A R) (sink : Term (sigma ⊕ sigma) nu)
    (hreach : ∀ a ∈ A, Reach rho.graph.par a sink) : rho.Universal := by
  intro a b hab
  exact ⟨hab.mem.1, hab.mem.2, sink, hreach a hab.mem.1, hreach b hab.mem.2⟩

/-! ## A three-term example with a changing destructor fiber -/

namespace Section7Active

abbrev T := Term (Unit ⊕ Unit) Unit

def wrap (t : T) : T := .app (.inr ()) [t]
def constant : T := .app (.inl ()) []
def once : T := wrap constant
def twice : T := wrap once
def terms : List T := coalgebraOf [twice]

theorem terms_coalgebra : Coalgebra terms := coalgebra_coalgebraOf [twice]

theorem mem_terms (t : T) : t ∈ terms ↔ t = twice ∨ t = once ∨ t = constant := by
  simp [terms, coalgebraOf, twice, once, wrap, constant, subterms, subtermsList]

@[simp] theorem twice_ne_once : twice ≠ once := by decide
@[simp] theorem twice_ne_constant : twice ≠ constant := by decide
@[simp] theorem once_ne_constant : once ≠ constant := by decide

theorem constant_conTopped : ConTopped constant := Or.inr ⟨(), [], rfl⟩

/-- The constructor rewrite rule d(x) → x. -/
def rule : Rule (Unit ⊕ Unit) Unit where
  lhs := wrap (.var ())
  rhs := .var ()
  lhs_isApp := rfl

def rules : TRS (Unit ⊕ Unit) Unit := [rule]

theorem rules_constructor : ConstructorRules rules := by
  intro r hr
  have hr' : r = rule := by simpa [rules] using hr
  subst r
  refine ⟨(), [.var ()], rfl, ?_⟩
  intro p hp
  have hp' : p = .var () := by simpa using hp
  subst p
  exact ConOnly.var ()

/-- Every root step deletes exactly one outer destructor. -/
theorem rootStep_iff (a b : T) : rootStep rules a b ↔ a = wrap b := by
  constructor
  · rintro ⟨r, hr, sub, ha, hb⟩
    have hr' : r = rule := by simpa [rules] using hr
    subst r
    change a = wrap (sub ()) at ha
    change b = sub () at hb
    exact ha.trans (congrArg wrap hb.symm)
  · intro h
    exact ⟨rule, by simp [rules], fun _ => b, h, rfl⟩

theorem rules_rhsDetermined : Rule.RhsDetermined rule := by
  intro a b h
  change wrap (a ()) = wrap (b ()) at h
  change a () = b ()
  simpa [wrap] using h

/-- The example satisfies the overlap assumptions of the Section 7 equivalence. -/
theorem rules_strong : StronglyAlmostNonOmegaOverlapping rules := by
  constructor
  · intro r₁ hr₁ r₂ hr₂ s hsub happ _
    have hr₁' : r₁ = rule := by simpa [rules] using hr₁
    subst r₁
    obtain ⟨f, args, a, heq, ha, hsa⟩ := hsub
    change Term.app (.inr ()) [.var ()] = Term.app f args at heq
    obtain ⟨_, hargs⟩ := Term.app.inj heq
    have ha' : a = .var () := by simpa only [← hargs, List.mem_singleton] using ha
    subst a
    have hs : s = .var () := hsa.eq_of_var
    subst s
    exact Bool.noConfusion happ
  · intro r₁ hr₁ r₂ hr₂ _
    have h₁ : r₁ = rule := by simpa [rules] using hr₁
    have h₂ : r₂ = rule := by simpa [rules] using hr₂
    subst r₁
    subst r₂
    refine ⟨CommonGeneralisation.self rule rules_rhsDetermined, ?_⟩
    intro x hx
    change VarOccurs x (.var () : T) at hx
    change VarOccurs x (wrap (.var ()))
    exact VarOccurs.arg (by simp) hx

theorem root_once : rootStep rules once constant := (rootStep_iff _ _).2 rfl
theorem root_twice : rootStep rules twice once := (rootStep_iff _ _).2 rfl

theorem down_once_constant : DownOn terms rules once constant :=
  DownOn.rootComp ((mem_terms _).2 (Or.inr (Or.inl rfl)))
    ((mem_terms _).2 (Or.inr (Or.inr rfl))) root_once
    (DownOn.refl ((mem_terms _).2 (Or.inr (Or.inr rfl))))

theorem down_twice_constant : DownOn terms rules twice constant :=
  DownOn.rootComp ((mem_terms _).2 (Or.inl rfl))
    ((mem_terms _).2 (Or.inr (Or.inl rfl))) root_twice down_once_constant

theorem down_twice_once : DownOn terms rules twice once :=
  DownOn.rootComp ((mem_terms _).2 (Or.inl rfl))
    ((mem_terms _).2 (Or.inr (Or.inl rfl))) root_twice
    (DownOn.refl ((mem_terms _).2 (Or.inr (Or.inl rfl))))

theorem down_all {a b : T} (ha : a ∈ terms) (hb : b ∈ terms) : DownOn terms rules a b := by
  rcases (mem_terms a).1 ha with rfl | rfl | rfl <;>
    rcases (mem_terms b).1 hb with rfl | rfl | rfl
  · exact DownOn.refl ha
  · exact down_twice_once
  · exact down_twice_constant
  · exact down_twice_once.symm
  · exact DownOn.refl ha
  · exact down_once_constant
  · exact down_twice_constant.symm
  · exact down_once_constant.symm
  · exact DownOn.refl ha

/-- Two distinct destructor terms have different but related arguments. -/
theorem bar_twice_once : BarStepOn terms rules twice once := by
  refine ⟨(mem_terms _).2 (Or.inl rfl), (mem_terms _).2 (Or.inr (Or.inl rfl)), ?_⟩
  exact ⟨.inr (), [once], [constant], ⟨(), rfl⟩, rfl, rfl,
    List.Forall₂.cons down_once_constant List.Forall₂.nil⟩

def parent (t : T) : Option T :=
  if t = twice then some once else if t = once then some constant else none

theorem parent_edge {a b : T} (h : parent a = some b) :
    (a = twice ∧ b = once) ∨ (a = once ∧ b = constant) := by
  by_cases h₂ : a = twice
  · subst a
    have hb : b = once := by simpa [parent] using h.symm
    exact Or.inl ⟨rfl, hb⟩
  · by_cases h₁ : a = once
    · subst a
      have hb : b = constant := by simpa [parent, h₂] using h.symm
      exact Or.inr ⟨rfl, hb⟩
    · simp [parent, h₂, h₁] at h

theorem parent_terminating : Terminating parent := by
  have hwf : WellFounded (fun x y : T => x.size < y.size) :=
    InvImage.wf (f := Term.size) Nat.lt_wfRel.wf
  have hsub : Subrelation (fun b a : T => parent a = some b)
      (fun b a : T => b.size < a.size) := by
    intro b a h
    rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  exact Subrelation.wf hsub hwf

def graph : PGraph terms rules where
  par := parent
  mem_edge := by
    intro a b h
    rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [mem_terms]
  term := parent_terminating
  sub := fun h => down_all h.mem.1 h.mem.2
  grey := by
    intro a b h
    rcases parent_edge h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl root_twice
    · exact Or.inl root_once

theorem reach_constant {t : T} (ht : t ∈ terms) : Reach graph.par t constant := by
  rcases (mem_terms t).1 ht with rfl | rfl | rfl
  · exact Reach.head (b := once) (by simp [graph, parent])
      (Reach.head (b := constant)
        (by simp [graph, parent, Ne.symm twice_ne_once]) (Reach.refl constant))
  · exact Reach.head (b := constant)
      (by simp [graph, parent, Ne.symm twice_ne_once]) (Reach.refl constant)
  · exact Reach.refl _

theorem graph_complete : graph.Complete :=
  graph.complete_of_common_reduct constant (fun _ h => reach_constant h)

/-- The constructor selects itself; both destructor terms select d(c). -/
def pick (t : T) : T := if t = constant then constant else once

def target : Section7Target terms rules where
  pick := pick
  pick_mem := by
    intro t _
    by_cases h : t = constant <;> simp [pick, h, mem_terms]
  inFiber := by
    intro t ht
    rcases (mem_terms t).1 ht with rfl | rfl | rfl
    · simpa [pick] using BarReachOn.single bar_twice_once
    · simpa [pick] using BarReachOn.refl (A := terms) (R := rules) once
    · simpa [pick] using BarReachOn.refl (A := terms) (R := rules) constant
  respectsFiber := by
    intro t z _ _ h
    by_cases ht : t = constant
    · subst t
      have hz : constant = z := h.eq_of_conTopped constant_conTopped
      subst z
      rfl
    · by_cases hz : z = constant
      · subst z
        exact (ht (h.symm.eq_of_conTopped constant_conTopped).symm).elim
      · simp [pick, ht, hz]
  redex_if_available := by
    intro t _ hred
    by_cases ht : t = constant
    · subst t
      exact (no_rootRedexInFiber_of_conTopped rules_constructor constant_conTopped hred).elim
    · refine ⟨constant, (mem_terms _).2 (Or.inr (Or.inr rfl)), ?_⟩
      simpa [pick, ht] using root_once

def targeted : TermTargetedPGraph terms rules where
  graph := graph
  target := target
  guided_or_nf := by
    intro t ht
    apply Or.inl
    rcases (mem_terms t).1 ht with rfl | rfl | rfl
    · have hstep : GuidedParentStep graph twice once :=
        ⟨by simp [graph, parent], bar_twice_once⟩
      simpa [target, pick] using Relation.ReflTransGen.single hstep
    · simpa [target, pick] using
        (Relation.ReflTransGen.refl : GuidedReach graph once once)
    · simpa [target, pick] using
        (Relation.ReflTransGen.refl : GuidedReach graph constant constant)
  target_edge_exits_fiber := by
    intro t z _ hpar hbar
    by_cases ht : t = constant
    · subst t
      simp [target, pick, graph, parent, Ne.symm twice_ne_constant,
        Ne.symm once_ne_constant] at hpar
    · have hz : z = constant := by
        simpa [target, pick, ht, graph, parent, Ne.symm twice_ne_once] using hpar.symm
      subst z
      exact ht (hbar.symm.eq_of_conTopped constant_conTopped).symm

theorem targeted_universal : targeted.Universal :=
  targeted.universal_of_common_reduct constant (fun _ h => reach_constant h)

theorem fiberArgs : FiberArgsRepresented terms rules targeted.graph :=
  targeted.fiberArgsRepresented_of_universal targeted_universal

/-- A complete universal targeted graph with a root rewrite and a nonidentity
destructor-fiber step on the same finite coalgebra. -/
theorem active_destructor_certificate :
    ConstructorRules rules ∧ StronglyAlmostNonOmegaOverlapping rules ∧
    Coalgebra terms ∧ targeted.graph.Complete ∧ targeted.Universal ∧
    FiberArgsRepresented terms rules targeted.graph ∧
    rootStep rules once constant ∧ once ≠ constant ∧
    BarStepOn terms rules twice once ∧ twice ≠ once :=
  ⟨rules_constructor, rules_strong, terms_coalgebra, graph_complete, targeted_universal,
    fiberArgs, root_once, once_ne_constant, bar_twice_once, twice_ne_once⟩

end Section7Active

/-! ## A complete targeted graph that omits a root rewrite -/

namespace Section7Active.Trap

/-- This graph points d(c) toward d(d(c)), with both other members terminal. -/
def parent (t : T) : Option T := if t = once then some twice else none

theorem parent_edge {a b : T} (h : parent a = some b) : a = once ∧ b = twice := by
  by_cases ha : a = once
  · subst a
    exact ⟨rfl, by simpa [parent] using h.symm⟩
  · simp [parent, ha] at h

theorem parent_terminating : Terminating parent := by
  let rank : T → Nat := fun t => if t = once then 1 else 0
  have hsub : Subrelation (fun b a : T => parent a = some b)
      (fun b a : T => rank b < rank a) := by
    intro b a h
    obtain ⟨rfl, rfl⟩ := parent_edge h
    simp [rank]
  exact Subrelation.wf hsub (InvImage.wf (f := rank) Nat.lt_wfRel.wf)

def graph : PGraph terms rules where
  par := parent
  mem_edge := by
    intro a b h
    obtain ⟨rfl, rfl⟩ := parent_edge h
    simp [mem_terms]
  term := parent_terminating
  sub := fun h => down_all h.mem.1 h.mem.2
  grey := by
    intro a b h
    obtain ⟨rfl, rfl⟩ := parent_edge h
    exact Or.inr (Or.inl bar_twice_once.symm.2.2)

theorem reach_eq_of_no_parent {g : T → Option T} {a b : T}
    (hn : g a = none) (h : Reach g a b) : a = b := by
  rcases h.head_inv with heq | ⟨c, hc, _⟩
  · exact heq
  · rw [hn] at hc
    contradiction

theorem once_reach_cases {t : T} (h : Reach graph.par once t) :
    t = once ∨ t = twice := by
  rcases h.head_inv with heq | ⟨b, hb, hbt⟩
  · exact Or.inl heq.symm
  · have hparent : parent once = some b := hb
    have hb' : b = twice := (parent_edge (a := once) (b := b) hparent).2
    subst b
    exact Or.inr (reach_eq_of_no_parent (by simp [graph, parent]) hbt).symm

theorem once_not_eqv_constant : ¬ EqvOn terms graph.par once constant := by
  rintro ⟨_, _, t, hot, hct⟩
  have hct' : constant = t :=
    reach_eq_of_no_parent (by simp [graph, parent, Ne.symm once_ne_constant]) hct
  subst t
  rcases once_reach_cases hot with h | h
  · exact once_ne_constant h.symm
  · exact twice_ne_constant h.symm

theorem no_grey_twice_constant (E : CRel Unit Unit) :
    ¬ Grey terms rules E twice constant := by
  rintro (hroot | hbar | hhat)
  · exact twice_ne_once ((rootStep_iff _ _).mp hroot)
  · obtain ⟨f, as, bs, ⟨d, hd⟩, _, hb, _⟩ := hbar
    subst f
    simp [constant] at hb
  · exact (not_conTopped_destructor [once]) (ConTopped.of_hatEq hhat)

theorem grey_from_constant {E : CRel Unit Unit} {b : T}
    (h : Grey terms rules E constant b) : b = constant := by
  rcases h with hroot | hbar | hhat
  · have hshape := (rootStep_iff _ _).mp hroot
    simp [constant, wrap] at hshape
  · obtain ⟨f, as, bs, ⟨d, hd⟩, ha, _, _⟩ := hbar
    subst f
    simp [constant] at ha
  · rcases hhat with ⟨x, ha, _⟩ | ⟨f, as, bs, _, ha, hb, hall⟩
    · simp [constant] at ha
    · change Term.app (.inl ()) [] = Term.app f as at ha
      obtain ⟨hf, has⟩ := Term.app.inj ha
      subst f
      subst as
      cases hall
      exact hb

/-- Every candidate added edge is already present, forms a cycle, or is not grey. -/
theorem graph_complete : graph.Complete := by
  intro beta hExt a b hab
  have ha := (beta.mem_edge hab).1
  have hb := (beta.mem_edge hab).2
  have hretained : beta.par once = some twice :=
    hExt (show graph.par once = some twice from by simp [graph, parent])
  rcases (mem_terms _).mp ha with rfl | rfl | rfl
  · rcases (mem_terms _).mp hb with rfl | rfl | rfl
    · exact (beta.term.no_parent_cycle hab (Reach.refl twice)).elim
    · exact (beta.term.no_parent_cycle hab
        (Reach.head hretained (Reach.refl twice))).elim
    · exact (no_grey_twice_constant _ (beta.grey hab)).elim
  · have htb : twice = b := Option.some.inj (hretained.symm.trans hab)
    rw [← htb]
    simp [graph, parent]
  · have hb' : b = constant := grey_from_constant (beta.grey hab)
    subst b
    exact (beta.term.no_parent_cycle hab (Reach.refl constant)).elim

/-- Both destructor terms select the larger root redex. -/
def pick (t : T) : T := if t = constant then constant else twice

def target : Section7Target terms rules where
  pick := pick
  pick_mem := by
    intro t _
    by_cases ht : t = constant <;> simp [pick, ht, mem_terms]
  inFiber := by
    intro t ht
    rcases (mem_terms _).mp ht with rfl | rfl | rfl
    · simpa [pick] using BarReachOn.refl (A := terms) (R := rules) twice
    · simpa [pick] using BarReachOn.single bar_twice_once.symm
    · simpa [pick] using BarReachOn.refl (A := terms) (R := rules) constant
  respectsFiber := by
    intro t z _ _ h
    by_cases ht : t = constant
    · subst t
      have hz : constant = z := h.eq_of_conTopped constant_conTopped
      subst z
      rfl
    · by_cases hz : z = constant
      · subst z
        exact (ht (h.symm.eq_of_conTopped constant_conTopped).symm).elim
      · simp [pick, ht, hz]
  redex_if_available := by
    intro t _ hred
    by_cases ht : t = constant
    · subst t
      exact (no_rootRedexInFiber_of_conTopped rules_constructor constant_conTopped hred).elim
    · refine ⟨once, (mem_terms _).mpr (Or.inr (Or.inl rfl)), ?_⟩
      simpa [pick, ht] using root_twice

theorem all_guided (t : T) (ht : t ∈ terms) :
    GuidedReach graph t (target.pick t) := by
  rcases (mem_terms _).mp ht with rfl | rfl | rfl
  · simpa [target, pick] using
      (Relation.ReflTransGen.refl : GuidedReach graph twice twice)
  · have hstep : GuidedParentStep graph once twice :=
      ⟨by simp [graph, parent], bar_twice_once.symm⟩
    simpa [target, pick] using Relation.ReflTransGen.single hstep
  · simpa [target, pick] using
      (Relation.ReflTransGen.refl : GuidedReach graph constant constant)

def targeted : TermTargetedPGraph terms rules where
  graph := graph
  target := target
  guided_or_nf := fun ht => Or.inl (all_guided _ ht)
  target_edge_exits_fiber := by
    intro t z _ hpar _
    by_cases ht : t = constant <;>
      simp [target, pick, graph, parent, ht, Ne.symm once_ne_constant] at hpar

theorem targeted_not_universal : ¬ targeted.Universal := by
  intro hu
  exact once_not_eqv_constant (hu down_once_constant)

theorem fiberArgs_not_represented : ¬ FiberArgsRepresented terms rules graph := by
  intro hf
  exact targeted_not_universal
    ((targeted.universal_iff_fiberArgsRepresented terms_coalgebra rules_constructor
      rules_strong graph_complete).mpr hf)

/-- All current hypotheses of the all-complete-targeted universality target hold. -/
theorem complete_targeted_counterexample :
    Coalgebra terms ∧ ConstructorRules rules ∧ StronglyAlmostNonOmegaOverlapping rules ∧
      targeted.graph.Complete ∧ (∀ t ∈ terms, GuidedReach graph t (target.pick t)) ∧
      ¬ targeted.Universal ∧ ¬ FiberArgsRepresented terms rules graph :=
  ⟨terms_coalgebra, rules_constructor, rules_strong, graph_complete, all_guided,
    targeted_not_universal, fiberArgs_not_represented⟩

theorem not_every_complete_targeted_graph_universal :
    ¬ ∀ rho : TermTargetedPGraph terms rules, rho.graph.Complete → rho.Universal := by
  intro h
  exact targeted_not_universal (h targeted graph_complete)

/-- The selected target root-contracts back into its own destructor fiber. -/
theorem selected_redex_returns_to_fiber :
    target.pick once = twice ∧ rootStep rules twice once ∧ BarStepOn terms rules twice once :=
  ⟨by simp [target, pick], root_twice, bar_twice_once⟩

/-! ## Repair by changing parents -/

/-- Redirect d(c) to c, then add d(d(c)) → d(c). -/
noncomputable def repairedParent : T → Option T :=
  extendPar (extendPar parent once constant) twice once

theorem repairedParent_eq : repairedParent = Section7Active.parent := by
  classical
  funext t
  by_cases h₂ : t = twice
  · subst t
    simp [repairedParent, extendPar, Section7Active.parent]
  · by_cases h₁ : t = once
    · subst t
      simp [repairedParent, extendPar, Section7Active.parent, h₂]
    · simp [repairedParent, extendPar, Section7Active.parent, h₂, h₁, parent]

theorem parent_replacement_repairs_graph :
    Terminating repairedParent ∧
      (∀ t ∈ terms, Reach repairedParent t constant) ∧
      Section7Active.targeted.graph.Complete ∧ Section7Active.targeted.Universal := by
  rw [repairedParent_eq]
  exact ⟨Section7Active.parent_terminating, (fun _ ht => Section7Active.reach_constant ht),
    Section7Active.graph_complete, Section7Active.targeted_universal⟩

/-- The repair cannot preserve the old d(c) → d(d(c)) edge. -/
theorem repair_is_not_edge_preserving : ¬ graph.Extends Section7Active.graph := by
  intro h
  have hp := h (show graph.par once = some twice from by simp [graph, parent])
  have heq : constant = twice := by
    simpa [Section7Active.graph, Section7Active.parent, Ne.symm twice_ne_once] using hp
  exact twice_ne_constant heq.symm

theorem same_coalgebra_complete_universal_and_nonuniversal :
    Section7Active.targeted.graph.Complete ∧ Section7Active.targeted.Universal ∧
      targeted.graph.Complete ∧ ¬ targeted.Universal :=
  ⟨Section7Active.graph_complete, Section7Active.targeted_universal,
    graph_complete, targeted_not_universal⟩

/-! ## The general path repair on the counterexample -/

/-- The trapped destructor follows a legal reversible edge to a graph root. -/
theorem once_guided_to_twice_root :
    GuidedReach graph once twice ∧ graph.NF twice := by
  refine ⟨Relation.ReflTransGen.single ?_, ?_⟩
  · exact ⟨by simp [graph, parent], bar_twice_once.symm⟩
  · simp [PGraph.NF, graph, parent]

/-- The constant has no outgoing edge in any proof graph on these terms. -/
theorem any_graph_constant_nf (rho : PGraph terms rules) : rho.NF constant := by
  cases hc : rho.par constant with
  | none => exact hc
  | some b =>
      have hb : b = constant := grey_from_constant (rho.grey hc)
      subst b
      exact (rho.term.no_parent_cycle hc (Reach.refl constant)).elim

/-- Generic reversible-path repair represents all terms of this coalgebra and
retains every old equality while replacing the trapped parent edge. -/
theorem generic_path_repair :
    ∃ beta : PGraph terms rules, beta.par once = some constant ∧
      (∀ x y, EqvOn terms graph.par x y → EqvOn terms beta.par x y) ∧
      (∀ t ∈ terms, Reach beta.par t constant) ∧ beta.Complete ∧ beta.Universal := by
  obtain ⟨beta, hedge, hmono, hnew⟩ :=
    graph.repair_rootStep_along_guided_path terms_coalgebra rules_constructor
      (by simp [mem_terms]) (by simp [mem_terms])
      once_guided_to_twice_root.1 once_guided_to_twice_root.2
      once_not_eqv_constant root_once
  have hconst := any_graph_constant_nf beta
  have htwiceOnce : EqvOn terms graph.par twice once :=
    EqvOn.symm (EqvOn.of_reach (by simp [mem_terms]) (by simp [mem_terms])
      (Reach.head (show graph.par once = some twice from by simp [graph, parent])
        (Reach.refl twice)))
  have heqc : ∀ t ∈ terms, EqvOn terms beta.par t constant := by
    intro t ht
    rcases (mem_terms t).mp ht with rfl | rfl | rfl
    · exact EqvOn.trans (hmono _ _ htwiceOnce) hnew
    · exact hnew
    · exact EqvOn.refl (by simp [mem_terms])
  have hreach : ∀ t ∈ terms, Reach beta.par t constant := by
    intro t ht
    obtain ⟨_, _, z, htz, hcz⟩ := heqc t ht
    have hz : constant = z := reach_eq_of_no_parent hconst hcz
    subst z
    exact htz
  refine ⟨beta, hedge, hmono, hreach, beta.complete_of_common_reduct constant hreach, ?_⟩
  apply beta.universal_iff_down_subset.mpr
  intro a b hab
  exact ⟨hab.mem.1, hab.mem.2, constant, hreach a hab.mem.1, hreach b hab.mem.2⟩

/-- Edge completeness in the counterexample does not imply equality completeness. -/
theorem trap_not_equalityComplete : ¬ graph.EqualityComplete := by
  intro hmax
  exact once_not_eqv_constant
    (hmax.rootStep_of_guided_to_root terms_coalgebra rules_constructor
      (by simp [mem_terms]) (by simp [mem_terms])
      once_guided_to_twice_root.1 once_guided_to_twice_root.2 root_once)

/-- The positive graph and the trapped graph distinguish the two completeness
conditions on one rule and one finite coalgebra. -/
theorem equality_complete_repair_separates_edge_completion :
    graph.Complete ∧ ¬ graph.EqualityComplete ∧
      ∃ beta : PGraph terms rules, graph.EqualityExtends beta ∧
        beta.EqualityComplete ∧ beta.Universal := by
  obtain ⟨beta, _, hmono, _, _, huniv⟩ := generic_path_repair
  have hmax : beta.EqualityComplete := by
    intro gamma _ x y hxy
    exact (huniv x y).mpr (gamma.sub hxy)
  exact ⟨graph_complete, trap_not_equalityComplete, beta, (by intro x y h; exact hmono x y h),
    hmax, huniv⟩

end Section7Active.Trap




/-! ## Reconstruction on positive and zero-distance redex fibers -/

namespace Section7Active

theorem graph_barClosed : graph.BarClosed := by
  intro a b hbar
  exact ⟨hbar.1, hbar.2.1, constant, reach_constant hbar.1, reach_constant hbar.2.1⟩

theorem graph_normalRoot_eq_constant {a : T} (ha : a ∈ terms) :
    graph.normalRoot a = constant := by
  have hc : constant = graph.normalRoot constant :=
    (graph.normalRoot_spec constant).1.toParentPath.eq_of_none
      (show graph.par constant = none from by
        simp [graph, parent, Ne.symm twice_ne_constant, Ne.symm once_ne_constant])
  exact (graph.normalRoot_eq_of_reach (reach_constant ha)).trans hc.symm

theorem once_positive_fiberDistance : graph.fiberDistance once ≠ 0 := by
  intro hzero
  have hbar := (graph.fiberDistance_zero_iff once).mp hzero
  rw [graph_normalRoot_eq_constant (by simp [mem_terms])] at hbar
  exact once_ne_constant (hbar.symm.eq_of_conTopped constant_conTopped).symm

/-- The positive-distance reconstruction selects d(c), whose actual old edge
leaves the destructor fiber. It cannot select d(d(c))'s internal edge. -/
theorem reconstruction_selects_actual_exit :
    let C := barClassOf terms rules once (by simp [mem_terms])
    graph_barClosed.retargetPick C = once ∧
      graph_barClosed.retargetExit C = some constant := by
  classical
  let C := barClassOf terms rules once (by simp [mem_terms])
  change graph_barClosed.retargetPick C = once ∧ graph_barClosed.retargetExit C = some constant
  have hd : graph.fiberDistance (graph_barClosed.retargetPick C) =
      graph.fiberDistance once :=
    graph_barClosed.retarget_pick_distance rules_constructor (by simp [mem_terms])
  have hnone : graph_barClosed.retargetExit C ≠ none := by
    intro hn
    have hz := (graph_barClosed.retargetExit_none_iff C).mp hn
    exact once_positive_fiberDistance (hd.symm.trans hz)
  cases he : graph_barClosed.retargetExit C with
  | none => exact (hnone he).elim
  | some v =>
      have hs := graph_barClosed.retargetExit_spec he
      rcases parent_edge (a := graph_barClosed.retargetPick C) (b := v) hs.1 with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
      · have hdistEq : graph.fiberDistance twice = graph.fiberDistance once :=
          graph_barClosed.fiberDistance_eq_of_barReach_all
            (BarReachOn.single bar_twice_once)
        have hdrop := hs.2.2
        rw [hsrc, hdst, hdistEq] at hdrop
        exact (Nat.lt_irrefl _ hdrop).elim
      · exact ⟨hsrc, congrArg some hdst⟩

theorem reconstructed_once_parent :
    (graph_barClosed.retargetGraph rules_constructor).par once = some constant := by
  have hs := reconstruction_selects_actual_exit
  change graph_barClosed.retargetParent rules_constructor once = some constant
  rw [graph_barClosed.retargetParent_of_target rules_constructor
    (by simp [mem_terms]) hs.1.symm]
  exact hs.2

theorem reconstructed_active_graph_universal :
    (graph_barClosed.retargeted rules_constructor).AllGuided ∧
      (graph_barClosed.retargeted rules_constructor).graph.Universal := by
  refine ⟨graph_barClosed.retargeted_allGuided rules_constructor, ?_⟩
  apply ((graph_barClosed.retargeted rules_constructor).graph.universal_iff_down_subset).mpr
  intro a b hab
  exact (graph_barClosed.retargetGraph_eqv_iff rules_constructor a b).mpr
    ⟨hab.mem.1, hab.mem.2, constant, reach_constant hab.mem.1, reach_constant hab.mem.2⟩

namespace Trap

theorem graph_barClosed : graph.BarClosed := by
  intro a b hbar
  have ha : a ≠ constant := by
    intro heq
    subst a
    exact (not_conTopped_barStepOn_source hbar) constant_conTopped
  have hb : b ≠ constant := by
    intro heq
    subst b
    exact (not_conTopped_barStepOn_source hbar.symm) constant_conTopped
  have reaches : ∀ t ∈ terms, t ≠ constant → Reach graph.par t twice := by
    intro t ht hne
    rcases (mem_terms t).mp ht with rfl | rfl | rfl
    · exact Reach.refl twice
    · exact Reach.head (by simp [graph, parent]) (Reach.refl twice)
    · exact (hne rfl).elim
  exact ⟨hbar.1, hbar.2.1, twice, reaches a hbar.1 ha, reaches b hbar.2.1 hb⟩

/-- Zero distance concerns the old graph-root fiber, not absence of rewrite redexes. -/
theorem zero_distance_redex_fiber :
    graph.fiberDistance once = 0 ∧ rootStep rules once constant := by
  refine ⟨(graph.fiberDistance_zero_iff once).mpr ?_, root_once⟩
  have hroot : graph.normalRoot once = twice :=
    ((graph.normalRoot_spec once).1.comparable once_guided_to_twice_root.1.toReach).elim
      (fun hp => hp.toParentPath.eq_of_none (graph.normalRoot_spec once).2)
      (fun hp => (hp.toParentPath.eq_of_none once_guided_to_twice_root.2).symm)
  rw [hroot]
  exact BarReachOn.single bar_twice_once.symm

/-- Equality-preserving reconstruction alone does not add the missing rewrite. -/
theorem reconstructed_trap_still_not_universal :
    (graph_barClosed.retargeted rules_constructor).AllGuided ∧
      ¬ (graph_barClosed.retargeted rules_constructor).graph.Universal := by
  refine ⟨graph_barClosed.retargeted_allGuided rules_constructor, ?_⟩
  intro huniv
  have hnew := (huniv once constant).mpr down_once_constant
  exact once_not_eqv_constant
    ((graph_barClosed.retargetGraph_eqv_iff rules_constructor once constant).mp hnew)

end Trap
end Section7Active

/-! ## An unrepresented root step produces an argument obstruction -/

/-- A failed pointwise relation has an aligned pair at one list position. -/
theorem forall₂_exists_aligned_failure {alpha : Type u} {beta : Type v}
    {P Q : alpha → beta → Prop} {xs : List alpha} {ys : List beta}
    (hP : List.Forall₂ P xs ys) (hnot : ¬ List.Forall₂ Q xs ys) :
    ∃ xp yp x y xt yt,
      xs = xp ++ x :: xt ∧ ys = yp ++ y :: yt ∧
      xp.length = yp.length ∧ P x y ∧ ¬ Q x y := by
  classical
  revert hnot
  induction hP with
  | nil =>
      intro hnot
      exact (hnot List.Forall₂.nil).elim
  | @cons x y xs ys hxy htail ih =>
      intro hnot
      by_cases hQ : Q x y
      · have htailNot : ¬ List.Forall₂ Q xs ys := by
          intro h
          exact hnot (List.Forall₂.cons hQ h)
        obtain ⟨xp, yp, x', y', xt, yt, hx, hy, hlen, hP', hQ'⟩ := ih htailNot
        refine ⟨x :: xp, y :: yp, x', y', xt, yt, ?_, ?_, ?_, hP', hQ'⟩
        · exact congrArg (List.cons x) hx
        · exact congrArg (List.cons y) hy
        · exact congrArg Nat.succ hlen
      · exact ⟨[], [], x, y, xs, ys, rfl, rfl, rfl, hxy, hQ⟩

/-- A destructor path either represents all its endpoint arguments or contains
an actual edge whose arguments are not represented. -/
theorem BarReachOn.eq_or_barRel_or_bad_step
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a b : Term (sigma ⊕ sigma) nu}
    (hpath : BarReachOn A R a b) :
    a = b ∨ barRel (EqvOn A rho.par) a b ∨
      ∃ u v, BarReachOn A R a u ∧ BarStepOn A R u v ∧
        BarReachOn A R v b ∧ ¬ barRel (EqvOn A rho.par) u v := by
  classical
  induction hpath with
  | refl => exact Or.inl rfl
  | @head a u b hstep htail ih =>
      by_cases hrep : barRel (EqvOn A rho.par) a u
      · rcases ih with rfl | hrepTail | ⟨p, q, hpre, hpq, hsuf, hbad⟩
        · exact Or.inr (Or.inl hrep)
        · exact Or.inr (Or.inl (barRel_eqvOn_trans hrep hrepTail))
        · exact Or.inr (Or.inr
            ⟨p, q, BarReachOn.head hstep hpre, hpq, hsuf, hbad⟩)
      · exact Or.inr (Or.inr
          ⟨a, u, BarReachOn.refl a, hstep, htail, hrep⟩)

/-- The failed argument pair belongs to one shared argument index of the
two actual destructor terms. -/
theorem BarStepOn.exists_unrepresented_argument
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a b : Term (sigma ⊕ sigma) nu}
    (hstep : BarStepOn A R a b) (hnot : ¬ barRel (EqvOn A rho.par) a b) :
    ∃ d xp yp x y xt yt,
      a = .app (.inr d) (xp ++ x :: xt) ∧
      b = .app (.inr d) (yp ++ y :: yt) ∧
      xp.length = yp.length ∧ DownOn A R x y ∧ ¬ EqvOn A rho.par x y := by
  obtain ⟨_, _, f, xs, ys, ⟨d, hf⟩, ha, hb, hall⟩ := hstep
  subst hf
  have hargs : ¬ List.Forall₂ (EqvOn A rho.par) xs ys := by
    intro h
    exact hnot ⟨.inr d, xs, ys, ⟨d, rfl⟩, ha, hb, h⟩
  obtain ⟨xp, yp, x, y, xt, yt, hx, hy, hlen, hxy, hne⟩ :=
    forall₂_exists_aligned_failure hall hargs
  exact ⟨d, xp, yp, x, y, xt, yt,
    ha.trans (congrArg (Term.app (.inr d)) hx),
    hb.trans (congrArg (Term.app (.inr d)) hy), hlen, hxy, hne⟩

/-- Equality maximality forces an actual outgoing root rewrite at the target
of an unrepresented root rewrite. No overlap hypothesis is used. -/
theorem TermTargetedPGraph.missing_root_has_target_exit
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hroot : rootStep R a b) (hmissing : ¬ EqvOn A rho.graph.par a b) :
    ∃ d, GuidedReach rho.graph a (rho.target.pick a) ∧
      rho.graph.par (rho.target.pick a) = some d ∧ d ∈ A ∧
      rootStep R (rho.target.pick a) d ∧ EqvOn A rho.graph.par a d ∧
      ¬ EqvOn A rho.graph.par b d ∧ ¬ BarReachOn A R a d := by
  have hguided : GuidedReach rho.graph a (rho.target.pick a) := by
    rcases rho.guided_or_nf ha with h | hnf
    · exact h
    · exact (hmissing (hmax.rootStep_of_guided_to_root hA hR ha hb
        Relation.ReflTransGen.refl hnf hroot)).elim
  cases hp : rho.graph.par (rho.target.pick a) with
  | none =>
      exact (hmissing
        (hmax.rootStep_of_guided_to_root hA hR ha hb hguided hp hroot)).elim
  | some d =>
      have ht := rho.target.pick_mem ha
      have hd := (rho.graph.mem_edge hp).2
      obtain ⟨v, _, hv⟩ := rho.target.redex_if_available ha
        ⟨a, b, ha, hb, BarReachOn.refl a, hroot⟩
      have htargetRoot := rho.target_parent_is_rootStep hR ha hp hv
      have had : EqvOn A rho.graph.par a d :=
        EqvOn.trans (EqvOn.of_reach ha ht hguided.toReach)
          (EqvOn.of_reach ht hd (Reach.head hp (Reach.refl d)))
      refine ⟨d, hguided, rfl, hd, htargetRoot, had, ?_,
        rho.target_edge_exits_fiber ha hp⟩
      intro hbd
      exact hmissing (EqvOn.trans had (EqvOn.symm hbd))

/-- Theorem 37 converts a missing rewrite into a failed argument relation on
an actual edge of the path from its source to the selected target. -/
theorem TermTargetedPGraph.missing_root_has_bad_fiber_step
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hroot : rootStep R a b) (hmissing : ¬ EqvOn A rho.graph.par a b) :
    ∃ d, GuidedReach rho.graph a (rho.target.pick a) ∧
      rho.graph.par (rho.target.pick a) = some d ∧
      rootStep R (rho.target.pick a) d ∧ EqvOn A rho.graph.par a d ∧
      ¬ EqvOn A rho.graph.par b d ∧
      ∃ u v, BarReachOn A R a u ∧ BarStepOn A R u v ∧
        BarReachOn A R v (rho.target.pick a) ∧
        ¬ barRel (EqvOn A rho.graph.par) u v := by
  obtain ⟨d, hguided, hp, hd, htargetRoot, had, hbd, _⟩ :=
    rho.missing_root_has_target_exit hA hR hmax ha hb hroot hmissing
  have hnot : ¬ barRel (EqvOn A rho.graph.par) a (rho.target.pick a) := by
    intro hbar
    have hCT : CT (EqvOn A rho.graph.par) b d :=
      thm37 (E := EqvOn A rho.graph.par) hR hstrong
        (fun _ _ h => EqvOn.symm h) (fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂)
        (rho.constructorCompatible_eqvOn hA hR) hroot hbar htargetRoot
    exact hbd (rho.eqvOn_of_CT_of_complete hA hR hmax.complete hb hd hCT)
  have hne : a ≠ rho.target.pick a := by
    intro he
    apply hnot
    rw [← he]
    exact barRel_eqvOn_refl_of_rootStep hA hR ha hroot
  have hbad := (rho.target.inFiber ha).eq_or_barRel_or_bad_step (rho := rho.graph)
  rcases hbad with he | hbar | hbad
  · exact (hne he).elim
  · exact (hnot hbar).elim
  · exact ⟨d, hguided, hp, htargetRoot, had, hbd, hbad⟩

/-- The obstruction contains actual source and target paths, an actual target
rewrite, and a DownOn pair at one aligned argument index that the graph misses. -/
theorem TermTargetedPGraph.missing_root_has_unrepresented_argument
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (hstrong : StronglyAlmostNonOmegaOverlapping R)
    (rho : TermTargetedPGraph A R) (hmax : rho.graph.EqualityComplete)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hroot : rootStep R a b) (hmissing : ¬ EqvOn A rho.graph.par a b) :
    ∃ d, rho.graph.par (rho.target.pick a) = some d ∧
      rootStep R (rho.target.pick a) d ∧ EqvOn A rho.graph.par a d ∧
      ¬ EqvOn A rho.graph.par b d ∧
      ∃ u v, BarReachOn A R a u ∧ BarStepOn A R u v ∧
        BarReachOn A R v (rho.target.pick a) ∧
        ∃ f xp yp x y xt yt,
          u = .app (.inr f) (xp ++ x :: xt) ∧
          v = .app (.inr f) (yp ++ y :: yt) ∧
          xp.length = yp.length ∧ DownOn A R x y ∧
          ¬ EqvOn A rho.graph.par x y := by
  obtain ⟨d, _, hp, hrootT, had, hbd, u, v, hpre, hstep, hsuf, hbad⟩ :=
    rho.missing_root_has_bad_fiber_step hA hR hstrong hmax ha hb hroot hmissing
  exact ⟨d, hp, hrootT, had, hbd, u, v, hpre, hstep, hsuf,
    hstep.exists_unrepresented_argument hbad⟩


end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.FiberArgsRepresented
#check @OperatorKO7.Meta.UniqueNormalization.barRel_eqvOn_trans
#check @OperatorKO7.Meta.UniqueNormalization.FiberArgsRepresented.barRel_of_barReachOn
#check @OperatorKO7.Meta.UniqueNormalization.barRel_eqvOn_refl_of_rootStep
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.constructorCompatible_eqvOn
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.rootStepsRepresented_of_fiberArgs
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.fiberArgsRepresented_of_universal
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.universal_iff_fiberArgsRepresented
#check @OperatorKO7.Meta.UniqueNormalization.fiberArgsRepresented_nil
#check @OperatorKO7.Meta.UniqueNormalization.fiberArgsRepresented_of_all_conTopped

#print axioms OperatorKO7.Meta.UniqueNormalization.FiberArgsRepresented
#print axioms OperatorKO7.Meta.UniqueNormalization.barRel_eqvOn_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberArgsRepresented.barRel_of_barReachOn
#print axioms OperatorKO7.Meta.UniqueNormalization.barRel_eqvOn_refl_of_rootStep
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.constructorCompatible_eqvOn
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.rootStepsRepresented_of_fiberArgs
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.fiberArgsRepresented_of_universal
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.universal_iff_fiberArgsRepresented
#print axioms OperatorKO7.Meta.UniqueNormalization.fiberArgsRepresented_nil
#print axioms OperatorKO7.Meta.UniqueNormalization.fiberArgsRepresented_of_all_conTopped
