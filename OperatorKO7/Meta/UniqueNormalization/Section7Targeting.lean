import OperatorKO7.Meta.UniqueNormalization.Lemma52

/-!
# Section 7 targeting interface

This module formalizes the finite targeting objects used immediately after
Lemma 56 in Kahrs and Smith, FSCD 2016, Section 7. The source definitions are
frozen in `Distinction_Boundary/Roadmaps/klop/definitions.md`, D14.

The destructor-fiber relation is the reflexive-transitive closure of the
Sigma_d tilde of `DownOn A R`. A target chooses one representative per fiber,
and chooses a root redex whenever that fiber contains one. A targeted proof
graph then records the two source conditions connecting graph edges to targets.

This module does not assume transitivity of `DownOn`, universality, or Lemma 64.
It establishes the equivalence laws of destructor fibers and the source's key
constructor-fiber sanity fact: constructor-topped members have singleton fibers,
so their target is forced to be the member itself and their fiber contains no
root redex.

Trust: kernel checked. No proof holes, native evaluation, unsafe definitions, or
new axioms are used. Public axiom footprints are reported at the end.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Definition 57 comes from `Lemma52`

`BarStepOn`, `BarReachOn`, `BarStepOn.symm`, `BarReachOn.trans` and
`BarReachOn.symm` are declared once, in
`OperatorKO7.Meta.UniqueNormalization.Lemma52`, which this module imports. This
module adds the three closure lemmas that Section 7 needs and that the inductive
presentation there does not supply. -/

/-- One destructor-fiber edge is a fiber path.

Relation: `BarStepOn` (Definition 57 destructor edge on the finite coalgebra).
Closure: single step into the reflexive-transitive fiber relation.
Strategy: not applicable.
Trust: kernel checked.
Scope: arbitrary `A` and `R`; no transitivity of `DownOn` is used. -/
theorem BarReachOn.single {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : BarStepOn A R a b) : BarReachOn A R a b :=
  BarReachOn.head h (BarReachOn.refl b)

/-- Append one destructor-fiber edge at the end of a fiber path.

Relation: `BarReachOn` followed by one `BarStepOn`.
Closure: reflexive-transitive.
Strategy: not applicable.
Trust: kernel checked.
Scope: arbitrary `A` and `R`. -/
theorem BarReachOn.tail {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b c : Term (sigma ⊕ sigma) nu}
    (hab : BarReachOn A R a b) (hbc : BarStepOn A R b c) :
    BarReachOn A R a c :=
  hab.trans (BarReachOn.single hbc)

/-- The inductive fiber relation of `Lemma52` is exactly Mathlib's
reflexive-transitive closure of `BarStepOn`. Downstream proofs may therefore use
either API without changing the represented relation.

Relation: `BarStepOn`.
Closure: reflexive-transitive, both presentations.
Strategy: not applicable.
Trust: kernel checked.
Scope: arbitrary `A` and `R`. -/
theorem barReachOn_iff_reflTransGen {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu} :
    BarReachOn A R a b ↔ Relation.ReflTransGen (BarStepOn A R) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | head hstep _ ih => exact Relation.ReflTransGen.head hstep ih
  · intro h
    induction h with
    | refl => exact BarReachOn.refl _
    | tail _ hlast ih => exact ih.tail hlast

/-- A nontrivial destructor-fiber edge cannot start at a constructor-topped term. -/
theorem not_conTopped_barStepOn_source {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : BarStepOn A R a b) : ¬ ConTopped a := by
  rcases h.2.2 with ⟨f, as, bs, ⟨d, hd⟩, ha, -, -⟩
  subst hd
  subst ha
  exact not_conTopped_destructor as

/-- Definition 57's constructor sanity fact. A constructor-topped member has a
singleton destructor fiber. -/
theorem BarReachOn.eq_of_conTopped {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (hca : ConTopped a) (h : BarReachOn A R a b) : a = b := by
  cases h with
  | refl => rfl
  | head hstep _ =>
      exact False.elim ((not_conTopped_barStepOn_source hstep) hca)

/-- A fiber contains a root redex when one of its members has a root step. -/
def HasRootRedexInFiber (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) (t : Term (sigma ⊕ sigma) nu) : Prop :=
  ∃ u v : Term (sigma ⊕ sigma) nu,
    u ∈ A ∧ v ∈ A ∧ BarReachOn A R t u ∧ rootStep R u v

/-- Definition 58, represented on term-indexed fibers. `respectsFiber` is the
well-definedness condition that makes `pick` a function on `D_A`, rather than on
chosen representatives. -/
structure Section7Target (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) where
  /-- Selected representative of the destructor fiber of a term. -/
  pick : Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu
  /-- Targets of members stay in the finite coalgebra. -/
  pick_mem : ∀ {t}, t ∈ A → pick t ∈ A
  /-- The selected representative lies in the same destructor fiber. -/
  inFiber : ∀ {t}, t ∈ A → BarReachOn A R t (pick t)
  /-- Equal destructor fibers receive one target. -/
  respectsFiber : ∀ {t u}, t ∈ A → u ∈ A → BarReachOn A R t u → pick t = pick u
  /-- If a fiber has a root redex, its target is itself a root redex. -/
  redex_if_available : ∀ {t}, t ∈ A → HasRootRedexInFiber A R t →
    ∃ v : Term (sigma ⊕ sigma) nu, v ∈ A ∧ rootStep R (pick t) v

/-- The target of a constructor-topped member is forced to be that member. -/
theorem Section7Target.pick_eq_self_of_conTopped
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (target : Section7Target A R) {t : Term (sigma ⊕ sigma) nu}
    (ht : t ∈ A) (hct : ConTopped t) : target.pick t = t := by
  exact (BarReachOn.eq_of_conTopped hct (target.inFiber ht)).symm

/-- Definition 57's second constructor sanity fact. Under constructor rules, a
constructor-topped member's destructor fiber contains no root redex. -/
theorem no_rootRedexInFiber_of_conTopped {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {t : Term (sigma ⊕ sigma) nu} (hct : ConTopped t) :
    ¬ HasRootRedexInFiber A R t := by
  rintro ⟨u, v, -, -, htu, huv⟩
  have htuEq : t = u := BarReachOn.eq_of_conTopped hct htu
  subst htuEq
  obtain ⟨d, args, htEq⟩ := rootStep_source_destructor hR huv
  subst htEq
  exact (not_conTopped_destructor args) hct

/-- Definition 59. A targeted proof graph couples a proof graph to a target and
requires every member either to reach its target using destructor-fiber parent
edges or already be a graph normal form. A parent edge leaving the target must
leave the source destructor fiber. -/
structure TermTargetedPGraph (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) where
  /-- Underlying proof graph. -/
  graph : PGraph A R
  /-- Target function on destructor fibers. -/
  target : Section7Target A R
  /-- Targeting condition 1. -/
  guided_or_nf : ∀ {t}, t ∈ A →
    GuidedReach graph t (target.pick t) ∨ graph.NF t
  /-- Targeting condition 2. -/
  target_edge_exits_fiber : ∀ {t u}, t ∈ A →
    graph.par (target.pick t) = some u → ¬ BarReachOn A R t u

/-- Definition 63. A targeted graph is universal when its represented
equivalence contains the full relativized invariant. -/
def TermTargetedPGraph.Universal {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : TermTargetedPGraph A R) : Prop :=
  ∀ {a b : Term (sigma ⊕ sigma) nu}, DownOn A R a b →
    EqvOn A rho.graph.par a b

/-- Constructor members satisfy the guided branch trivially: their target is the
member itself. This is a useful normalization of Definition 59 before Lemma 62. -/
theorem TermTargetedPGraph.constructor_guided
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TermTargetedPGraph A R) {t : Term (sigma ⊕ sigma) nu}
    (ht : t ∈ A) (hct : ConTopped t) :
    GuidedReach rho.graph t (rho.target.pick t) := by
  rw [rho.target.pick_eq_self_of_conTopped ht hct]
  exact Relation.ReflTransGen.refl

/-! ## The term-indexed reading is the quotient-typed Definition 58

`Lemma52` states Definitions 58 and 59 on the destructor quotient `D_A`, which is
the source's own typing, and proves the quotient-typed target inhabited by
`canonicalTarget`. Section 7 is easier to write on terms. The two readings are
connected here, so every Section 7 theorem below applies to the canonical
quotient-typed objects and `Section7Target` is not a fresh unwitnessed class. -/

open scoped Classical in
/-- Term-indexed reading of a quotient-typed target. Outside the coalgebra the
value is the argument itself; only the `∈ A` branch is ever used. -/
noncomputable def Target.pickAt {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    (t : Term (sigma ⊕ sigma) nu) : Term (sigma ⊕ sigma) nu :=
  if ht : t ∈ A then target.pick (barClassOf A R t ht) else t

/-- On the coalgebra the term-indexed reading is the quotient-typed target. -/
theorem Target.pickAt_of_mem {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A) :
    target.pickAt t = target.pick (barClassOf A R t ht) := by
  classical
  simp only [Target.pickAt, dif_pos ht]

/-- A quotient-typed target of Definition 58 is a term-indexed target. -/
noncomputable def Section7Target.ofTarget {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R) : Section7Target A R where
  pick := target.pickAt
  pick_mem := fun {_} ht => by
    rw [target.pickAt_of_mem ht]; exact target.pick_mem _
  inFiber := fun {t} ht => by
    rw [target.pickAt_of_mem ht]; exact target.inFiber t ht
  respectsFiber := fun {_ _} ht hu htu => by
    rw [target.pickAt_of_mem ht, target.pickAt_of_mem hu]
    exact target.pick_eq_of_barReach ht hu htu
  redex_if_available := fun {t} ht hred => by
    rw [target.pickAt_of_mem ht]
    obtain ⟨u, v, hu, hv, htu, huv⟩ := hred
    exact target.redexPriority t ht ⟨u, hu, htu, v, hv, huv⟩

@[simp] theorem Section7Target.ofTarget_pick
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (target : Target A R) {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A) :
    (Section7Target.ofTarget target).pick t = target.pick (barClassOf A R t ht) :=
  target.pickAt_of_mem ht

/-- Non-vacuity of the term-indexed Definition 58: every finite coalgebra carries
one, because `canonicalTarget` carries the quotient-typed one.

Relation: `BarReachOn` fibers of `DownOn A R`.
Closure: reflexive-transitive.
Strategy: not applicable.
Trust: kernel checked; `canonicalTarget` uses the baseline `Classical.choice`.
Scope: arbitrary `A` and `R`. -/
theorem section7Target_nonempty (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) : Nonempty (Section7Target A R) :=
  ⟨Section7Target.ofTarget (canonicalTarget A R)⟩

/-- Definition 59 in its quotient-typed form yields the term-indexed form used by
the rest of Section 7. -/
noncomputable def TargetedPGraph.toTermTargeted
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : TargetedPGraph A R) : TermTargetedPGraph A R where
  graph := rho.graph
  target := Section7Target.ofTarget rho.target
  guided_or_nf := fun {t} ht => by
    rw [Section7Target.ofTarget_pick rho.target ht]
    exact rho.guided_or_nf t ht
  target_edge_exits_fiber := fun {t u} ht hpar => by
    rw [Section7Target.ofTarget_pick rho.target ht] at hpar
    exact rho.target_exit t ht u hpar

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.BarStepOn
#check @OperatorKO7.Meta.UniqueNormalization.BarReachOn
#check @OperatorKO7.Meta.UniqueNormalization.BarStepOn.symm
#check @OperatorKO7.Meta.UniqueNormalization.BarReachOn.symm
#check @OperatorKO7.Meta.UniqueNormalization.BarReachOn.single
#check @OperatorKO7.Meta.UniqueNormalization.BarReachOn.tail
#check @OperatorKO7.Meta.UniqueNormalization.barReachOn_iff_reflTransGen
#check @OperatorKO7.Meta.UniqueNormalization.not_conTopped_barStepOn_source
#check @OperatorKO7.Meta.UniqueNormalization.BarReachOn.eq_of_conTopped
#check @OperatorKO7.Meta.UniqueNormalization.HasRootRedexInFiber
#check @OperatorKO7.Meta.UniqueNormalization.Section7Target
#check @OperatorKO7.Meta.UniqueNormalization.Section7Target.pick_eq_self_of_conTopped
#check @OperatorKO7.Meta.UniqueNormalization.no_rootRedexInFiber_of_conTopped
#check @OperatorKO7.Meta.UniqueNormalization.GuidedParentStep
#check @OperatorKO7.Meta.UniqueNormalization.GuidedReach
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.Universal
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.constructor_guided
#check @OperatorKO7.Meta.UniqueNormalization.Target.pickAt
#check @OperatorKO7.Meta.UniqueNormalization.Target.pickAt_of_mem
#check @OperatorKO7.Meta.UniqueNormalization.Section7Target.ofTarget
#check @OperatorKO7.Meta.UniqueNormalization.Section7Target.ofTarget_pick
#check @OperatorKO7.Meta.UniqueNormalization.section7Target_nonempty
#check @OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.toTermTargeted

#print axioms OperatorKO7.Meta.UniqueNormalization.BarStepOn.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.symm
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.single
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.tail
#print axioms OperatorKO7.Meta.UniqueNormalization.barReachOn_iff_reflTransGen
#print axioms OperatorKO7.Meta.UniqueNormalization.not_conTopped_barStepOn_source
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.eq_of_conTopped
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Target.pick_eq_self_of_conTopped
#print axioms OperatorKO7.Meta.UniqueNormalization.no_rootRedexInFiber_of_conTopped
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.constructor_guided
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.pickAt
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.pickAt_of_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Target.ofTarget
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Target.ofTarget_pick
#print axioms OperatorKO7.Meta.UniqueNormalization.section7Target_nonempty
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.toTermTargeted
#print axioms OperatorKO7.Meta.UniqueNormalization.HasRootRedexInFiber
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Target
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.Universal
