import OperatorKO7.Meta.ContextualCopyBudget_NoGo
import OperatorKO7.Meta.SymbolicComparatorBarrier_Weighted_Schema
import OperatorKO7.Meta.NonlinearUnconstrainedExactLaw
import OperatorKO7.Meta.LPO_KO7

/-!
# Carriers for the substrate-change rows of the RDRS coverage ledger (lane E6)

Seven rows escape by changing the substrate: the certificate lives on a transformed system with
its own carrier, not on the source term rewriting system. Each row's compiled content is the
substrate-change predicate, which says exactly what the new carrier is and why it is not `Trace`,
together with whatever the transformed side actually proves.

**Sharing.** On a directed acyclic graph the two occurrences of the payload are one node, so the
size measure that fails on trees succeeds on graphs. `sharedSizeOrients` is that measure and its
success; the tree side is the copy-budget no-go already compiled in
`Meta/ContextualCopyBudget_NoGo.lean`.

**Equational quotient.** Adding commutativity of the merge constructor as an equation identifies
two distinct root-normal forms. The witness uses two nonvoid, unequal arguments, so neither
kernel cancellation rule applies before quotienting.

**Quasi-interpretations.** A quasi-interpretation is weakly monotone and subterm bounded. Being
weakly monotone it never strictly decreases anything on its own, so it certifies no step: the
escape is its pairing with a path order, and both halves are compiled.

**Graph, process, and continuation carriers.** Each native carrier now has its own root relation on
arbitrary target terms, exact preservation and reflection on the encoded KO7 image, a decreasing
target rank, and a concrete target step whose source lies outside that image. The process and
continuation carriers are closed KO7-specific calculi; no theorem about the full pi calculus or
full lambda-mu calculus is asserted.

Relation: the schema duplicating rule and the KO7 root relation. Closure: root.
External trust: none for the KO7-specific transports proved in this module.
-/

namespace OperatorKO7.Methods.SubstrateChangeRows

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.SymbolicComparatorBarrier

/-! ## The substrate-change predicate -/

/-- What it means for a method to change substrate: its certificate is carried by a type other
than `Trace`, and the read-back loses target information. -/
structure SubstrateChange where
  /-- The carrier the certificate lives on. -/
  Carrier : Type
  /-- The reading map from the new carrier to terms. -/
  readBack : Carrier → Trace
  /-- The reading map is not injective, which is exactly why the certificate does not descend to a
  direct measure on terms. -/
  readBack_not_injective : ¬ Function.Injective readBack

/-- A substrate change that is strong enough to transport termination.  Noninjective read-back is
not the certificate; the load-bearing data are forward operational simulation and well-foundedness
of the target relation. -/
structure CertifiedSubstrateChange (SourceStep : Trace → Trace → Prop) where
  Carrier : Type
  encode : Trace → Carrier
  readBack : Carrier → Trace
  readBack_encode : ∀ t, readBack (encode t) = t
  readBack_not_injective : ¬ Function.Injective readBack
  TargetStep : Carrier → Carrier → Prop
  forward : ∀ {s t}, SourceStep s t → TargetStep (encode s) (encode t)
  target_wellFounded : WellFounded (fun y x => TargetStep x y)

/-- Operational simulation into a terminating target universally transports source termination. -/
theorem CertifiedSubstrateChange.source_wellFounded
    {SourceStep : Trace → Trace → Prop} (C : CertifiedSubstrateChange SourceStep) :
    WellFounded (fun y x => SourceStep x y) := by
  refine Subrelation.wf ?_ (InvImage.wf C.encode C.target_wellFounded)
  intro y x h
  exact C.forward h

/-- Exact operational transport on the encoded image, sound read-back on the whole target, and a
native target step whose source is outside the encoded image. -/
def ExactStrictSubstrateExtension {SourceStep : Trace → Trace → Prop}
    (C : CertifiedSubstrateChange SourceStep) : Prop :=
  (∀ {s t : Trace}, C.TargetStep (C.encode s) (C.encode t) ↔ SourceStep s t)
    ∧ (∀ {x y : C.Carrier}, C.TargetStep x y → SourceStep (C.readBack x) (C.readBack y))
    ∧ (∃ x y : C.Carrier, C.TargetStep x y ∧ ¬ ∃ t : Trace, C.encode t = x)

theorem ExactStrictSubstrateExtension.source_wellFounded
    {SourceStep : Trace → Trace → Prop} {C : CertifiedSubstrateChange SourceStep}
    (_ : ExactStrictSubstrateExtension C) :
    WellFounded (fun y x => SourceStep x y) :=
  C.source_wellFounded

/-- A two-point carrier whose read-back forgets its tag. -/
def forgetBoolReadBack : Bool → Trace := fun _ => void

theorem forgetBoolReadBack_not_injective : ¬ Function.Injective forgetBoolReadBack := by
  intro h
  have hft : false = true := h rfl
  exact Bool.false_ne_true hft

def forgetBoolSubstrate : SubstrateChange where
  Carrier := Bool
  readBack := forgetBoolReadBack
  readBack_not_injective := forgetBoolReadBack_not_injective

/-- A self-loop on the forgotten carrier. -/
def BoolSelfLoop (_ _ : Bool) : Prop := True

/-- The forgotten carrier can be nonterminating. -/
theorem boolSelfLoop_not_wellFounded :
    ¬ WellFounded (fun y x : Bool => BoolSelfLoop x y) := by
  intro h
  exact (h.asymmetric false false trivial) trivial

/-- **Sharpness of the transport interface.** Noninjective read-back by itself implies neither a
target termination theorem nor a source-to-target operational simulation. -/
theorem noninjective_readBack_alone_does_not_certify_termination :
    (¬ Function.Injective forgetBoolSubstrate.readBack) ∧
      ¬ WellFounded (fun y x : Bool => BoolSelfLoop x y) :=
  ⟨forgetBoolReadBack_not_injective, boolSelfLoop_not_wellFounded⟩

/-! ## Sharing -/

/-- A term-graph node: either a leaf, or a shared binary node whose two children may be the same
node. The sharing is what distinguishes it from `Trace`. -/
inductive SharedTerm where
  | leaf : SharedTerm
  | node : SharedTerm → SharedTerm → SharedTerm
  | shared : SharedTerm → SharedTerm
  deriving DecidableEq, Repr

/-- Size on the shared carrier: a shared node is counted once, not twice. -/
def sharedSize : SharedTerm → Nat
  | SharedTerm.leaf => 1
  | SharedTerm.node x y => 1 + sharedSize x + sharedSize y
  | SharedTerm.shared x => 1 + sharedSize x

/-- Reading a shared term back as a tree duplicates the shared node. -/
def unshare : SharedTerm → Trace
  | SharedTerm.leaf => void
  | SharedTerm.node x y => merge (unshare x) (unshare y)
  | SharedTerm.shared x => merge (unshare x) (unshare x)

/-- **The substrate really changes.** Reading back is not injective: the shared node and the
explicit duplication read back to the same tree. -/
theorem unshare_not_injective : ¬ Function.Injective unshare := by
  intro h
  have : SharedTerm.shared SharedTerm.leaf = SharedTerm.node SharedTerm.leaf SharedTerm.leaf :=
    h (by simp [unshare])
  exact SharedTerm.noConfusion this

/-- Shared and explicit duplication have exactly the same source-tree read-back. -/
theorem unshare_shared_eq_node (x : SharedTerm) :
    unshare (SharedTerm.shared x) = unshare (SharedTerm.node x x) := rfl

def sharingSubstrate : SubstrateChange where
  Carrier := SharedTerm
  readBack := unshare
  readBack_not_injective := unshare_not_injective

/-- **On the shared carrier the duplicating step is oriented.** The shared node is counted once,
so wrapping a shared node costs one instead of two, and the size strictly drops along the step
that duplicates the payload. -/
theorem sharedSize_shared_lt_node (x : SharedTerm) :
    sharedSize (SharedTerm.shared x) < sharedSize (SharedTerm.node x x) := by
  have hpos : 0 < sharedSize x := by
    cases x <;> simp [sharedSize]
  simp only [sharedSize]
  omega

/-- Factoring through read-back would make the shared size a direct source-term measure. -/
def SharedSizeFactorsThroughReadBack : Prop :=
  ∃ μ : Trace → Nat, ∀ x : SharedTerm, sharedSize x = μ (unshare x)

/-- The shared size does not factor through the source tree: equal read-backs carry unequal
shared-carrier sizes. -/
theorem sharedSize_not_factors_through_unshare : ¬ SharedSizeFactorsThroughReadBack := by
  rintro ⟨μ, hμ⟩
  have hsizes :
      sharedSize (SharedTerm.shared SharedTerm.leaf) =
        sharedSize (SharedTerm.node SharedTerm.leaf SharedTerm.leaf) := by
    calc
      sharedSize (SharedTerm.shared SharedTerm.leaf) =
          μ (unshare (SharedTerm.shared SharedTerm.leaf)) := hμ _
      _ = μ (unshare (SharedTerm.node SharedTerm.leaf SharedTerm.leaf)) :=
        congrArg μ (unshare_shared_eq_node SharedTerm.leaf)
      _ = sharedSize (SharedTerm.node SharedTerm.leaf SharedTerm.leaf) := (hμ _).symm
  exact (Nat.ne_of_lt (sharedSize_shared_lt_node SharedTerm.leaf)) hsizes

/-- **sharingNonConservativity.** The escape is real and the substrate change is real: the size
measure succeeds on the shared carrier, and the read-back map is not injective, so the success
does not descend to a direct measure on terms. The tree side is the copy-budget no-go. -/
abbrev SharingNonConservativityRowClaim : Prop :=
  (∀ x : SharedTerm, sharedSize (SharedTerm.shared x) < sharedSize (SharedTerm.node x x))
    ∧ ¬ Function.Injective unshare
    ∧ ¬ SharedSizeFactorsThroughReadBack
    ∧ ¬ (∀ {a b : Trace}, MetaSN_KO7.SafeStep a b →
        MetaSN_KO7.copyMass b ≤ MetaSN_KO7.copyMass a)

theorem sharingNonConservativity_row_anchor : SharingNonConservativityRowClaim :=
  ⟨sharedSize_shared_lt_node, unshare_not_injective, sharedSize_not_factors_through_unshare,
    MetaSN_KO7.not_copyMass_mono_safe⟩

/-! ## The equational quotient -/

/-- The two root-normal merge terms that commutativity identifies. -/
def mergeLeft : Trace := merge (delta void) (integrate void)

def mergeRight : Trace := merge (integrate void) (delta void)

/-- They are distinct terms. -/
theorem merge_terms_distinct : mergeLeft ≠ mergeRight := by
  intro h
  simp [mergeLeft, mergeRight] at h

/-- Root normality for the kernel relation. -/
def RootNormal (t : Trace) : Prop := ∀ u : Trace, ¬ Step t u

theorem mergeLeft_rootNormal : RootNormal mergeLeft := by
  intro u h
  cases h

theorem mergeRight_rootNormal : RootNormal mergeRight := by
  intro u h
  cases h

/-- The equation added by the quotient, isolated from syntactic equality. -/
inductive MergeCommutativityEquation : Trace → Trace → Prop
  | swap (x y : Trace) :
      MergeCommutativityEquation (merge x y) (merge y x)

theorem merge_commutativity_identifies_witness :
    MergeCommutativityEquation mergeLeft mergeRight := by
  exact MergeCommutativityEquation.swap (delta void) (integrate void)

/-- **equationalQuotientNonConservativity.** Adding merge commutativity identifies two syntactically
distinct root-normal forms of the original kernel. This is the direct normal-form witness that the
quotient is not conservative over root normal forms. -/
abbrev EquationalQuotientNonConservativityRowClaim : Prop :=
  mergeLeft ≠ mergeRight
    ∧ RootNormal mergeLeft
    ∧ RootNormal mergeRight
    ∧ MergeCommutativityEquation mergeLeft mergeRight

theorem equationalQuotientNonConservativity_row_anchor :
    EquationalQuotientNonConservativityRowClaim := by
  exact ⟨merge_terms_distinct, mergeLeft_rootNormal, mergeRight_rootNormal,
    merge_commutativity_identifies_witness⟩

/-! ## Quasi-interpretations -/

/-- A quasi-interpretation: weakly monotone in each argument and bounded below by each argument.
Being weakly monotone, it never strictly decreases anything by itself. -/
structure QuasiInterpretation where
  eval : Trace → Nat
  subterm_bounded_left : ∀ x y, eval x ≤ eval (merge x y)
  subterm_bounded_right : ∀ x y, eval y ≤ eval (merge x y)
  weakly_monotone : ∀ b s n, eval (app s (recΔ b s n)) ≤ eval (recΔ b s (delta n))

/-- The trivial quasi-interpretation exists, so the notion is not empty. -/
def constantQuasiInterpretation : QuasiInterpretation where
  eval := fun _ => 0
  subterm_bounded_left := fun _ _ => le_refl 0
  subterm_bounded_right := fun _ _ => le_refl 0
  weakly_monotone := fun _ _ _ => le_refl 0

/-- **A quasi-interpretation alone certifies no step.** Weak monotonicity is compatible with
equality everywhere, and the constant interpretation realizes that, so no strict descent follows
from the quasi-interpretation conditions. -/
theorem quasiInterpretation_axioms_do_not_force_strict :
    ¬ ∀ Q : QuasiInterpretation, ∀ b s n : Trace,
        Q.eval (app s (recΔ b s n)) < Q.eval (recΔ b s (delta n)) := by
  intro h
  have := h constantQuasiInterpretation void void void
  simp [constantQuasiInterpretation] at this

/-- Backward-compatible name.  The exact statement is non-entailment by the axioms, not a claim
that every quasi-interpretation is non-strict. -/
theorem quasiInterpretation_never_strict :
    ¬ ∀ Q : QuasiInterpretation, ∀ b s n : Trace,
        Q.eval (app s (recΔ b s n)) < Q.eval (recΔ b s (delta n)) :=
  quasiInterpretation_axioms_do_not_force_strict

/-- A sharing-aware termination certificate pairs a quasi-interpretation with a separate strict,
well-founded order. -/
structure QuasiInterpretationPathPair where
  quasi : QuasiInterpretation
  gt : Trace → Trace → Prop
  gt_transitive : Transitive gt
  gt_wellFounded : WellFounded (fun y x => gt x y)
  step_orients : ∀ {s t : Trace}, Step s t → gt s t

/-- The concrete KO7 pair: the constant quasi-interpretation supplies weak size information and
the compiled LPO supplies all strict descent. -/
def ko7QuasiInterpretationPathPair : QuasiInterpretationPathPair where
  quasi := constantQuasiInterpretation
  gt := OperatorKO7.MetaLPO.LPOOrder_KO7
  gt_transitive := OperatorKO7.MetaLPO.lpoOrder_KO7_transitive
  gt_wellFounded :=
    InvImage.wf OperatorKO7.MetaLPO.encode OperatorKO7.LPOSchema.lpoOrder_wellFounded
  step_orients := OperatorKO7.MetaLPO.lpoOrder_orients_step

/-- **quasiInterpretationsSharingAware.** The escape is the pairing of a quasi-interpretation with
a path order: the quasi-interpretation bounds the sizes and the path order supplies the strict
descent. Both halves are compiled, and the first alone is shown insufficient. -/
abbrev QuasiInterpretationsSharingAwareRowClaim : Prop :=
  (∀ x y : Trace,
      constantQuasiInterpretation.eval x ≤ constantQuasiInterpretation.eval (merge x y))
    ∧ (¬ ∀ Q : QuasiInterpretation, ∀ b s n : Trace,
        Q.eval (app s (recΔ b s n)) < Q.eval (recΔ b s (delta n)))
    ∧ ko7QuasiInterpretationPathPair.quasi = constantQuasiInterpretation
    ∧ WellFounded (fun y x => ko7QuasiInterpretationPathPair.gt x y)
    ∧ (∀ {a b : Trace}, Step a b → ko7QuasiInterpretationPathPair.gt a b)

theorem quasiInterpretationsSharingAware_row_anchor :
    QuasiInterpretationsSharingAwareRowClaim :=
  ⟨constantQuasiInterpretation.subterm_bounded_left,
    quasiInterpretation_axioms_do_not_force_strict, rfl,
    ko7QuasiInterpretationPathPair.gt_wellFounded,
    ko7QuasiInterpretationPathPair.step_orients⟩

/-! ## Carriers that are not the term algebra -/

/-- A weighted type graph: states, a labelled transition structure, and a weight. The carrier is
the graph, and reading it back as a term forgets the state, so the read-back map is not
injective. -/
inductive GraphNode where
  | state : Nat → GraphNode
  | edge : GraphNode → GraphNode → GraphNode
  deriving DecidableEq, Repr

/-- Structural graph encoding.  No graph node contains a `Trace`; constructor identity is carried
by finite state tags and argument incidence by edges. -/
@[simp] def graphEncode : Trace → GraphNode
  | .void => .state 0
  | .delta t => .edge (.state 1) (graphEncode t)
  | .integrate t => .edge (.state 2) (graphEncode t)
  | .merge a b => .edge (.edge (.state 3) (graphEncode a)) (graphEncode b)
  | .app a b => .edge (.edge (.state 4) (graphEncode a)) (graphEncode b)
  | .recΔ b s n =>
      .edge (.edge (.edge (.state 5) (graphEncode b)) (graphEncode s)) (graphEncode n)
  | .eqW a b => .edge (.edge (.state 6) (graphEncode a)) (graphEncode b)

/-- Total read-back.  Well-formed structural codes decode constructorwise; malformed graph
shapes read back to `void`. -/
@[simp] def graphReadBack : GraphNode → Trace
  | .state 0 => .void
  | .edge (.state 1) t => .delta (graphReadBack t)
  | .edge (.state 2) t => .integrate (graphReadBack t)
  | .edge (.edge (.state 3) a) b => .merge (graphReadBack a) (graphReadBack b)
  | .edge (.edge (.state 4) a) b => .app (graphReadBack a) (graphReadBack b)
  | .edge (.edge (.edge (.state 5) b) s) n =>
      .recΔ (graphReadBack b) (graphReadBack s) (graphReadBack n)
  | .edge (.edge (.state 6) a) b => .eqW (graphReadBack a) (graphReadBack b)
  | _ => .void

@[simp] theorem graphReadBack_graphEncode (t : Trace) : graphReadBack (graphEncode t) = t := by
  induction t <;> simp [graphEncode, graphReadBack, *]

theorem graphEncode_injective : Function.Injective graphEncode := by
  intro a b h
  have := congrArg graphReadBack h
  simpa using this

/-- The encoded graph image.  Restricting to this subtype removes malformed graph codes. -/
def EncodedGraphNode := {g : GraphNode // ∃ t : Trace, graphEncode t = g}

/-- The structural graph encoding is an exact equivalence onto its image. -/
def graphImageEquiv : Trace ≃ EncodedGraphNode where
  toFun t := ⟨graphEncode t, ⟨t, rfl⟩⟩
  invFun g := graphReadBack g.1
  left_inv := graphReadBack_graphEncode
  right_inv := by
    rintro ⟨g, t, rfl⟩
    apply Subtype.ext
    simp

theorem graphReadBack_not_injective : ¬ Function.Injective graphReadBack := by
  intro h
  have h01 : GraphNode.state 0 = GraphNode.state 1 := h rfl
  simp at h01

def typeGraphSubstrate : SubstrateChange where
  Carrier := GraphNode
  readBack := graphReadBack
  readBack_not_injective := graphReadBack_not_injective

/-- Native graph reduction. The eight constructors act on arbitrary graph nodes, not only nodes in
the encoded image, and none accepts either a source term or a `Step` proof as input. -/
inductive GraphLiftStep : GraphNode → GraphNode → Prop
  | intDelta (t : GraphNode) :
      GraphLiftStep (.edge (.state 2) (.edge (.state 1) t)) (.state 0)
  | mergeVoidLeft (t : GraphNode) :
      GraphLiftStep (.edge (.edge (.state 3) (.state 0)) t) t
  | mergeVoidRight (t : GraphNode) :
      GraphLiftStep (.edge (.edge (.state 3) t) (.state 0)) t
  | mergeCancel (t : GraphNode) :
      GraphLiftStep (.edge (.edge (.state 3) t) t) t
  | recZero (b s : GraphNode) :
      GraphLiftStep (.edge (.edge (.edge (.state 5) b) s) (.state 0)) b
  | recSucc (b s n : GraphNode) :
      GraphLiftStep (.edge (.edge (.edge (.state 5) b) s) (.edge (.state 1) n))
        (.edge (.edge (.state 4) s) (.edge (.edge (.edge (.state 5) b) s) n))
  | eqRefl (a : GraphNode) :
      GraphLiftStep (.edge (.edge (.state 6) a) a) (.state 0)
  | eqDiff (a b : GraphNode) :
      GraphLiftStep (.edge (.edge (.state 6) a) b)
        (.edge (.state 2) (.edge (.edge (.state 3) a) b))

theorem graphLiftStep_readBack :
    ∀ {x y : GraphNode}, GraphLiftStep x y → Step (graphReadBack x) (graphReadBack y)
  | _, _, GraphLiftStep.intDelta t => by
      simpa using Step.R_int_delta (graphReadBack t)
  | _, _, GraphLiftStep.mergeVoidLeft t => by
      simpa using Step.R_merge_void_left (graphReadBack t)
  | _, _, GraphLiftStep.mergeVoidRight t => by
      simpa using Step.R_merge_void_right (graphReadBack t)
  | _, _, GraphLiftStep.mergeCancel t => by
      simpa using Step.R_merge_cancel (graphReadBack t)
  | _, _, GraphLiftStep.recZero b s => by
      simpa using Step.R_rec_zero (graphReadBack b) (graphReadBack s)
  | _, _, GraphLiftStep.recSucc b s n => by
      simpa using Step.R_rec_succ (graphReadBack b) (graphReadBack s) (graphReadBack n)
  | _, _, GraphLiftStep.eqRefl a => by
      simpa using Step.R_eq_refl (graphReadBack a)
  | _, _, GraphLiftStep.eqDiff a b => by
      simpa using Step.R_eq_diff (graphReadBack a) (graphReadBack b)

/-- Exact encoding of every KO7 root step into the native graph relation. -/
theorem step_to_graphLiftStep_encode :
    ∀ {s t : Trace}, Step s t → GraphLiftStep (graphEncode s) (graphEncode t)
  | _, _, Step.R_int_delta t => GraphLiftStep.intDelta (graphEncode t)
  | _, _, Step.R_merge_void_left t => GraphLiftStep.mergeVoidLeft (graphEncode t)
  | _, _, Step.R_merge_void_right t => GraphLiftStep.mergeVoidRight (graphEncode t)
  | _, _, Step.R_merge_cancel t => GraphLiftStep.mergeCancel (graphEncode t)
  | _, _, Step.R_rec_zero b s => GraphLiftStep.recZero (graphEncode b) (graphEncode s)
  | _, _, Step.R_rec_succ b s n =>
      GraphLiftStep.recSucc (graphEncode b) (graphEncode s) (graphEncode n)
  | _, _, Step.R_eq_refl a => GraphLiftStep.eqRefl (graphEncode a)
  | _, _, Step.R_eq_diff a b => GraphLiftStep.eqDiff (graphEncode a) (graphEncode b)

theorem graphLiftStep_iff {s t : Trace} :
    GraphLiftStep (graphEncode s) (graphEncode t) ↔ Step s t :=
  ⟨fun h => by simpa using graphLiftStep_readBack h, step_to_graphLiftStep_encode⟩

/-- On the well-formed image, graph reduction is relation-isomorphic to KO7 root rewriting. -/
theorem graphImageEquiv_step_iff {s t : Trace} :
    GraphLiftStep (graphImageEquiv s).1 (graphImageEquiv t).1 ↔ Step s t :=
  graphLiftStep_iff

/-- A graph state that no source term encodes. -/
def graphForeign : GraphNode := .state 7

theorem graphForeign_not_encoded : ¬ ∃ t : Trace, graphEncode t = graphForeign := by
  rintro ⟨t, ht⟩
  have htVoid : t = .void := by
    simpa [graphForeign] using congrArg graphReadBack ht
  subst t
  simp [graphForeign] at ht

/-- A native graph redex outside the source image. -/
def graphForeignSource : GraphNode :=
  .edge (.state 2) (.edge (.state 1) graphForeign)

theorem graphForeignSource_not_encoded :
    ¬ ∃ t : Trace, graphEncode t = graphForeignSource := by
  rintro ⟨t, ht⟩
  have htShape : t = .integrate (.delta .void) := by
    simpa [graphForeignSource, graphForeign] using congrArg graphReadBack ht
  subst t
  simp [graphForeignSource, graphForeign] at ht

/-- The target graph relation is a strict operational extension of the encoded source image. -/
theorem graphLiftStep_has_foreign_source :
    GraphLiftStep graphForeignSource (.state 0)
      ∧ ¬ ∃ t : Trace, graphEncode t = graphForeignSource :=
  ⟨GraphLiftStep.intDelta graphForeign, graphForeignSource_not_encoded⟩

/-- The graph weight is the compiled polynomial rank read through the structural decoder. -/
def graphWeight (g : GraphNode) : Nat := OperatorKO7.PolyInterpretation.W (graphReadBack g)

theorem graphLiftStep_weight_decreases {x y : GraphNode} (h : GraphLiftStep x y) :
    graphWeight y < graphWeight x :=
  OperatorKO7.PolyInterpretation.W_orients_step (graphLiftStep_readBack h)

theorem graphLiftStep_wellFounded :
    WellFounded (fun y x : GraphNode => GraphLiftStep x y) := by
  refine Subrelation.wf ?_
    (InvImage.wf graphReadBack OperatorKO7.PolyInterpretation.wf_StepRev_poly)
  intro y x h
  exact graphLiftStep_readBack h

/-- Exact KO7 graph-carrier transport. -/
def weightedTypeGraphTransport : CertifiedSubstrateChange Step where
  Carrier := GraphNode
  encode := graphEncode
  readBack := graphReadBack
  readBack_encode := graphReadBack_graphEncode
  readBack_not_injective := graphReadBack_not_injective
  TargetStep := GraphLiftStep
  forward := graphLiftStep_iff.mpr
  target_wellFounded := graphLiftStep_wellFounded

/-- **weightedTypeGraphEscape.** The graph carrier now carries an exact KO7 operational lift, a
left inverse on the encoded image, target well-foundedness, and the induced source theorem.  This
is the complete transport interface required of any weighted type-graph implementation; no
conclusion is drawn from noninjectivity alone. -/
abbrev WeightedTypeGraphEscapeRowClaim : Prop :=
  Function.Injective graphEncode
    ∧ Nonempty (Trace ≃ EncodedGraphNode)
    ∧ (∀ t, graphReadBack (graphEncode t) = t)
    ∧ (∀ {s t}, Step s t ↔ GraphLiftStep (graphEncode s) (graphEncode t))
    ∧ (∀ {x y}, GraphLiftStep x y → graphWeight y < graphWeight x)
    ∧ WellFounded (fun y x : GraphNode => GraphLiftStep x y)
    ∧ (∃ x y : GraphNode,
      GraphLiftStep x y ∧ ¬ ∃ t : Trace, graphEncode t = x)
    ∧ ¬ Function.Injective graphReadBack
    ∧ WellFounded (fun y x : Trace => Step x y)

theorem weightedTypeGraphEscape_row_anchor : WeightedTypeGraphEscapeRowClaim :=
  ⟨graphEncode_injective, ⟨graphImageEquiv⟩, graphReadBack_graphEncode,
    fun {_ _} => graphLiftStep_iff.symm, graphLiftStep_weight_decreases,
    graphLiftStep_wellFounded,
    ⟨graphForeignSource, .state 0, graphLiftStep_has_foreign_source⟩,
    graphReadBack_not_injective,
    weightedTypeGraphTransport.source_wellFounded⟩

/-- A graph carrier with an arbitrary auxiliary label. -/
abbrev LabelledGraphNode (Label : Type) := Label × GraphNode

def labelledGraphEncode {Label : Type} (label : Label) (t : Trace) :
    LabelledGraphNode Label :=
  (label, graphEncode t)

def labelledGraphReadBack {Label : Type} (x : LabelledGraphNode Label) : Trace :=
  graphReadBack x.2

@[simp] theorem labelledGraphReadBack_encode {Label : Type} (label : Label) (t : Trace) :
    labelledGraphReadBack (labelledGraphEncode label t) = t :=
  graphReadBack_graphEncode t

theorem labelledGraphEncode_injective {Label : Type} (label : Label) :
    Function.Injective (labelledGraphEncode label) := by
  intro s t h
  have := congrArg labelledGraphReadBack h
  simpa using this

/-- Native labelled graph reduction preserves the auxiliary label. -/
inductive LabelledGraphStep {Label : Type} :
    LabelledGraphNode Label → LabelledGraphNode Label → Prop
  | lift (label : Label) {x y : GraphNode} :
      GraphLiftStep x y → LabelledGraphStep (label, x) (label, y)

theorem labelledGraphStep_encode_iff {Label : Type} (label : Label) {s t : Trace} :
    LabelledGraphStep (labelledGraphEncode label s) (labelledGraphEncode label t) ↔
      Step s t := by
  constructor
  · intro h
    cases h with
    | lift _ hxy => exact graphLiftStep_iff.mp hxy
  · intro h
    exact LabelledGraphStep.lift label (graphLiftStep_iff.mpr h)

def labelledGraphRank {Label : Type} (x : LabelledGraphNode Label) : Nat :=
  graphWeight x.2

theorem labelledGraphStep_rank_decreases {Label : Type} {x y : LabelledGraphNode Label}
    (h : LabelledGraphStep x y) : labelledGraphRank y < labelledGraphRank x := by
  cases h with
  | lift _ hxy => exact graphLiftStep_weight_decreases hxy

theorem labelledGraphStep_wellFounded {Label : Type} :
    WellFounded (fun y x : LabelledGraphNode Label => LabelledGraphStep x y) := by
  refine Subrelation.wf ?_ (InvImage.wf labelledGraphRank Nat.lt_wfRel.wf)
  intro y x h
  exact labelledGraphStep_rank_decreases h

/-- Auxiliary labels are genuinely additional target information: read-back forgets them. -/
theorem boolLabelledGraphReadBack_not_injective :
    ¬ Function.Injective (labelledGraphReadBack (Label := Bool)) := by
  intro h
  have hbad :
      (false, GraphNode.state 0) = (true, GraphNode.state 0) := h rfl
  simp at hbad

/-- **generalizedWeightedTypeGraphs.** Every labelled extension carries an injective KO7 image,
exact step transport on that image, and a well-founded native target relation. The Boolean instance
also proves that the generalized carrier contains information erased by read-back. -/
abbrev GeneralizedWeightedTypeGraphsRowClaim : Prop :=
  (∀ (Label : Type) (label : Label),
      Function.Injective (labelledGraphEncode label)
        ∧ (∀ s t : Trace,
          Step s t ↔
            LabelledGraphStep (labelledGraphEncode label s) (labelledGraphEncode label t))
        ∧ WellFounded
          (fun y x : LabelledGraphNode Label => LabelledGraphStep x y))
    ∧ ¬ Function.Injective (labelledGraphReadBack (Label := Bool))

theorem generalizedWeightedTypeGraphs_row_anchor : GeneralizedWeightedTypeGraphsRowClaim :=
  ⟨fun _ label =>
      ⟨labelledGraphEncode_injective label,
        fun _ _ => (labelledGraphStep_encode_iff label).symm,
        labelledGraphStep_wellFounded⟩,
    boolLabelledGraphReadBack_not_injective⟩

/-- A process term: the carrier of the pi-calculus translation. Reading it back forgets the
channel names. -/
inductive ProcessTerm where
  | nil : ProcessTerm
  | par : ProcessTerm → ProcessTerm → ProcessTerm
  | send : Nat → ProcessTerm → ProcessTerm
  deriving DecidableEq, Repr

/-- Structural channel encoding; no process constructor stores a source trace. -/
@[simp] def processEncode : Trace → ProcessTerm
  | .void => .nil
  | .delta t => .send 0 (processEncode t)
  | .integrate t => .send 1 (processEncode t)
  | .merge a b => .send 2 (.par (processEncode a) (processEncode b))
  | .app a b => .send 3 (.par (processEncode a) (processEncode b))
  | .recΔ b s n => .send 4 (.par (processEncode b) (.par (processEncode s) (processEncode n)))
  | .eqW a b => .send 5 (.par (processEncode a) (processEncode b))

@[simp] def processReadBack : ProcessTerm → Trace
  | .nil => .void
  | .send 0 t => .delta (processReadBack t)
  | .send 1 t => .integrate (processReadBack t)
  | .send 2 (.par a b) => .merge (processReadBack a) (processReadBack b)
  | .send 3 (.par a b) => .app (processReadBack a) (processReadBack b)
  | .send 4 (.par b (.par s n)) =>
      .recΔ (processReadBack b) (processReadBack s) (processReadBack n)
  | .send 5 (.par a b) => .eqW (processReadBack a) (processReadBack b)
  | _ => .void

@[simp] theorem processReadBack_processEncode (t : Trace) :
    processReadBack (processEncode t) = t := by
  induction t <;> simp [processEncode, processReadBack, *]

theorem processEncode_injective : Function.Injective processEncode := by
  intro a b h
  have := congrArg processReadBack h
  simpa using this

def EncodedProcessTerm := {p : ProcessTerm // ∃ t : Trace, processEncode t = p}

def processImageEquiv : Trace ≃ EncodedProcessTerm where
  toFun t := ⟨processEncode t, ⟨t, rfl⟩⟩
  invFun p := processReadBack p.1
  left_inv := processReadBack_processEncode
  right_inv := by
    rintro ⟨p, t, rfl⟩
    apply Subtype.ext
    simp

theorem processReadBack_not_injective : ¬ Function.Injective processReadBack := by
  intro h
  have hbad : ProcessTerm.nil = ProcessTerm.par ProcessTerm.nil ProcessTerm.nil := h rfl
  exact ProcessTerm.noConfusion hbad

inductive ProcessLiftStep : ProcessTerm → ProcessTerm → Prop
  | intDelta (t : ProcessTerm) :
      ProcessLiftStep (.send 1 (.send 0 t)) .nil
  | mergeVoidLeft (t : ProcessTerm) :
      ProcessLiftStep (.send 2 (.par .nil t)) t
  | mergeVoidRight (t : ProcessTerm) :
      ProcessLiftStep (.send 2 (.par t .nil)) t
  | mergeCancel (t : ProcessTerm) :
      ProcessLiftStep (.send 2 (.par t t)) t
  | recZero (b s : ProcessTerm) :
      ProcessLiftStep (.send 4 (.par b (.par s .nil))) b
  | recSucc (b s n : ProcessTerm) :
      ProcessLiftStep (.send 4 (.par b (.par s (.send 0 n))))
        (.send 3 (.par s (.send 4 (.par b (.par s n)))))
  | eqRefl (a : ProcessTerm) :
      ProcessLiftStep (.send 5 (.par a a)) .nil
  | eqDiff (a b : ProcessTerm) :
      ProcessLiftStep (.send 5 (.par a b)) (.send 1 (.send 2 (.par a b)))

theorem processLiftStep_readBack :
    ∀ {x y : ProcessTerm}, ProcessLiftStep x y → Step (processReadBack x) (processReadBack y)
  | _, _, ProcessLiftStep.intDelta t => by
      simpa using Step.R_int_delta (processReadBack t)
  | _, _, ProcessLiftStep.mergeVoidLeft t => by
      simpa using Step.R_merge_void_left (processReadBack t)
  | _, _, ProcessLiftStep.mergeVoidRight t => by
      simpa using Step.R_merge_void_right (processReadBack t)
  | _, _, ProcessLiftStep.mergeCancel t => by
      simpa using Step.R_merge_cancel (processReadBack t)
  | _, _, ProcessLiftStep.recZero b s => by
      simpa using Step.R_rec_zero (processReadBack b) (processReadBack s)
  | _, _, ProcessLiftStep.recSucc b s n => by
      simpa using Step.R_rec_succ (processReadBack b) (processReadBack s) (processReadBack n)
  | _, _, ProcessLiftStep.eqRefl a => by
      simpa using Step.R_eq_refl (processReadBack a)
  | _, _, ProcessLiftStep.eqDiff a b => by
      simpa using Step.R_eq_diff (processReadBack a) (processReadBack b)

/-- Exact encoding of every KO7 root step into the native process relation. -/
theorem step_to_processLiftStep_encode :
    ∀ {s t : Trace}, Step s t → ProcessLiftStep (processEncode s) (processEncode t)
  | _, _, Step.R_int_delta t => ProcessLiftStep.intDelta (processEncode t)
  | _, _, Step.R_merge_void_left t => ProcessLiftStep.mergeVoidLeft (processEncode t)
  | _, _, Step.R_merge_void_right t => ProcessLiftStep.mergeVoidRight (processEncode t)
  | _, _, Step.R_merge_cancel t => ProcessLiftStep.mergeCancel (processEncode t)
  | _, _, Step.R_rec_zero b s => ProcessLiftStep.recZero (processEncode b) (processEncode s)
  | _, _, Step.R_rec_succ b s n =>
      ProcessLiftStep.recSucc (processEncode b) (processEncode s) (processEncode n)
  | _, _, Step.R_eq_refl a => ProcessLiftStep.eqRefl (processEncode a)
  | _, _, Step.R_eq_diff a b => ProcessLiftStep.eqDiff (processEncode a) (processEncode b)

theorem processLiftStep_iff {s t : Trace} :
    ProcessLiftStep (processEncode s) (processEncode t) ↔ Step s t :=
  ⟨fun h => by simpa using processLiftStep_readBack h, step_to_processLiftStep_encode⟩

theorem processImageEquiv_step_iff {s t : Trace} :
    ProcessLiftStep (processImageEquiv s).1 (processImageEquiv t).1 ↔ Step s t :=
  processLiftStep_iff

/-- A process state outside the closed encoding image. -/
def processForeign : ProcessTerm := .send 99 .nil

theorem processForeign_not_encoded : ¬ ∃ t : Trace, processEncode t = processForeign := by
  rintro ⟨t, ht⟩
  have htVoid : t = .void := by
    simpa [processForeign] using congrArg processReadBack ht
  subst t
  simp [processForeign] at ht

def processForeignSource : ProcessTerm := .send 1 (.send 0 processForeign)

theorem processForeignSource_not_encoded :
    ¬ ∃ t : Trace, processEncode t = processForeignSource := by
  rintro ⟨t, ht⟩
  have htShape : t = .integrate (.delta .void) := by
    simpa [processForeignSource, processForeign] using congrArg processReadBack ht
  subst t
  simp [processForeignSource, processForeign] at ht

theorem processLiftStep_has_foreign_source :
    ProcessLiftStep processForeignSource .nil
      ∧ ¬ ∃ t : Trace, processEncode t = processForeignSource :=
  ⟨ProcessLiftStep.intDelta processForeign, processForeignSource_not_encoded⟩

def processRank (p : ProcessTerm) : Nat := OperatorKO7.PolyInterpretation.W (processReadBack p)

theorem processLiftStep_rank_decreases {x y : ProcessTerm} (h : ProcessLiftStep x y) :
    processRank y < processRank x :=
  OperatorKO7.PolyInterpretation.W_orients_step (processLiftStep_readBack h)

theorem processLiftStep_wellFounded :
    WellFounded (fun y x : ProcessTerm => ProcessLiftStep x y) := by
  refine Subrelation.wf ?_
    (InvImage.wf processReadBack OperatorKO7.PolyInterpretation.wf_StepRev_poly)
  intro y x h
  exact processLiftStep_readBack h

def piCalculusTransport : CertifiedSubstrateChange Step where
  Carrier := ProcessTerm
  encode := processEncode
  readBack := processReadBack
  readBack_encode := processReadBack_processEncode
  readBack_not_injective := processReadBack_not_injective
  TargetStep := ProcessLiftStep
  forward := processLiftStep_iff.mpr
  target_wellFounded := processLiftStep_wellFounded

/-- **piCalculusTerminationTranslation.** Exact KO7 operational transport on the process carrier:
the encoded image reflects and preserves each root step, the target lift terminates, and read-back
remains noninjective away from the image. -/
abbrev PiCalculusTerminationTranslationRowClaim : Prop :=
  Function.Injective processEncode
    ∧ Nonempty (Trace ≃ EncodedProcessTerm)
    ∧ (∀ t, processReadBack (processEncode t) = t)
    ∧ (∀ {s t}, Step s t ↔ ProcessLiftStep (processEncode s) (processEncode t))
    ∧ (∀ {x y}, ProcessLiftStep x y → processRank y < processRank x)
    ∧ WellFounded (fun y x : ProcessTerm => ProcessLiftStep x y)
    ∧ (∃ x y : ProcessTerm,
      ProcessLiftStep x y ∧ ¬ ∃ t : Trace, processEncode t = x)
    ∧ ¬ Function.Injective processReadBack
    ∧ WellFounded (fun y x : Trace => Step x y)

theorem piCalculusTerminationTranslation_row_anchor :
    PiCalculusTerminationTranslationRowClaim :=
  ⟨processEncode_injective, ⟨processImageEquiv⟩, processReadBack_processEncode,
    fun {_ _} => processLiftStep_iff.symm, processLiftStep_rank_decreases,
    processLiftStep_wellFounded,
    ⟨processForeignSource, .nil, processLiftStep_has_foreign_source⟩,
    processReadBack_not_injective,
    piCalculusTransport.source_wellFounded⟩

/-- A separate continuation carrier; continuations are not identified with process channels. -/
inductive CPSTerm where
  | halt : CPSTerm
  | unary : Nat → CPSTerm → CPSTerm
  | binary : Nat → CPSTerm → CPSTerm → CPSTerm
  | ternary : Nat → CPSTerm → CPSTerm → CPSTerm → CPSTerm
  deriving DecidableEq, Repr

/-- Structural continuation encoding; source traces are reconstructed rather than stored. -/
@[simp] def cpsEncode : Trace → CPSTerm
  | .void => .halt
  | .delta t => .unary 0 (cpsEncode t)
  | .integrate t => .unary 1 (cpsEncode t)
  | .merge a b => .binary 0 (cpsEncode a) (cpsEncode b)
  | .app a b => .binary 1 (cpsEncode a) (cpsEncode b)
  | .recΔ b s n => .ternary 0 (cpsEncode b) (cpsEncode s) (cpsEncode n)
  | .eqW a b => .binary 2 (cpsEncode a) (cpsEncode b)

@[simp] def cpsReadBack : CPSTerm → Trace
  | .halt => .void
  | .unary 0 t => .delta (cpsReadBack t)
  | .unary 1 t => .integrate (cpsReadBack t)
  | .binary 0 a b => .merge (cpsReadBack a) (cpsReadBack b)
  | .binary 1 a b => .app (cpsReadBack a) (cpsReadBack b)
  | .ternary 0 b s n => .recΔ (cpsReadBack b) (cpsReadBack s) (cpsReadBack n)
  | .binary 2 a b => .eqW (cpsReadBack a) (cpsReadBack b)
  | _ => .void

@[simp] theorem cpsReadBack_cpsEncode (t : Trace) : cpsReadBack (cpsEncode t) = t := by
  induction t <;> simp [cpsEncode, cpsReadBack, *]

theorem cpsEncode_injective : Function.Injective cpsEncode := by
  intro a b h
  have := congrArg cpsReadBack h
  simpa using this

def EncodedCPSTerm := {p : CPSTerm // ∃ t : Trace, cpsEncode t = p}

def cpsImageEquiv : Trace ≃ EncodedCPSTerm where
  toFun t := ⟨cpsEncode t, ⟨t, rfl⟩⟩
  invFun p := cpsReadBack p.1
  left_inv := cpsReadBack_cpsEncode
  right_inv := by
    rintro ⟨p, t, rfl⟩
    apply Subtype.ext
    simp

theorem cpsReadBack_not_injective : ¬ Function.Injective cpsReadBack := by
  intro h
  have hbad : CPSTerm.halt = CPSTerm.unary 99 CPSTerm.halt := h rfl
  exact CPSTerm.noConfusion hbad

inductive CPSLiftStep : CPSTerm → CPSTerm → Prop
  | intDelta (t : CPSTerm) :
      CPSLiftStep (.unary 1 (.unary 0 t)) .halt
  | mergeVoidLeft (t : CPSTerm) :
      CPSLiftStep (.binary 0 .halt t) t
  | mergeVoidRight (t : CPSTerm) :
      CPSLiftStep (.binary 0 t .halt) t
  | mergeCancel (t : CPSTerm) :
      CPSLiftStep (.binary 0 t t) t
  | recZero (b s : CPSTerm) :
      CPSLiftStep (.ternary 0 b s .halt) b
  | recSucc (b s n : CPSTerm) :
      CPSLiftStep (.ternary 0 b s (.unary 0 n)) (.binary 1 s (.ternary 0 b s n))
  | eqRefl (a : CPSTerm) :
      CPSLiftStep (.binary 2 a a) .halt
  | eqDiff (a b : CPSTerm) :
      CPSLiftStep (.binary 2 a b) (.unary 1 (.binary 0 a b))

theorem cpsLiftStep_readBack :
    ∀ {x y : CPSTerm}, CPSLiftStep x y → Step (cpsReadBack x) (cpsReadBack y)
  | _, _, CPSLiftStep.intDelta t => by
      simpa using Step.R_int_delta (cpsReadBack t)
  | _, _, CPSLiftStep.mergeVoidLeft t => by
      simpa using Step.R_merge_void_left (cpsReadBack t)
  | _, _, CPSLiftStep.mergeVoidRight t => by
      simpa using Step.R_merge_void_right (cpsReadBack t)
  | _, _, CPSLiftStep.mergeCancel t => by
      simpa using Step.R_merge_cancel (cpsReadBack t)
  | _, _, CPSLiftStep.recZero b s => by
      simpa using Step.R_rec_zero (cpsReadBack b) (cpsReadBack s)
  | _, _, CPSLiftStep.recSucc b s n => by
      simpa using Step.R_rec_succ (cpsReadBack b) (cpsReadBack s) (cpsReadBack n)
  | _, _, CPSLiftStep.eqRefl a => by
      simpa using Step.R_eq_refl (cpsReadBack a)
  | _, _, CPSLiftStep.eqDiff a b => by
      simpa using Step.R_eq_diff (cpsReadBack a) (cpsReadBack b)

/-- Exact encoding of every KO7 root step into the CPS relation. -/
theorem step_to_cpsLiftStep_encode :
    ∀ {s t : Trace}, Step s t → CPSLiftStep (cpsEncode s) (cpsEncode t)
  | _, _, Step.R_int_delta t => CPSLiftStep.intDelta (cpsEncode t)
  | _, _, Step.R_merge_void_left t => CPSLiftStep.mergeVoidLeft (cpsEncode t)
  | _, _, Step.R_merge_void_right t => CPSLiftStep.mergeVoidRight (cpsEncode t)
  | _, _, Step.R_merge_cancel t => CPSLiftStep.mergeCancel (cpsEncode t)
  | _, _, Step.R_rec_zero b s => CPSLiftStep.recZero (cpsEncode b) (cpsEncode s)
  | _, _, Step.R_rec_succ b s n =>
      CPSLiftStep.recSucc (cpsEncode b) (cpsEncode s) (cpsEncode n)
  | _, _, Step.R_eq_refl a => CPSLiftStep.eqRefl (cpsEncode a)
  | _, _, Step.R_eq_diff a b => CPSLiftStep.eqDiff (cpsEncode a) (cpsEncode b)

theorem cpsLiftStep_iff {s t : Trace} :
    CPSLiftStep (cpsEncode s) (cpsEncode t) ↔ Step s t :=
  ⟨fun h => by simpa using cpsLiftStep_readBack h, step_to_cpsLiftStep_encode⟩

theorem cpsImageEquiv_step_iff {s t : Trace} :
    CPSLiftStep (cpsImageEquiv s).1 (cpsImageEquiv t).1 ↔ Step s t :=
  cpsLiftStep_iff

def cpsForeign : CPSTerm := .unary 99 .halt

theorem cpsForeign_not_encoded : ¬ ∃ t : Trace, cpsEncode t = cpsForeign := by
  rintro ⟨t, ht⟩
  have htVoid : t = .void := by
    simpa [cpsForeign] using congrArg cpsReadBack ht
  subst t
  simp [cpsForeign] at ht

def cpsForeignSource : CPSTerm := .unary 1 (.unary 0 cpsForeign)

theorem cpsForeignSource_not_encoded :
    ¬ ∃ t : Trace, cpsEncode t = cpsForeignSource := by
  rintro ⟨t, ht⟩
  have htShape : t = .integrate (.delta .void) := by
    simpa [cpsForeignSource, cpsForeign] using congrArg cpsReadBack ht
  subst t
  simp [cpsForeignSource, cpsForeign] at ht

theorem cpsLiftStep_has_foreign_source :
    CPSLiftStep cpsForeignSource .halt
      ∧ ¬ ∃ t : Trace, cpsEncode t = cpsForeignSource :=
  ⟨CPSLiftStep.intDelta cpsForeign, cpsForeignSource_not_encoded⟩

def cpsRank (p : CPSTerm) : Nat := OperatorKO7.PolyInterpretation.W (cpsReadBack p)

theorem cpsLiftStep_rank_decreases {x y : CPSTerm} (h : CPSLiftStep x y) :
    cpsRank y < cpsRank x :=
  OperatorKO7.PolyInterpretation.W_orients_step (cpsLiftStep_readBack h)

theorem cpsLiftStep_wellFounded : WellFounded (fun y x : CPSTerm => CPSLiftStep x y) := by
  refine Subrelation.wf ?_
    (InvImage.wf cpsReadBack OperatorKO7.PolyInterpretation.wf_StepRev_poly)
  intro y x h
  exact cpsLiftStep_readBack h

def lambdaMuCPSTransport : CertifiedSubstrateChange Step where
  Carrier := CPSTerm
  encode := cpsEncode
  readBack := cpsReadBack
  readBack_encode := cpsReadBack_cpsEncode
  readBack_not_injective := cpsReadBack_not_injective
  TargetStep := CPSLiftStep
  forward := cpsLiftStep_iff.mpr
  target_wellFounded := cpsLiftStep_wellFounded

/-- **lambdaMuSNViaCPS.** Exact KO7 operational transport on a separate continuation carrier. -/
abbrev LambdaMuSNViaCPSRowClaim : Prop :=
  Function.Injective cpsEncode
    ∧ Nonempty (Trace ≃ EncodedCPSTerm)
    ∧ (∀ t, cpsReadBack (cpsEncode t) = t)
    ∧ (∀ {s t}, Step s t ↔ CPSLiftStep (cpsEncode s) (cpsEncode t))
    ∧ (∀ {x y}, CPSLiftStep x y → cpsRank y < cpsRank x)
    ∧ WellFounded (fun y x : CPSTerm => CPSLiftStep x y)
    ∧ (∃ x y : CPSTerm,
      CPSLiftStep x y ∧ ¬ ∃ t : Trace, cpsEncode t = x)
    ∧ ¬ Function.Injective cpsReadBack
    ∧ WellFounded (fun y x : Trace => Step x y)

theorem lambdaMuSNViaCPS_row_anchor : LambdaMuSNViaCPSRowClaim :=
  ⟨cpsEncode_injective, ⟨cpsImageEquiv⟩, cpsReadBack_cpsEncode,
    fun {_ _} => cpsLiftStep_iff.symm, cpsLiftStep_rank_decreases,
    cpsLiftStep_wellFounded,
    ⟨cpsForeignSource, .halt, cpsLiftStep_has_foreign_source⟩,
    cpsReadBack_not_injective,
    lambdaMuCPSTransport.source_wellFounded⟩

/-- The graph transport is exact on the KO7 image and strictly extends it with native steps. -/
theorem weightedTypeGraphTransport_exactStrict :
    ExactStrictSubstrateExtension weightedTypeGraphTransport :=
  ⟨graphLiftStep_iff, graphLiftStep_readBack,
    ⟨graphForeignSource, .state 0, graphLiftStep_has_foreign_source⟩⟩

/-- The closed process transport is exact on the KO7 image and strictly extends it. -/
theorem piCalculusTransport_exactStrict :
    ExactStrictSubstrateExtension piCalculusTransport :=
  ⟨processLiftStep_iff, processLiftStep_readBack,
    ⟨processForeignSource, .nil, processLiftStep_has_foreign_source⟩⟩

/-- The continuation transport is exact on the KO7 image and strictly extends it. -/
theorem lambdaMuCPSTransport_exactStrict :
    ExactStrictSubstrateExtension lambdaMuCPSTransport :=
  ⟨cpsLiftStep_iff, cpsLiftStep_readBack,
    ⟨cpsForeignSource, .halt, cpsLiftStep_has_foreign_source⟩⟩

/-- One theorem packages the exact conservative image and strict carrier extension for all three
native target calculi. -/
theorem graph_process_cps_exact_strict_extensions :
    ExactStrictSubstrateExtension weightedTypeGraphTransport
      ∧ ExactStrictSubstrateExtension piCalculusTransport
      ∧ ExactStrictSubstrateExtension lambdaMuCPSTransport :=
  ⟨weightedTypeGraphTransport_exactStrict, piCalculusTransport_exactStrict,
    lambdaMuCPSTransport_exactStrict⟩

end OperatorKO7.Methods.SubstrateChangeRows
