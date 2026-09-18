import OperatorKO7.Meta.Methods.SubstrateChangeRows
import Mathlib.Data.Prod.Lex

/-!
# Native substrate-change semantics for ORI-6

The existing source-image transports are retained. This module adds termination
measures and operational fragments defined directly on the target carriers.
None of the target-side ranks below calls a source read-back function.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SubstrateChangeNativeSemantics

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.Methods.SubstrateChangeRows

/-! ## Native weighted graph rank -/

/-- Structural rank on the graph carrier. The constructor codes follow the
native graph reduction rather than evaluating `graphReadBack`. -/
@[simp] def graphNativeRank : GraphNode → Nat
  | .state _ => 1
  | .edge (.state 1) t => graphNativeRank t + 1
  | .edge (.state 2) t => graphNativeRank t + 1
  | .edge (.edge (.state 3) a) b => graphNativeRank a + graphNativeRank b + 1
  | .edge (.edge (.state 4) a) b => graphNativeRank a + graphNativeRank b + 1
  | .edge (.edge (.edge (.state 5) b) s) n =>
      (graphNativeRank n + 1) * (graphNativeRank s + graphNativeRank b + 1)
  | .edge (.edge (.state 6) a) b => graphNativeRank a + graphNativeRank b + 3
  | .edge a b => graphNativeRank a + graphNativeRank b + 1

/-- Every graph node has positive native rank. -/
theorem graphNativeRank_pos (g : GraphNode) : 0 < graphNativeRank g := by
  induction g using graphNativeRank.induct <;>
    simp_all [graphNativeRank]

/-- Every native graph reduction strictly decreases the graph-native rank. -/
theorem graphLiftStep_nativeRank_decreases :
    ∀ {x y : GraphNode}, GraphLiftStep x y → graphNativeRank y < graphNativeRank x
  | _, _, .intDelta t => by
      simp [graphNativeRank]
  | _, _, .mergeVoidLeft t => by
      have hp := graphNativeRank_pos t
      simp [graphNativeRank]
      omega
  | _, _, .mergeVoidRight t => by
      have hp := graphNativeRank_pos t
      simp [graphNativeRank]
      omega
  | _, _, .mergeCancel t => by
      have hp := graphNativeRank_pos t
      simp [graphNativeRank]
      omega
  | _, _, .recZero b s => by
      have hb := graphNativeRank_pos b
      have hs := graphNativeRank_pos s
      simp [graphNativeRank]
      nlinarith
  | _, _, .recSucc b s n => by
      have hb := graphNativeRank_pos b
      have hs := graphNativeRank_pos s
      have hn := graphNativeRank_pos n
      simp [graphNativeRank]
      nlinarith
  | _, _, .eqRefl a => by
      have ha := graphNativeRank_pos a
      simp [graphNativeRank]
  | _, _, .eqDiff a b => by
      simp [graphNativeRank]

/-- Target-internal well-foundedness of the graph reduction. -/
theorem graphLiftStep_native_wellFounded :
    WellFounded (fun y x : GraphNode => GraphLiftStep x y) := by
  apply Subrelation.wf
    (r := fun y x : GraphNode => graphNativeRank y < graphNativeRank x)
  · intro y x h
    exact graphLiftStep_nativeRank_decreases h
  · exact InvImage.wf graphNativeRank Nat.lt_wfRel.wf

/-- The native rank is meaningful on a target-only source, not only on encoded
source terms. -/
theorem graphForeignSource_nativeRank_drop :
    graphNativeRank (.state 0) < graphNativeRank graphForeignSource := by
  simp [graphForeignSource, graphForeign, graphNativeRank]

/-! ## Generalized weighted type graph -/

/-- A generalized target graph carries a numeric auxiliary weight in addition
to the graph node. -/
abbrev GeneralizedGraphNode := Nat × GraphNode

/-- Generalized target reduction. The graph rule preserves the auxiliary
weight, while a native relabel step can strictly reduce it. -/
inductive GeneralizedGraphStep : GeneralizedGraphNode → GeneralizedGraphNode → Prop
  | graph (k : Nat) {x y : GraphNode} :
      GraphLiftStep x y → GeneralizedGraphStep (k, x) (k, y)
  | relabel {j k : Nat} (g : GraphNode) :
      j < k → GeneralizedGraphStep (k, g) (j, g)

/-- Lexicographic target weight using both graph structure and the auxiliary
weight. -/
def generalizedGraphWeight (x : GeneralizedGraphNode) : Nat × Nat :=
  (graphNativeRank x.2, x.1)

/-- The generalized weight strictly decreases on both kinds of native step. -/
theorem generalizedGraphStep_weight_decreases {x y : GeneralizedGraphNode}
    (h : GeneralizedGraphStep x y) :
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (generalizedGraphWeight y) (generalizedGraphWeight x) := by
  cases h with
  | graph k hxy =>
      exact Prod.Lex.left _ _ (graphLiftStep_nativeRank_decreases hxy)
  | relabel g hjk =>
      exact Prod.Lex.right (graphNativeRank g) hjk

/-- The generalized target relation is well founded by its native pair weight. -/
theorem generalizedGraphStep_wellFounded :
    WellFounded (fun y x : GeneralizedGraphNode => GeneralizedGraphStep x y) := by
  have hlex : WellFounded
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)) :=
    WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      generalizedGraphWeight)
  · intro y x h
    exact generalizedGraphStep_weight_decreases h
  · exact InvImage.wf generalizedGraphWeight hlex

/-- Auxiliary weight is load-bearing: relabeling changes the generalized
weight while leaving the graph node fixed. -/
theorem generalizedGraph_auxiliary_weight_contributes (g : GraphNode) :
    GeneralizedGraphStep (1, g) (0, g) ∧
      generalizedGraphWeight (1, g) ≠ generalizedGraphWeight (0, g) := by
  constructor
  · exact GeneralizedGraphStep.relabel g (by decide)
  · simp [generalizedGraphWeight]

/-! ## Native process rank for the existing process carrier -/

/-- Structural rank computed on `ProcessTerm` itself. -/
@[simp] def processNativeRank : ProcessTerm → Nat
  | .nil => 1
  | .par a b => processNativeRank a + processNativeRank b + 1
  | .send 0 t => processNativeRank t + 1
  | .send 1 t => processNativeRank t + 1
  | .send 2 (.par a b) => processNativeRank a + processNativeRank b + 1
  | .send 3 (.par a b) => processNativeRank a + processNativeRank b + 1
  | .send 4 (.par b (.par s n)) =>
      (processNativeRank n + 1) * (processNativeRank s + processNativeRank b + 1)
  | .send 5 (.par a b) => processNativeRank a + processNativeRank b + 3
  | .send _ t => processNativeRank t + 1

/-- Every process has positive native rank. -/
theorem processNativeRank_pos (p : ProcessTerm) : 0 < processNativeRank p := by
  induction p using processNativeRank.induct <;>
    simp_all [processNativeRank]

/-- Existing KO7 process-lift rules decrease the target-native process rank. -/
theorem processLiftStep_nativeRank_decreases :
    ∀ {x y : ProcessTerm}, ProcessLiftStep x y → processNativeRank y < processNativeRank x
  | _, _, .intDelta t => by
      simp [processNativeRank]
  | _, _, .mergeVoidLeft t => by
      have hp := processNativeRank_pos t
      simp [processNativeRank]
      omega
  | _, _, .mergeVoidRight t => by
      have hp := processNativeRank_pos t
      simp [processNativeRank]
      omega
  | _, _, .mergeCancel t => by
      have hp := processNativeRank_pos t
      simp [processNativeRank]
      omega
  | _, _, .recZero b s => by
      have hb := processNativeRank_pos b
      have hs := processNativeRank_pos s
      simp [processNativeRank]
      nlinarith
  | _, _, .recSucc b s n => by
      have hb := processNativeRank_pos b
      have hs := processNativeRank_pos s
      have hn := processNativeRank_pos n
      simp [processNativeRank]
      nlinarith
  | _, _, .eqRefl a => by
      have ha := processNativeRank_pos a
      simp [processNativeRank]
  | _, _, .eqDiff a b => by
      simp [processNativeRank]

/-- Target-internal well-foundedness of the existing process lift. -/
theorem processLiftStep_native_wellFounded :
    WellFounded (fun y x : ProcessTerm => ProcessLiftStep x y) := by
  apply Subrelation.wf
    (r := fun y x : ProcessTerm => processNativeRank y < processNativeRank x)
  · intro y x h
    exact processLiftStep_nativeRank_decreases h
  · exact InvImage.wf processNativeRank Nat.lt_wfRel.wf

/-! ## Selected finite pi-calculus fragment -/

/-- Finite process syntax with synchronous send/receive and parallel
composition. Replication and recursive process definitions are intentionally
absent from this selected termination fragment. -/
inductive NativePiTerm where
  | zero : NativePiTerm
  | send : Nat → NativePiTerm → NativePiTerm
  | recv : Nat → NativePiTerm → NativePiTerm
  | par : NativePiTerm → NativePiTerm → NativePiTerm
  deriving DecidableEq, Repr

/-- Structural size of the selected process fragment. -/
@[simp] def nativePiSize : NativePiTerm → Nat
  | .zero => 1
  | .send _ p => nativePiSize p + 2
  | .recv _ p => nativePiSize p + 2
  | .par p q => nativePiSize p + nativePiSize q + 1

/-- Synchronous reduction with parallel-context closure. -/
inductive NativePiStep : NativePiTerm → NativePiTerm → Prop
  | sync (c : Nat) (p q : NativePiTerm) :
      NativePiStep (.par (.send c p) (.recv c q)) (.par p q)
  | syncComm (c : Nat) (p q : NativePiTerm) :
      NativePiStep (.par (.recv c q) (.send c p)) (.par q p)
  | parLeft {p p' q : NativePiTerm} :
      NativePiStep p p' → NativePiStep (.par p q) (.par p' q)
  | parRight {p q q' : NativePiTerm} :
      NativePiStep q q' → NativePiStep (.par p q) (.par p q')

/-- Every selected pi-calculus step decreases native process size. -/
theorem nativePiStep_size_decreases {p q : NativePiTerm}
    (h : NativePiStep p q) : nativePiSize q < nativePiSize p := by
  induction h with
  | sync c p q =>
      simp [nativePiSize]
      omega
  | syncComm c p q =>
      simp [nativePiSize, Nat.add_comm]
      omega
  | parLeft h ih => simp [nativePiSize]; omega
  | parRight h ih => simp [nativePiSize]; omega

/-- Strong normalization of the selected finite, replication-free process
fragment. This theorem does not quantify over arbitrary pi processes. -/
theorem nativePiStep_wellFounded :
    WellFounded (fun q p : NativePiTerm => NativePiStep p q) := by
  apply Subrelation.wf
    (r := fun q p : NativePiTerm => nativePiSize q < nativePiSize p)
  · intro q p h
    exact nativePiStep_size_decreases h
  · exact InvImage.wf nativePiSize Nat.lt_wfRel.wf

/-- Non-vacuous synchronization step. -/
theorem nativePi_sync_control :
    NativePiStep
      (.par (.send 0 .zero) (.recv 0 .zero))
      (.par .zero .zero) :=
  NativePiStep.sync 0 .zero .zero

/-! ## Native continuation rank for the existing CPS carrier -/

/-- Structural rank on the existing CPS syntax. -/
@[simp] def cpsNativeRank : CPSTerm → Nat
  | .halt => 1
  | .unary 0 t => cpsNativeRank t + 1
  | .unary 1 t => cpsNativeRank t + 1
  | .binary 0 a b => cpsNativeRank a + cpsNativeRank b + 1
  | .binary 1 a b => cpsNativeRank a + cpsNativeRank b + 1
  | .binary 2 a b => cpsNativeRank a + cpsNativeRank b + 3
  | .ternary 0 b s n =>
      (cpsNativeRank n + 1) * (cpsNativeRank s + cpsNativeRank b + 1)
  | .unary _ t => cpsNativeRank t + 1
  | .binary _ a b => cpsNativeRank a + cpsNativeRank b + 1
  | .ternary _ a b c => cpsNativeRank a + cpsNativeRank b + cpsNativeRank c + 1

/-- Every CPS term has positive native rank. -/
theorem cpsNativeRank_pos (p : CPSTerm) : 0 < cpsNativeRank p := by
  induction p using cpsNativeRank.induct <;>
    simp_all [cpsNativeRank]

/-- Existing CPS-lift rules decrease the target-native continuation rank. -/
theorem cpsLiftStep_nativeRank_decreases :
    ∀ {x y : CPSTerm}, CPSLiftStep x y → cpsNativeRank y < cpsNativeRank x
  | _, _, .intDelta t => by
      simp [cpsNativeRank]
  | _, _, .mergeVoidLeft t => by
      have hp := cpsNativeRank_pos t
      simp [cpsNativeRank]
      omega
  | _, _, .mergeVoidRight t => by
      have hp := cpsNativeRank_pos t
      simp [cpsNativeRank]
      omega
  | _, _, .mergeCancel t => by
      have hp := cpsNativeRank_pos t
      simp [cpsNativeRank]
      omega
  | _, _, .recZero b s => by
      have hb := cpsNativeRank_pos b
      have hs := cpsNativeRank_pos s
      simp [cpsNativeRank]
      nlinarith
  | _, _, .recSucc b s n => by
      have hb := cpsNativeRank_pos b
      have hs := cpsNativeRank_pos s
      have hn := cpsNativeRank_pos n
      simp [cpsNativeRank]
      nlinarith
  | _, _, .eqRefl a => by
      have ha := cpsNativeRank_pos a
      simp [cpsNativeRank]
  | _, _, .eqDiff a b => by
      simp [cpsNativeRank]

/-- Target-internal well-foundedness of the existing CPS lift. -/
theorem cpsLiftStep_native_wellFounded :
    WellFounded (fun y x : CPSTerm => CPSLiftStep x y) := by
  apply Subrelation.wf
    (r := fun y x : CPSTerm => cpsNativeRank y < cpsNativeRank x)
  · intro y x h
    exact cpsLiftStep_nativeRank_decreases h
  · exact InvImage.wf cpsNativeRank Nat.lt_wfRel.wf

/-! ## Selected lambda-mu/CPS fragment -/

/-- A selected control fragment with named continuations. -/
inductive LambdaMuTerm where
  | halt : LambdaMuTerm
  | mu : Nat → LambdaMuTerm → LambdaMuTerm
  | throw : Nat → LambdaMuTerm → LambdaMuTerm
  deriving DecidableEq, Repr

/-- Native lambda-mu reduction and unary context closure. -/
inductive LambdaMuStep : LambdaMuTerm → LambdaMuTerm → Prop
  | fire (k : Nat) (t : LambdaMuTerm) :
      LambdaMuStep (.throw k (.mu k t)) t
  | underMu {t u : LambdaMuTerm} (k : Nat) :
      LambdaMuStep t u → LambdaMuStep (.mu k t) (.mu k u)
  | underThrow {t u : LambdaMuTerm} (k : Nat) :
      LambdaMuStep t u → LambdaMuStep (.throw k t) (.throw k u)

/-- CPS syntax for the selected control fragment. -/
inductive NativeCPSTerm where
  | done : NativeCPSTerm
  | bind : Nat → NativeCPSTerm → NativeCPSTerm
  | invoke : Nat → NativeCPSTerm → NativeCPSTerm
  deriving DecidableEq, Repr

/-- CPS translation. -/
@[simp] def lambdaMuToCPS : LambdaMuTerm → NativeCPSTerm
  | .halt => .done
  | .mu k t => .bind k (lambdaMuToCPS t)
  | .throw k t => .invoke k (lambdaMuToCPS t)

/-- CPS reduction matching the control redex, with unary context closure. -/
inductive NativeCPSStep : NativeCPSTerm → NativeCPSTerm → Prop
  | fire (k : Nat) (t : NativeCPSTerm) :
      NativeCPSStep (.invoke k (.bind k t)) t
  | underBind {t u : NativeCPSTerm} (k : Nat) :
      NativeCPSStep t u → NativeCPSStep (.bind k t) (.bind k u)
  | underInvoke {t u : NativeCPSTerm} (k : Nat) :
      NativeCPSStep t u → NativeCPSStep (.invoke k t) (.invoke k u)

/-- One lambda-mu step is simulated by one CPS step on the translated terms. -/
theorem lambdaMuStep_simulates_cps {t u : LambdaMuTerm}
    (h : LambdaMuStep t u) : NativeCPSStep (lambdaMuToCPS t) (lambdaMuToCPS u) := by
  induction h with
  | fire k t => exact NativeCPSStep.fire k (lambdaMuToCPS t)
  | underMu k h ih => exact NativeCPSStep.underBind k ih
  | underThrow k h ih => exact NativeCPSStep.underInvoke k ih

/-- Native CPS size. -/
@[simp] def nativeCPSSize : NativeCPSTerm → Nat
  | .done => 1
  | .bind _ t => nativeCPSSize t + 2
  | .invoke _ t => nativeCPSSize t + 2

/-- Every selected CPS step strictly decreases size. -/
theorem nativeCPSStep_size_decreases {t u : NativeCPSTerm}
    (h : NativeCPSStep t u) : nativeCPSSize u < nativeCPSSize t := by
  induction h with
  | fire k t =>
      simp [nativeCPSSize]
      omega
  | underBind k h ih => simp [nativeCPSSize]; omega
  | underInvoke k h ih => simp [nativeCPSSize]; omega

/-- Strong normalization of the selected CPS target. -/
theorem nativeCPSStep_wellFounded :
    WellFounded (fun u t : NativeCPSTerm => NativeCPSStep t u) := by
  apply Subrelation.wf
    (r := fun u t : NativeCPSTerm => nativeCPSSize u < nativeCPSSize t)
  · intro u t h
    exact nativeCPSStep_size_decreases h
  · exact InvImage.wf nativeCPSSize Nat.lt_wfRel.wf

/-- Non-vacuous source/target simulation control. -/
theorem lambdaMu_cps_fire_control :
    LambdaMuStep (.throw 0 (.mu 0 .halt)) .halt ∧
      NativeCPSStep
        (lambdaMuToCPS (.throw 0 (.mu 0 .halt)))
        (lambdaMuToCPS .halt) :=
  ⟨LambdaMuStep.fire 0 .halt,
    lambdaMuStep_simulates_cps (LambdaMuStep.fire 0 .halt)⟩

/-! ## Sharing-aware quasi-interpretation -/

/-- Quasi-interpretation laws on the real shared-node carrier. -/
structure SharedQuasiInterpretation where
  eval : SharedTerm → Nat
  node_left : ∀ x y, eval x ≤ eval (.node x y)
  node_right : ∀ x y, eval y ≤ eval (.node x y)
  shared_contains : ∀ x, eval x ≤ eval (.shared x)
  sharing_weak : ∀ x, eval (.shared x) ≤ eval (.node x x)

/-- Nonconstant sharing-aware quasi-interpretation given by actual shared size. -/
def sharedSizeQuasiInterpretation : SharedQuasiInterpretation where
  eval := sharedSize
  node_left := by
    intro x y
    simp [sharedSize]
    omega
  node_right := by
    intro x y
    simp [sharedSize]
  shared_contains := by
    intro x
    simp [sharedSize]
  sharing_weak := by
    intro x
    exact Nat.le_of_lt (sharedSize_shared_lt_node x)

/-- The sharing-aware quasi-interpretation is genuinely nonconstant. -/
theorem sharedSizeQuasiInterpretation_nonconstant :
    sharedSizeQuasiInterpretation.eval .leaf ≠
      sharedSizeQuasiInterpretation.eval (.shared .leaf) := by
  simp [sharedSizeQuasiInterpretation, sharedSize]

/-- Native sharing contraction. -/
inductive SharedDupStep : SharedTerm → SharedTerm → Prop
  | contract (x : SharedTerm) : SharedDupStep (.node x x) (.shared x)

/-- Native shared size strictly decreases on sharing contraction. -/
theorem sharedDupStep_size_decreases {x y : SharedTerm}
    (h : SharedDupStep x y) : sharedSize y < sharedSize x := by
  cases h with
  | contract x => exact sharedSize_shared_lt_node x

/-- The sharing contraction is well founded on the target carrier. -/
theorem sharedDupStep_wellFounded :
    WellFounded (fun y x : SharedTerm => SharedDupStep x y) := by
  apply Subrelation.wf (r := fun y x : SharedTerm => sharedSize y < sharedSize x)
  · intro y x h
    exact sharedDupStep_size_decreases h
  · exact InvImage.wf sharedSize Nat.lt_wfRel.wf

/-- Same source-tree read-back, different native size, and a strict target
sharing step. This is the nonconservative contribution of sharing. -/
theorem sharing_native_control :
    unshare (.shared .leaf) = unshare (.node .leaf .leaf) ∧
      sharedSize (.shared .leaf) < sharedSize (.node .leaf .leaf) ∧
      SharedDupStep (.node .leaf .leaf) (.shared .leaf) := by
  exact ⟨unshare_shared_eq_node .leaf,
    sharedSize_shared_lt_node .leaf, SharedDupStep.contract .leaf⟩

/-! ## ORI-6 capstone -/

/-- Native semantics for the five ORI-6 rows. Existing exact source-image
transport and target-only-source controls are retained beside the target-native
termination arguments. -/
structure ORI6NativeSemantics where
  weightedGraphExact : ExactStrictSubstrateExtension weightedTypeGraphTransport
  weightedGraphNativeWF : WellFounded (fun y x : GraphNode => GraphLiftStep x y)
  generalizedGraphNativeWF :
    WellFounded (fun y x : GeneralizedGraphNode => GeneralizedGraphStep x y)
  generalizedWeightActive : ∀ g : GraphNode,
    generalizedGraphWeight (1, g) ≠ generalizedGraphWeight (0, g)
  processExact : ExactStrictSubstrateExtension piCalculusTransport
  processNativeWF : WellFounded (fun y x : ProcessTerm => ProcessLiftStep x y)
  piFragmentWF : WellFounded (fun y x : NativePiTerm => NativePiStep x y)
  cpsExact : ExactStrictSubstrateExtension lambdaMuCPSTransport
  cpsNativeWF : WellFounded (fun y x : CPSTerm => CPSLiftStep x y)
  lambdaMuSimulation : ∀ {t u}, LambdaMuStep t u →
    NativeCPSStep (lambdaMuToCPS t) (lambdaMuToCPS u)
  nativeCPSWF : WellFounded (fun y x : NativeCPSTerm => NativeCPSStep x y)
  sharingQI : SharedQuasiInterpretation
  sharingQINonconstant : sharingQI.eval .leaf ≠ sharingQI.eval (.shared .leaf)
  sharingWF : WellFounded (fun y x : SharedTerm => SharedDupStep x y)
  sharingNoninjective : ¬ Function.Injective unshare

/-- Concrete ORI-6 native-method package. -/
def ori6NativeSemantics : ORI6NativeSemantics where
  weightedGraphExact := weightedTypeGraphTransport_exactStrict
  weightedGraphNativeWF := graphLiftStep_native_wellFounded
  generalizedGraphNativeWF := generalizedGraphStep_wellFounded
  generalizedWeightActive := by
    intro g h
    exact (generalizedGraph_auxiliary_weight_contributes g).2 h
  processExact := piCalculusTransport_exactStrict
  processNativeWF := processLiftStep_native_wellFounded
  piFragmentWF := nativePiStep_wellFounded
  cpsExact := lambdaMuCPSTransport_exactStrict
  cpsNativeWF := cpsLiftStep_native_wellFounded
  lambdaMuSimulation := lambdaMuStep_simulates_cps
  nativeCPSWF := nativeCPSStep_wellFounded
  sharingQI := sharedSizeQuasiInterpretation
  sharingQINonconstant := sharedSizeQuasiInterpretation_nonconstant
  sharingWF := sharedDupStep_wellFounded
  sharingNoninjective := unshare_not_injective

end OperatorKO7.Methods.OrientationClosure.SubstrateChangeNativeSemantics
