import OperatorKO7.Meta.EstimatedDPGraphTcap
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.TTT2_CertificateReplay
import OperatorKO7.Meta.DependencyPairs_KernelFirstOrder

set_option autoImplicit false

/-!
# KO7 TCAP Estimated Dependency-Graph Soundness

This module specializes the generic TCAP over-approximation theorem from
`EstimatedDPGraphTcap` to the live KO7 dependency-pair problem. The KO7 DP
surface is a singleton schema pair, so the public API here packages that single
pair as a small node type, reuses the replayed pair-count fact, reuses the live
extracted-call-graph witness for the recursive `recD` self-successor, and keeps
the actual soundness proof as a thin wrapper around the already-landed generic
 theorem.
-/

namespace OperatorKO7.Meta.EstimatedDPGraphTCAPSoundness

open OperatorKO7.Meta.EstimatedDPGraphTcap
open OperatorKO7.DependencyPairsFragment
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.TTT2CertificateReplay

/-- The KO7 dependency-pair problem has one schema pair, matching the replayed
certificate surface. -/
inductive KO7DPPairNode
  | recSucc
  deriving DecidableEq, Fintype, Repr

/-- The replayed FAST surface and the live Lean dependency-pair relation agree
on the KO7 pair predicate. -/
theorem ko7_pair_surface_matches_replay :
    ko7FastReplay.projectionProblem.Pair = DPPair :=
  ko7FastReplay_uses_recSucc_pair

/-- The schema-node presentation used below has the same cardinality as the
replayed KO7 pair set. -/
theorem ko7_dp_schema_count_matches_replay :
    Fintype.card KO7DPPairNode = ko7FastReplay.pairCount := by
  rw [ko7FastReplay_pairCount]
  decide

/-- The extracted call graph already records the recursive `recD` successor used
by the KO7 dependency-pair pair. -/
theorem ko7_extracted_call_graph_supports_recD_successor :
    ∃ n ∈
        OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7FullStepExtractedNodes.toList,
      n.nodeKey = OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.recD ∧
        n.succKeys =
          ({OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.recD} :
            Finset OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol) :=
  OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7_full_step_has_recD_successor

abbrev symVoid : Nat := 0
abbrev symDelta : Nat := 1
abbrev symIntegrate : Nat := 2
abbrev symMerge : Nat := 3
abbrev symApp : Nat := 4
abbrev symRecD : Nat := 5
abbrev symEqW : Nat := 6

def vx : FOTm := .var 0
def vy : FOTm := .var 1
def vz : FOTm := .var 2

def voidTm : FOTm := .app symVoid []
def deltaTm (t : FOTm) : FOTm := .app symDelta [t]
def integrateTm (t : FOTm) : FOTm := .app symIntegrate [t]
def mergeTm (a b : FOTm) : FOTm := .app symMerge [a, b]
def appTm (a b : FOTm) : FOTm := .app symApp [a, b]
def recDTm (b s n : FOTm) : FOTm := .app symRecD [b, s, n]
def eqWTm (a b : FOTm) : FOTm := .app symEqW [a, b]

def integrateDeltaRule : Rule :=
  { lhs := integrateTm (deltaTm vx), rhs := vx }

def mergeVoidLeftRule : Rule :=
  { lhs := mergeTm voidTm vx, rhs := vx }

def mergeVoidRightRule : Rule :=
  { lhs := mergeTm vx voidTm, rhs := vx }

def mergeIdemRule : Rule :=
  { lhs := mergeTm vx vx, rhs := vx }

def recZeroRule : Rule :=
  { lhs := recDTm vx vy voidTm, rhs := vy }

def recSuccRule : Rule :=
  { lhs := recDTm vx vy (deltaTm vz), rhs := appTm vx (recDTm vx vy vz) }

def eqReflRule : Rule :=
  { lhs := eqWTm vx vx, rhs := vx }

def eqDiffRule : Rule :=
  { lhs := eqWTm vx vy, rhs := voidTm }

def ko7Rules : List Rule :=
  [ integrateDeltaRule
  , mergeVoidLeftRule
  , mergeVoidRightRule
  , mergeIdemRule
  , recZeroRule
  , recSuccRule
  , eqReflRule
  , eqDiffRule
  ]

/-- The Nat-coded KO7 full-step TRS used by `EstimatedDPGraphTcap`. This is the
signature bridge required by that generic module, not a replacement rewrite
 theory. -/
def ko7TRS : TRS where
  rules := ko7Rules
  lhs_app := by
    intro r hr
    simp [ko7Rules, integrateDeltaRule, mergeVoidLeftRule, mergeVoidRightRule,
      mergeIdemRule, recZeroRule, recSuccRule, eqReflRule, eqDiffRule] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨symIntegrate, [deltaTm vx], rfl⟩
    · exact ⟨symMerge, [voidTm, vx], rfl⟩
    · exact ⟨symMerge, [vx, voidTm], rfl⟩
    · exact ⟨symMerge, [vx, vx], rfl⟩
    · exact ⟨symRecD, [vx, vy, voidTm], rfl⟩
    · exact ⟨symRecD, [vx, vy, deltaTm vz], rfl⟩
    · exact ⟨symEqW, [vx, vx], rfl⟩
    · exact ⟨symEqW, [vx, vy], rfl⟩

/-- The singleton KO7 dependency-pair schema projected into the generic rule
format used by `EstimatedDPGraphTcap`. -/
def ko7PairRule : KO7DPPairNode → Rule
  | .recSucc =>
      { lhs := recDTm vx vy (deltaTm vz)
      , rhs := recDTm vx vy vz
      }

/-- Real KO7 DP edges, specialized to the singleton schema-node surface. -/
def ko7RealDPEdge (a b : KO7DPPairNode) : Prop :=
  RealEdge ko7TRS (ko7PairRule a) (ko7PairRule b)

/-- TCAP-estimated KO7 DP edges on the same schema-node surface. -/
def ko7EstimatedDPEdge (a b : KO7DPPairNode) : Prop :=
  EstEdge ko7TRS (ko7PairRule a) (ko7PairRule b)

def idSubst : Nat → FOTm := FOTm.var

/-- The KO7 recursive schema pair is itself admitted by the TCAP estimate. -/
theorem ko7_estimated_self_edge :
    ko7EstimatedDPEdge .recSucc .recSucc := by
  refine ⟨applySubst idSubst (ko7PairRule .recSucc).lhs, ?_, ⟨idSubst, rfl⟩⟩
  have hcap : tcap ko7TRS.rules (ko7PairRule .recSucc).rhs = Cap.hole := by
    show tcap ko7Rules (FOTm.app symRecD [vx, vy, vz]) = Cap.hole
    rw [tcap_app, if_pos (show definedB ko7Rules symRecD = true by decide)]
  rw [hcap]
  exact CapMatches.hole _

/-- KO7 specialization of the generic TCAP over-approximation theorem. -/
theorem estimated_dp_graph_tcap_overapproximation_sound
    {a b : KO7DPPairNode} :
    ko7RealDPEdge a b → ko7EstimatedDPEdge a b := by
  intro h
  cases a
  cases b
  simpa [ko7RealDPEdge, ko7EstimatedDPEdge, ko7PairRule] using
    estimated_dp_graph_tcap_unconditional ko7TRS
      (ko7PairRule KO7DPPairNode.recSucc)
      (ko7PairRule KO7DPPairNode.recSucc) h

theorem transGen_transport {α : Type} {R S : α → α → Prop}
  (hRS : ∀ {a b}, R a b → S a b)
  {a b : α} (h : Relation.TransGen R a b) :
  Relation.TransGen S a b := by
  induction h with
  | single hstep =>
    exact .single (hRS hstep)
  | tail hab hbc ih =>
    exact .tail ih (hRS hbc)

/-- Any realized KO7 real-edge path transports to a TCAP-estimated path over the
same schema nodes. -/
theorem real_dp_path_is_tcap_path {a b : KO7DPPairNode}
    (h : Relation.TransGen ko7RealDPEdge a b) :
    Relation.TransGen ko7EstimatedDPEdge a b :=
  transGen_transport
    (fun {x y} => estimated_dp_graph_tcap_overapproximation_sound (a := x) (b := y)) h

/-- `SCCCycle` transport specialized to the KO7 real-edge and estimated-edge
relations. This reuses the existing dependency-pair fragment cycle carrier. -/
theorem real_dp_cycle_is_tcap_cycle
    {source target : KO7DPPairNode}
    (h : Relation.TransGen ko7RealDPEdge source target) :
    ∃ C : SCCCycle KO7DPPairNode,
      C.Step = ko7EstimatedDPEdge ∧
      C.source = source ∧
      C.target = target := by
  refine ⟨
    { Step := ko7EstimatedDPEdge
      source := source
      target := target
      path := real_dp_path_is_tcap_path h },
    rfl, rfl, rfl⟩

abbrev witnessSymF : Nat := 10
abbrev witnessSymG : Nat := 11
abbrev witnessSymC : Nat := 12

def witnessFTm : FOTm := .app witnessSymF []
def witnessGTm : FOTm := .app witnessSymG []
def witnessCTm : FOTm := .app witnessSymC []

def witnessRewriteRule : Rule :=
  { lhs := witnessFTm, rhs := witnessGTm }

def witnessRules : List Rule := [witnessRewriteRule]

def witnessTRS : TRS where
  rules := witnessRules
  lhs_app := by
    intro r hr
    simp [witnessRules, witnessRewriteRule] at hr
    rcases hr with rfl
    exact ⟨witnessSymF, [], rfl⟩

def positiveSourcePair : Rule :=
  { lhs := witnessFTm, rhs := witnessFTm }

def positiveTargetPair : Rule :=
  { lhs := witnessGTm, rhs := witnessCTm }

def negativeSourcePair : Rule :=
  { lhs := witnessCTm, rhs := witnessCTm }

def negativeTargetPair : Rule :=
  { lhs := witnessFTm, rhs := witnessGTm }

/-- Concrete non-vacuity witness: a real edge that is covered by the estimate. -/
theorem positive_real_edge_witness :
    RealEdge witnessTRS positiveSourcePair positiveTargetPair := by
  refine ⟨idSubst, idSubst, ?_⟩
  apply Rstar.tail
  · exact Rstar.refl _
  · have hrule : witnessRewriteRule ∈ witnessTRS.rules := by
      simp [witnessTRS, witnessRules, witnessRewriteRule]
    simpa [witnessTRS, witnessRules, witnessRewriteRule, positiveSourcePair,
      positiveTargetPair, idSubst] using
      (Rstep.root witnessRewriteRule hrule idSubst)

/-- Concrete positive witness projected through the generic TCAP theorem. -/
theorem positive_real_edge_is_estimated :
    EstEdge witnessTRS positiveSourcePair positiveTargetPair :=
  estimated_dp_graph_tcap_unconditional witnessTRS
    positiveSourcePair positiveTargetPair positive_real_edge_witness

/-- A cap node matches an application only at the same head symbol. -/
theorem capMatches_node_app_head {f g : Nat} {cargs : List Cap} {targs : List FOTm} :
    CapMatches (Cap.node f cargs) (FOTm.app g targs) → f = g := by
  intro h; cases h; rfl

/-- Concrete non-vacuity witness: an absent estimated edge. -/
theorem negative_estimated_edge_witness :
    ¬ EstEdge witnessTRS negativeSourcePair negativeTargetPair := by
  intro h
  rcases h with ⟨u, hu, τ, huτ⟩
  have hu' : u = witnessFTm := by
    calc
      u = applySubst τ negativeTargetPair.lhs := by simpa using huτ.symm
      _ = witnessFTm := by simp [negativeTargetPair, witnessFTm]
  have huF : CapMatches (tcap witnessTRS.rules negativeSourcePair.rhs) witnessFTm := by
    simpa [hu'] using hu
  have htcap : tcap witnessTRS.rules negativeSourcePair.rhs = Cap.node witnessSymC [] := by
    show tcap witnessRules (FOTm.app witnessSymC []) = Cap.node witnessSymC []
    rw [tcap_app, if_neg (show ¬ (definedB witnessRules witnessSymC = true) by decide),
      tcapList_nil]
  rw [htcap] at huF
  exact absurd (capMatches_node_app_head huF) (by decide)

/-- Audit anchor for the KO7 TCAP soundness wrapper lane. -/
def audit_estimated_dp_graph_tcap_soundness_anchor : String :=
  "OperatorKO7.Meta.EstimatedDPGraphTCAPSoundness.estimated_dp_graph_tcap_overapproximation_sound"

end OperatorKO7.Meta.EstimatedDPGraphTCAPSoundness
