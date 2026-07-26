import OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7LocalCone

/-!
# Canonical local-peak extraction for the KO7 equality cone

This module exhaustively enumerates the three nodes of `KO7LocalCone`, forms
all ordered node pairs, and retains the canonically ordered pairs whose two
components are successors of `source`. The Boolean successor tests are proved
equivalent to `LocalRaw` and `LocalLicensed`; the imported cone bridges those
relations to `Step` and `SafeStep` on the embedded traces.

The resulting count concerns the fixed three-node cone at
`eqW void void`. It is not a critical-pair extractor for the full rewrite
system.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7CriticalPairDefect

open OperatorKO7 Trace
open MetaSN_KO7
open KO7LocalCone

/-- Exhaustive constructor list for the three-node local cone. -/
def allNodes : List EqWBreakerNode :=
  [.source, .reflVerdict, .diffVerdict]

theorem allNodes_nodup : allNodes.Nodup := by decide

theorem allNodes_complete (x : EqWBreakerNode) : x ∈ allNodes := by
  cases x <;> decide

/-- A fixed constructor rank used to count each unordered local peak once. -/
def nodeRank : EqWBreakerNode → Nat
  | .source => 0
  | .reflVerdict => 1
  | .diffVerdict => 2

/-- Boolean test for a raw successor of the cone source. -/
def rawSuccessor : EqWBreakerNode → Bool
  | .source => false
  | .reflVerdict | .diffVerdict => true

/-- Boolean test for a licensed successor of the cone source. -/
def licensedSuccessor : EqWBreakerNode → Bool
  | .reflVerdict => true
  | .source | .diffVerdict => false

@[simp] theorem raw_source_source_false : ¬ LocalRaw .source .source := by
  intro h
  cases h

@[simp] theorem raw_source_refl : LocalRaw .source .reflVerdict :=
  LocalRaw.refl

@[simp] theorem raw_source_diff : LocalRaw .source .diffVerdict :=
  LocalRaw.diff

@[simp] theorem licensed_source_source_false : ¬ LocalLicensed .source .source := by
  intro h
  cases h

@[simp] theorem licensed_source_refl : LocalLicensed .source .reflVerdict :=
  LocalLicensed.refl

@[simp] theorem licensed_source_diff_false : ¬ LocalLicensed .source .diffVerdict := by
  intro h
  cases h

theorem rawSuccessor_eq_true_iff (y : EqWBreakerNode) :
    rawSuccessor y = true ↔ LocalRaw .source y := by
  cases y <;> simp [rawSuccessor]

theorem licensedSuccessor_eq_true_iff (y : EqWBreakerNode) :
    licensedSuccessor y = true ↔ LocalLicensed .source y := by
  cases y <;> simp [licensedSuccessor]

/-- Cartesian square of the exhaustive node list. -/
def allNodePairs : List (EqWBreakerNode × EqWBreakerNode) :=
  allNodes.flatMap fun x => allNodes.map fun y => (x, y)

/-- Canonically oriented pairs of distinct successors selected by `successor`. -/
def canonicalLocalPeaks
    (successor : EqWBreakerNode → Bool) :
    List (EqWBreakerNode × EqWBreakerNode) :=
  allNodePairs.filter fun p =>
    successor p.1 && successor p.2 && decide (nodeRank p.1 < nodeRank p.2)

/-- Exhaustively extracted raw local peaks in the three-node cone. -/
def rawCriticalPairs : List (EqWBreakerNode × EqWBreakerNode) :=
  canonicalLocalPeaks rawSuccessor

/-- Exhaustively extracted licensed local peaks in the three-node cone. -/
def licensedCriticalPairs : List (EqWBreakerNode × EqWBreakerNode) :=
  canonicalLocalPeaks licensedSuccessor

/-- Membership is equivalent to being a canonically ordered raw peak at `source`. -/
theorem mem_rawCriticalPairs_iff (p : EqWBreakerNode × EqWBreakerNode) :
    p ∈ rawCriticalPairs ↔
      LocalRaw .source p.1 ∧ LocalRaw .source p.2 ∧ nodeRank p.1 < nodeRank p.2 := by
  rcases p with ⟨x, y⟩
  cases x <;> cases y <;>
    simp [rawCriticalPairs, canonicalLocalPeaks, allNodePairs, allNodes,
      rawSuccessor, nodeRank]

/-- Membership is equivalent to being a canonically ordered licensed peak at `source`. -/
theorem mem_licensedCriticalPairs_iff (p : EqWBreakerNode × EqWBreakerNode) :
    p ∈ licensedCriticalPairs ↔
      LocalLicensed .source p.1 ∧ LocalLicensed .source p.2 ∧ nodeRank p.1 < nodeRank p.2 := by
  rcases p with ⟨x, y⟩
  cases x <;> cases y <;>
    simp [licensedCriticalPairs, canonicalLocalPeaks, allNodePairs, allNodes,
      licensedSuccessor, nodeRank]

/-- Raw extracted peaks correspond to `Step` successors of the embedded source. -/
theorem mem_rawCriticalPairs_step_iff (p : EqWBreakerNode × EqWBreakerNode) :
    p ∈ rawCriticalPairs ↔
      Step (embed .source) (embed p.1) ∧
      Step (embed .source) (embed p.2) ∧
      nodeRank p.1 < nodeRank p.2 := by
  rw [mem_rawCriticalPairs_iff]
  simp only [raw_step_iff]

/-- Licensed extracted peaks correspond to `SafeStep` successors of the embedded source. -/
theorem mem_licensedCriticalPairs_safeStep_iff
    (p : EqWBreakerNode × EqWBreakerNode) :
    p ∈ licensedCriticalPairs ↔
      SafeStep (embed .source) (embed p.1) ∧
      SafeStep (embed .source) (embed p.2) ∧
      nodeRank p.1 < nodeRank p.2 := by
  rw [mem_licensedCriticalPairs_iff]
  simp only [licensed_step_iff]

/-- Number of unequal endpoint pairs in an extracted local-peak list. -/
def localDefectCount (pairs : List (EqWBreakerNode × EqWBreakerNode)) : Nat :=
  (pairs.filter fun p => decide (p.1 != p.2)).length

theorem rawCriticalPairs_eq :
    rawCriticalPairs = [(.reflVerdict, .diffVerdict)] := by decide

theorem licensedCriticalPairs_eq : licensedCriticalPairs = [] := by decide

theorem raw_localDefectCount_eq_one : localDefectCount rawCriticalPairs = 1 := by decide
theorem licensed_localDefectCount_eq_zero : localDefectCount licensedCriticalPairs = 0 := by decide

theorem guard_removes_unique_local_defect :
    localDefectCount rawCriticalPairs = localDefectCount licensedCriticalPairs + 1 := by decide

#print axioms allNodes_complete
#print axioms mem_rawCriticalPairs_iff
#print axioms mem_licensedCriticalPairs_iff
#print axioms mem_rawCriticalPairs_step_iff
#print axioms mem_licensedCriticalPairs_safeStep_iff
#print axioms raw_localDefectCount_eq_one
#print axioms licensed_localDefectCount_eq_zero
#print axioms guard_removes_unique_local_defect

end OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7CriticalPairDefect
