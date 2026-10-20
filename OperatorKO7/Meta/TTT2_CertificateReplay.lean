import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.DependencyPairs_TPDBExtraction
import OperatorKO7.Meta.DependencyPairs_FirstOrderExtraction
import OperatorKO7.Meta.DependencyPairs_KernelFirstOrder
import OperatorKO7.Meta.TPDB_Export

/-!
# Internal dependency-pair replay metadata for KO7

This module constructs an internal `FastDPReplay` record around `ko7ProjectionProblem`. It does not
parse a CPF certificate or read an external artifact. The projection indices and count fields are
literal metadata. The export theorem compares two Lean string constants, the extraction theorems
inspect Lean encodings of the KO7 rules, and the soundness theorem reuses the internally proved
well-foundedness of `ko7ProjectionProblem`.

These declarations establish consistency among the in-repository encodings. They are not an
independent checker replay of an external TTT2 or CeTA certificate.
-/

open OperatorKO7 Trace

namespace OperatorKO7.TTT2CertificateReplay

open OperatorKO7.DependencyPairsFragment
open OperatorKO7.MetaDependencyPairs

/-- Record containing two projection-index conventions, two literal counts, and an internal
dependency-pair projection problem. -/
structure FastDPReplay where
  projectionIndexTool : Nat
  projectionIndexPaper : Nat
  pairCount : Nat
  singletonRealSccCount : Nat
  projectionProblem : DPProjection Trace

/-- The KO7 replay record with fixed metadata and `ko7ProjectionProblem` as its proof-bearing field. -/
def ko7FastReplay : FastDPReplay where
  projectionIndexTool := 2
  projectionIndexPaper := 3
  pairCount := 1
  singletonRealSccCount := 1
  projectionProblem := ko7ProjectionProblem

theorem ko7FastReplay_indices :
    ko7FastReplay.projectionIndexTool + 1 = ko7FastReplay.projectionIndexPaper := by
  decide

theorem ko7FastReplay_pairCount :
    ko7FastReplay.pairCount = 1 := rfl

theorem ko7FastReplay_singletonRealScc :
    ko7FastReplay.singletonRealSccCount = 1 := rfl

/-- The replay record's projection problem has `DPPair` as its pair relation by definition. -/
theorem ko7FastReplay_uses_recSucc_pair :
    ko7FastReplay.projectionProblem.Pair = DPPair := rfl

/-- Two Lean constants containing the exported and artifact-labelled TPDB text are equal. This
theorem performs no filesystem read and does not identify a submitted external file. -/
theorem ko7FastReplay_export_text_matches_artifact :
    OperatorKO7.ko7_full_step_tpdb = OperatorKO7.ko7_full_step_tpdb_artifact_text :=
  OperatorKO7.ko7_full_step_tpdb_matches_artifact_text

/-- The Lean TPDB rule encoding contains a node whose key and successor set are both `recD`. -/
theorem ko7FastReplay_export_has_recD_successor :
    ∃ n ∈ OperatorKO7.DependencyPairsFragment.ko7FullStepExtractedNodes.toList,
      n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String) := by
  exact OperatorKO7.DependencyPairsFragment.ko7_full_step_has_recD_successor

/-- Bundle the equality of the two Lean text constants, existence of a `recD` self-successor node,
and the definitional identification of the internal pair relation. The theorem does not prove
uniqueness of that node or parse an external artifact. -/
theorem ko7FastReplay_matches_export_surface :
    OperatorKO7.ko7_full_step_tpdb = OperatorKO7.ko7_full_step_tpdb_artifact_text ∧
      (∃ n ∈ OperatorKO7.DependencyPairsFragment.ko7FullStepExtractedNodes.toList,
        n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String)) ∧
      ko7FastReplay.projectionProblem.Pair = DPPair := by
  exact ⟨ko7FastReplay_export_text_matches_artifact,
    ko7FastReplay_export_has_recD_successor,
    ko7FastReplay_uses_recSucc_pair⟩

/-- Bundle the defined-head sets and existence of a `recD` self-successor node in three Lean rule
encodings, together with the text-constant equality and internal pair identification. The theorem
does not establish graph isomorphism, node uniqueness, or external certificate correspondence. -/
theorem ko7FastReplay_matches_all_extraction_surfaces :
    OperatorKO7.ko7_full_step_tpdb = OperatorKO7.ko7_full_step_tpdb_artifact_text ∧
      OperatorKO7.DependencyPairsFragment.tpdbDefinedHeads
        OperatorKO7.ko7FullStepTpdbRules.toArray =
        ({ "integrate", "merge", "recD", "eqW" } : Finset String) ∧
      OperatorKO7.DependencyPairsFragment.foDefinedHeads
        OperatorKO7.DependencyPairsFragment.KO7FirstOrder.ko7FullStepFORules =
        ({ "integrate", "merge", "recD", "eqW" } : Finset String) ∧
      OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7Engine.definedHeads =
        ({ OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.integrate,
           OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.merge,
           OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.recD,
           OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.eqW } :
          Finset OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol) ∧
      (∃ n ∈ OperatorKO7.DependencyPairsFragment.ko7FullStepExtractedNodes.toList,
        n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String)) ∧
      (∃ n ∈ OperatorKO7.DependencyPairsFragment.KO7FirstOrder.ko7FullStepExtractedNodes.toList,
        n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String)) ∧
      (∃ n ∈ OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7FullStepExtractedNodes.toList,
        n.nodeKey = OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.recD ∧
          n.succKeys =
            ({ OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol.recD } :
              Finset OperatorKO7.DependencyPairsFragment.KernelFirstOrder.Symbol)) ∧
      ko7FastReplay.projectionProblem.Pair = DPPair := by
  refine ⟨ko7FastReplay_export_text_matches_artifact, ?_, ?_, ?_, ?_, ?_, ?_, ko7FastReplay_uses_recSucc_pair⟩
  · exact OperatorKO7.DependencyPairsFragment.ko7_full_step_defined_heads
  · exact OperatorKO7.DependencyPairsFragment.KO7FirstOrder.ko7_full_step_defined_heads
  · exact OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7_full_step_defined_heads
  · exact ko7FastReplay_export_has_recD_successor
  · exact OperatorKO7.DependencyPairsFragment.KO7FirstOrder.ko7_full_step_has_recD_successor
  · exact OperatorKO7.DependencyPairsFragment.KernelFirstOrder.ko7_full_step_has_recD_successor

/-- The replay record inherits the rank decrease stored in its internal `DPProjection`. -/
theorem ko7FastReplay_subterm_drop :
    ∀ {a b : Trace}, ko7FastReplay.projectionProblem.Pair a b →
      ko7FastReplay.projectionProblem.rank b < ko7FastReplay.projectionProblem.rank a := by
  intro a b h
  exact ko7FastReplay.projectionProblem.decreases h

/-- The replay record's reverse relation is well-founded because its projection problem is
definitionally `ko7ProjectionProblem`, whose well-foundedness is imported. -/
theorem ko7FastReplay_sound :
    WellFounded ko7FastReplay.projectionProblem.Rev := by
  simpa [ko7FastReplay] using ko7ProjectionProblem.wfRev

/-- Restatement of the internal well-foundedness result for the alias `DPPairRev`. -/
theorem wf_DPPairRev_replayed : WellFounded DPPairRev := by
  simpa [DPPairRev, ko7FastReplay] using ko7FastReplay_sound

end OperatorKO7.TTT2CertificateReplay
