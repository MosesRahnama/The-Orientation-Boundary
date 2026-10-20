import OperatorKO7.Meta.Methods.OrientationClosure.DependentMethodEvidence
import OperatorKO7.Meta.Methods.OrientationClosure.ProcessorCorrespondence
import OperatorKO7.Meta.Methods.OrientationClosure.ExistingSixteenGeneralization
import OperatorKO7.Meta.ConfessionMethod_SCT

/-!
# Orientation certificate mutation controls

Semantic regression tests for the dependent method-evidence layer and the
dependency-pair chain interfaces. Each control pins one property: a returned
certificate stores the canonical interpretation of its row; removing one row
breaks the sixty-row coverage equality; the call extractor ties the call to the
actual right-hand side of the same source; a resetting connector defeats chain
well-foundedness; the size-change graph is strict only at the counter
coordinate; a neutral processor keeps every transformed call; and pair-chain
well-foundedness does not give source termination.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.CertificateControls

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.SourceChainSoundness
open OperatorKO7.Methods.OrientationClosure.ProcessorCorrespondence
open OperatorKO7.Methods.OrientationClosure.DependencyPairNativeSemantics
open OperatorKO7.Methods.OrientationClosure.ExistingSixteenGeneralization
open OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage
open OperatorKO7.Methods.OrientationClosure.DependentMethodEvidence

/-! ## Canonical stored interpretation -/

/-- A certificate returned for a row stores that row's canonical native
interpretation. -/
theorem dependentNativeCertificate_interpretation_canonical
    {f : RDRSMethodFamily} {c : DependentNativeCertificate f}
    (h : dependentNativeCertificate f = some c) :
    missingNativeInterpretation f = some c.interpretation := by
  unfold dependentNativeCertificate at h
  split at h
  · cases h
  · rename_i i hi
    cases h
    exact hi

/-- Two certificates returned for the same row coincide. -/
theorem dependentNativeCertificate_unique {f : RDRSMethodFamily}
    {c d : DependentNativeCertificate f}
    (hc : dependentNativeCertificate f = some c)
    (hd : dependentNativeCertificate f = some d) : c = d :=
  Option.some.inj (hc.symm.trans hd)

/-- The dependent layer leaves the historical rows to their older interface. -/
theorem standardKBO_has_no_dependent_certificate :
    dependentNativeCertificate .standardKBO = none := rfl

/-- The dependent layer leaves the Cichon row to its older interface. -/
theorem cichon_has_no_dependent_certificate :
    dependentNativeCertificate .cichonSlowGrowing = none := rfl

/-- A representative new row carries a certificate that stores its canonical
interpretation. -/
theorem kboWithStatus_certificate_canonical :
    ∃ c : DependentNativeCertificate .kboWithStatus,
      dependentNativeCertificate .kboWithStatus = some c ∧
        missingNativeInterpretation .kboWithStatus = some c.interpretation := by
  cases h : dependentNativeCertificate .kboWithStatus with
  | none =>
      have hs : (dependentNativeCertificate .kboWithStatus).isSome = true := rfl
      rw [h] at hs
      cases hs
  | some c => exact ⟨c, rfl, dependentNativeCertificate_interpretation_canonical h⟩

/-! ## Coverage mutation -/

/-- Removing one certified row changes the coverage set. -/
theorem dependentNativeRows_erase_kboWithStatus_length :
    (dependentNativeRows.erase .kboWithStatus).length = 59 := by
  rw [dependentNativeRows_eq_missingNativeInterpretationRows,
    missingNativeInterpretationRows_eq_missingNativeRows]
  decide

/-- Therefore the sixty-row coverage equality cannot survive that mutation. -/
theorem dependentNativeRows_erase_kboWithStatus_not_full :
    dependentNativeRows.erase .kboWithStatus ≠ missingNativeRows := by
  intro h
  have hlen := congrArg List.length h
  rw [dependentNativeRows_erase_kboWithStatus_length, missingNativeRows_count] at hlen
  omega

/-! ## Extraction mutations -/

/-- The successor source instance `recur 0 0 (succ 0)`. -/
def extractSource : FreeTerm Empty := .recur .zero .zero (.succ .zero)

/-- Its actual right-hand side `wrap 0 (recur 0 0 0)`. -/
def extractRHS : FreeTerm Empty := .wrap .zero (.recur .zero .zero .zero)

/-- The recursive call `recur 0 0 0`. -/
def extractCall : FreeTerm Empty := .recur .zero .zero .zero

/-- The source term extracts exactly the recursive call. -/
theorem extractSource_extracts_call :
    extractRecursiveCall extractSource = some extractCall := rfl

/-- The zero rule has no extracted call. -/
theorem zero_rule_extracts_nothing :
    extractRecursiveCall (.recur .zero .zero .zero : FreeTerm Empty) = none := rfl

/-- The call occurs in the actual right-hand side of the same source step. -/
theorem extractCall_occurs_in_source_rhs :
    RootStep extractSource extractRHS ∧
      FreeCallOccurrence extractSource extractRHS extractCall :=
  ⟨.recurSucc .zero .zero .zero, .successor .zero .zero .zero⟩

/-- The transformed call is not the right-hand side of the source step. -/
theorem call_as_rhs_rejected :
    ¬ FreeCallOccurrence extractSource extractCall extractCall := by
  unfold extractSource extractCall
  intro h
  cases h

/-- Changing the wrapper payload of the right-hand side breaks the occurrence. -/
theorem altered_payload_rhs_rejected :
    ¬ FreeCallOccurrence extractSource
      (.wrap (.succ .zero) (.recur .zero .zero .zero)) extractCall := by
  unfold extractSource extractCall
  intro h
  cases h

/-! ## Connector mutation -/

/-- A resetting connector makes the chain relation loop although the pair
relation alone is well founded. -/
theorem resetConnector_control :
    WellFounded (fun y x : Bool => ResetPair x y) ∧
      ChainStep ResetPair ResetConnector true true ∧
      ¬ WellFounded (fun y x : Bool => ChainStep ResetPair ResetConnector x y) :=
  ⟨resetPair_wellFounded, reset_chain_self_loop, reset_chain_not_wellFounded⟩

/-! ## Size-change graph coordinates -/

/-- The free recursive call is strict at the counter coordinate. -/
theorem sct_counter_coordinate_strict :
    schemaRecCallGraph.arcs ⟨2, by decide⟩ ⟨2, by decide⟩ = SCArc.strictDecrease := by
  decide

/-- Strictness at the base coordinate is not available. -/
theorem wrong_sct_base_coordinate_rejected :
    schemaRecCallGraph.arcs ⟨0, by decide⟩ ⟨0, by decide⟩ ≠ SCArc.strictDecrease := by
  decide

/-- Strictness at the payload coordinate is not available either. -/
theorem wrong_sct_payload_coordinate_rejected :
    schemaRecCallGraph.arcs ⟨1, by decide⟩ ⟨1, by decide⟩ ≠ SCArc.strictDecrease := by
  decide

/-! ## Neutral processor -/

/-- A processor that deletes every transformed call is not neutral for the free
call problem. -/
theorem empty_output_not_neutral :
    ¬ ∃ P : NeutralProcessorMethod (FreeTerm Empty) (@FreeRecursiveCallPair Empty),
      ∀ a b, ¬ P.output a b := by
  rintro ⟨P, hempty⟩
  exact hempty extractSource extractCall
    ((P.neutral extractSource extractCall).2 (.successor .zero .zero .zero))

/-! ## Pair-only source transfer -/

/-- The pair-free self-loop problem has well-founded pairs and a looping source,
so pair-chain well-foundedness alone does not give source termination. -/
theorem pair_only_source_transfer_rejected :
    WellFounded (fun y x : Unit => pairFreeSelfLoopProblem.pairStep x y) ∧
      ¬ WellFounded (fun y x : Unit => pairFreeSelfLoopProblem.sourceStep x y) := by
  refine ⟨⟨fun a => Acc.intro a (fun _ h => False.elim h)⟩, ?_⟩
  intro hwf
  have hloop : pairFreeSelfLoopProblem.sourceStep () () := trivial
  exact (hwf.asymmetric () () hloop) hloop

end OperatorKO7.Methods.OrientationClosure.CertificateControls
