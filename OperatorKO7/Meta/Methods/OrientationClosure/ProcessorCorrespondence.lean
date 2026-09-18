import OperatorKO7.Meta.Methods.OrientationClosure.SourceChainSoundness
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairNativeSemantics

/-!
# Processor correspondence for dependency-pair chains

This module connects the existing native reduction-pair object to the generic
same-input chain theorem.  The strict dependency-pair edge and the weak source
connector are certified by the same `NativeReductionPair` object.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.ProcessorCorrespondence

open OperatorKO7
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.Methods.OrientationClosure.SourceChainSoundness
open OperatorKO7.Methods.OrientationClosure.DependencyPairNativeSemantics

/-- A native reduction pair is exactly a connector-aware chain reduction pair
for the KO7 transformed-call relation and source root relation. -/
def toChainReductionPair (P : NativeReductionPair) :
    ChainReductionPair Trace DPPair Step where
  weak := P.weak
  strict := P.strict
  weak_refl := P.weak_refl
  weak_trans := P.weak_trans
  strict_reverse_wellFounded := P.strict_reverse_wellFounded
  pair_strict := P.pairs_strict
  connector_weak := P.rules_weak
  strict_weak := P.strict_weak

/-- Every actual pair/source-connector chain step is strict in the exact native
reduction pair supplied to the theorem. -/
theorem nativeReductionPair_chain_strict
    (P : NativeReductionPair) {a c : Trace}
    (h : ChainStep DPPair Step a c) : P.strict a c := by
  exact chainStep_strict (toChainReductionPair P) h

/-- Native reduction-pair semantics prove well-foundedness of the composed
pair-plus-source-connector chain, not merely the isolated pair relation. -/
theorem nativeReductionPair_chain_wellFounded (P : NativeReductionPair) :
    WellFounded (fun y x : Trace => ChainStep DPPair Step x y) :=
  chainStep_wellFounded (toChainReductionPair P)

/-- The polynomial native reduction pair supplies the chain theorem. -/
theorem polynomial_chain_wellFounded :
    WellFounded (fun y x : Trace => ChainStep DPPair Step x y) :=
  nativeReductionPair_chain_wellFounded polynomialReductionPair

/-- The gap-two native reduction pair supplies the same chain theorem through a
genuinely different strict relation. -/
theorem gapTwo_chain_wellFounded :
    WellFounded (fun y x : Trace => ChainStep DPPair Step x y) :=
  nativeReductionPair_chain_wellFounded gapTwoReductionPair

/-- The two successful chain processors really use different strict relations. -/
theorem chain_processors_relation_distinct :
    polynomialReductionPair.strict ≠ gapTwoReductionPair.strict := by
  exact dependencyPairNativeBundle.relationSeparation

/-! ## Connector reset control -/

/-- Pair edge from `true` to `false`. -/
def ResetPair (a b : Bool) : Prop := a = true ∧ b = false

/-- Connector edge resets `false` back to `true`. -/
def ResetConnector (a b : Bool) : Prop := a = false ∧ b = true

/-- The isolated pair relation is well founded. -/
theorem resetPair_wellFounded :
    WellFounded (fun y x : Bool => ResetPair x y) := by
  let rank : Bool → Nat := fun b => if b then 1 else 0
  apply Subrelation.wf (r := fun y x : Bool => rank y < rank x)
  · intro y x h
    rcases h with ⟨rfl, rfl⟩
    decide
  · exact InvImage.wf rank Nat.lt_wfRel.wf

/-- Pair-plus-connector composition has an explicit self-loop when connector
weakness is not enforced. -/
theorem reset_chain_self_loop :
    ChainStep ResetPair ResetConnector true true := by
  refine ⟨false, ⟨rfl, rfl⟩, ?_⟩
  exact Relation.ReflTransGen.single ⟨rfl, rfl⟩

/-- Therefore pair well-foundedness alone does not prove dependency-chain
well-foundedness in the presence of arbitrary connectors. -/
theorem reset_chain_not_wellFounded :
    ¬ WellFounded (fun y x : Bool => ChainStep ResetPair ResetConnector x y) := by
  intro hwf
  exact (hwf.asymmetric true true reset_chain_self_loop) reset_chain_self_loop

/-- Load-bearing connector control in one theorem. -/
theorem connector_compatibility_is_necessary_control :
    WellFounded (fun y x : Bool => ResetPair x y) ∧
      ¬ WellFounded (fun y x : Bool => ChainStep ResetPair ResetConnector x y) :=
  ⟨resetPair_wellFounded, reset_chain_not_wellFounded⟩

end OperatorKO7.Methods.OrientationClosure.ProcessorCorrespondence
