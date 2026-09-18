import OperatorKO7.Meta.DistinctionBoundary.UniqueCheck
import OperatorKO7.Meta.DistinctionBoundary.ContextualConfluence
import OperatorKO7.Meta.DistinctionBoundary.WriteClosure
import OperatorKO7.Meta.DistinctionBoundary.SafeStepDeltaConfluence
import OperatorKO7.Meta.DistinctionBoundary.KO7RootDPExtraction
import OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance
import OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.API

set_option autoImplicit false

/-!
# Distinction Boundary crown

This module is a paper-facing conjunction of previously proved results. It adds
no new rewrite relation, repair algorithm, dependency-pair processor, or dynamic
grade semantics. Each conjunct is discharged by the named source theorem.

The crown records nine linked facts: the raw relation has one diagonal defect;
root repair forces disequality; the resulting comparator is the unique total
check under the declared interface; the root repair expires under unrestricted
context; the positional confluence condition is characterized by the frozen
`eqW` position and the two `recD` write dependencies; `confluenceRepair` is a
confluent least write-closed extension of the requested non-`eqW` positions;
the expanded licensed SafeStep context is confluent; the KO7 root dependency-
pair channel is complete for the single extracting rule and its role signal is
external to the value-only interface; and the stable KO7 pair inhabits D2 in
the declared internal comparator language.

Relation scope: `Step`, `EqGuardedStep`, `EqGuardedStepCtx`, positional
`CtxOnPos _ EqGuardedStep`, expanded contextual `SafeStep`, and root `DPPair`.
Closure scope: root where stated; reflexive-transitive contextual closure in the
contextual components. Trust: kernel-checked Lean plus the Mathlib baseline
axioms inherited by the imported theorem proofs.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.DistinctionBoundaryCrown

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.Meta.DistinctionBoundary.FreezePositions

/-- Composite paper-facing crown. Every component is an application or direct
re-export of an existing theorem; this declaration introduces no new proof
mechanism.

Relation: mixed, component-scoped as documented in the module header.
Property: theorem bundle / paper-facing API.
-/
theorem distinction_boundary_crown :
    -- A. Raw defect and strict relation sandwich.
    (∀ s t : Trace,
      (Step s t ∧ ¬ EqGuardedStep s t) ↔
        ConservativeRepair.DiagonalDifferenceEdge s t) ∧
    (∃ s t : Trace, Step s t ∧ ¬ EqGuardedStep s t) ∧
    (∃ s t : Trace, EqGuardedStep s t ∧ ¬ MetaSN_KO7.SafeStep s t) ∧
    -- B. Forced disequality and greatest admissible root repair.
    (∀ g : Trace → Trace → Prop,
      (ConservativeRepair.DiagSafe g ∧ ConservativeRepair.OffDiagonalComplete g) ↔
        ∀ a b, g a b ↔ a ≠ b) ∧
    ConservativeRepair.AdmissibleRepair EqGuardedStep ∧
    (∀ R : Trace → Trace → Prop,
      ConservativeRepair.AdmissibleRepair R →
        ∀ s t, R s t → EqGuardedStep s t) ∧
    (∀ R : Trace → Trace → Prop,
      ConservativeRepair.AdmissibleRepair R →
      (∀ s t, EqGuardedStep s t → R s t) →
        ∀ s t, R s t ↔ EqGuardedStep s t) ∧
    (∀ (R : Trace → Trace → Prop),
      ConservativeRepair.AdmissibleRepair R →
        ∀ a b : Trace,
          R (eqW a b) (integrate (merge a b)) ↔ a ≠ b) ∧
    -- C. One-check boundary.
    ((∀ (R : Trace → Trace → Prop),
        ConservativeRepair.AdmissibleRepair R → ∀ a b : Trace,
          R (eqW a b) (integrate (merge a b)) ↔ a ≠ b) ∧
      (∀ (c₁ c₂ : Trace → Trace → Bool),
        UniqueCheck.IsCheck c₁ → UniqueCheck.IsCheck c₂ →
          ∀ a b, c₁ a b = c₂ a b) ∧
      (∀ {β : Type} (h : Trace → β) (c' : β → β → Bool),
        UniqueCheck.IsCheck (fun a b : Trace => c' (h a) (h b)) →
          Function.Injective h) ∧
      (¬ ∃ t : Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm,
        ∀ a b : Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm,
          (a ≠ b) ↔
            (Meta.SafeStep.SigmaFreeAlgebra.evalSigma a b t ≠
              Meta.SafeStep.SigmaFreeAlgebra.SigmaTerm.void)) ∧
      (UniqueCheck.IsCheck DiscriminatorExtension.structEq ∧
        ∀ (c : Trace → Trace → Bool), UniqueCheck.IsCheck c →
          ∀ a b, c a b = DiscriminatorExtension.structEq a b)) ∧
    -- D. Root minimality expires under context.
    (EqGuardedConfluence.ConfluentEqGuarded ∧
      ¬ ContextualConfluence.ConfluentEqGuardedCtx) ∧
    (∃ a b : Trace,
      a ≠ b ∧
      ContextualConfluence.EqGuardedStepCtx (eqW a b)
        (integrate (merge a b)) ∧
      ContextualConfluence.EqGuardedStepCtx (eqW a b) (eqW b b) ∧
      ContextualConfluence.EqGuardedCtxStar (integrate (merge a b))
        (integrate void) ∧
      ContextualConfluence.EqGuardedCtxStar (eqW b b) void ∧
      ¬ ∃ d,
        ContextualConfluence.EqGuardedCtxStar (integrate void) d ∧
        ContextualConfluence.EqGuardedCtxStar void d) ∧
    -- E. Positional crown and least write-closed confluence repair.
    (∀ S : CtorPos → Prop,
      ConfluentOnPos S EqGuardedStep ↔
        (¬ S .eqW ∧ (S .recD → S .appL) ∧ (S .recD → S .appR))) ∧
    (∀ S : CtorPos → Prop,
      ConfluentOnPos (WriteClosure.confluenceRepair S) EqGuardedStep) ∧
    (∀ S T : CtorPos → Prop,
      ConfluentOnPos T EqGuardedStep →
      (∀ c, S c → c ≠ .eqW → T c) →
        WriteClosure.SelectionLE (WriteClosure.confluenceRepair S) T) ∧
    -- F. Licensed contextual confluence and the complete root DP-role channel.
    DeltaThawBoundary.safeStepDeltaCongruenceConfluent ∧
    (SafeStepDeltaConfluence.SafeDelta
        (delta (merge void void)) (delta void) ∧
      ¬ MetaSN_KO7.SafeStepCtx (delta (merge void void)) (delta void)) ∧
    (∀ a b : Trace, (h : Step a b) →
      (KO7RootDPExtraction.extractsDP h ↔ ∃ c, DPPair a c) ∧
      (∀ c, DPPair a c → dpRank c < dpRank a) ∧
      WellFounded DPPairRev) ∧
    (∀ b s n : Trace,
      DPChannelInstance.actualDPChannel b s n
          (((), RoleErasureInstance.Role.frame) : RoleErasureInstance.Occ Unit) ≠
        DPChannelInstance.actualDPChannel b s n
          (((), RoleErasureInstance.Role.active) : RoleErasureInstance.Occ Unit)) ∧
    (∀ b s n : Trace,
      ¬ ∃ g : Unit → Bool, ∀ o : RoleErasureInstance.Occ Unit,
        DPChannelInstance.actualDPChannel b s n o = g o.1) ∧
    -- Dynamic-grade conclusion.
    DynamicDiagonalGrade.D2At
      DynamicDiagonalGrade.TraceComparatorRepresented EqGuardedStep
      (id : Trace → Trace) (delta void) void := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t
    exact ConservativeRepair.step_and_not_eqGuarded_iff s t
  · exact ConservativeRepair.eqGuardedStep_strict_subset_step
  · exact ConservativeRepair.safeStep_strict_subset_eqGuardedStep
  · intro g
    exact ConservativeRepair.diagSafe_offDiagonalComplete_iff_disequality g
  · exact ConservativeRepair.eqGuardedStep_unique_greatest_admissible.1
  · exact ConservativeRepair.eqGuardedStep_unique_greatest_admissible.2.1
  · exact ConservativeRepair.eqGuardedStep_unique_greatest_admissible.2.2
  · intro R hR a b
    exact ConservativeRepair.conservative_repair_forces_exact_distinction hR a b
  · exact UniqueCheck.one_check_boundary
  · exact ContextualConfluence.root_confluent_but_ctx_not
  · exact ContextualConfluence.contextual_repair_needs_more_than_root_guard
  · intro S
    exact FreezePositions.confluentOnPos_eqGuarded_iff S
  · intro S
    exact WriteClosure.confluenceRepair_confluent S
  · intro S T hT hExt
    exact WriteClosure.confluenceRepair_least hT hExt
  · exact SafeStepDeltaConfluence.safeStepDeltaCongruenceConfluent_holds
  · exact SafeStepDeltaConfluence.expanded_strictly_extends_ctx
  · intro a b h
    exact KO7RootDPExtraction.processor_sound h
  · intro b s n
    exact DPChannelInstance.actual_dp_license_is_exogenous_separator b s n
  · intro b s n
    exact DPChannelInstance.actual_dp_license_not_value_factored b s n
  · exact DynamicDiagonalGrade.ko7_stable_pair_d2

#check @distinction_boundary_crown
#print axioms distinction_boundary_crown

/-- Additive extension of the existing crown by the schema-first minimal-fork
crown. The existing `distinction_boundary_crown` declaration and its exact type
remain unchanged. This definition is proof-bearing; its inferred type is the
conjunction of the complete legacy crown proposition and `MinimalForkCrown`. -/
def distinctionBoundaryCrown_extended :=
  And.intro distinction_boundary_crown
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.minimal_distinction_boundary_crown

#check @distinctionBoundaryCrown_extended
#print axioms distinctionBoundaryCrown_extended

end OperatorKO7.Meta.DistinctionBoundary.DistinctionBoundaryCrown
