import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel

/-! Declaration, axiom, and concrete execution checks for the free recursor. -/

set_option autoImplicit false

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorStep
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorStep

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorDPPair
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorDPPair

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootNext
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootNext

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpNext
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpNext

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootNext_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootNext_iff

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpNext_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpNext_iff

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.extractCall
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.extractCall

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.extractCall_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.extractCall_iff

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_extraction_sound
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_extraction_sound

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_extraction_complete
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_extraction_complete

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.deltaPrefix
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.deltaPrefix

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.stripDelta
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.stripDelta

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpRank
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpRank

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_rank_exact
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_rank_exact

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_rank_decreases
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_rank_decreases

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpMachine
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpMachine

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpMachine_step_eq
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.dpMachine_step_eq

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_rev_wellFounded
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_rev_wellFounded

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_deterministic
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_deterministic

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_confluent
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_confluent

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_length
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_length

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_normalize
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_normalize

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootWeight
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootWeight

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootWeight_decreases
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootWeight_decreases

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootMachine
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootMachine

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootMachine_step_eq
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootMachine_step_eq

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_step_rev_wellFounded
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_step_rev_wellFounded

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_root_confluent
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_root_confluent

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_normalization_certificate
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_normalization_certificate

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.ExtendedStep
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.ExtendedStep

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.ExtractionComplete
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.ExtractionComplete

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.PairFree
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.PairFree

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.CompatibleExtra
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.CompatibleExtra

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootExtension_extraction_complete_iff_compatible
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootExtension_extraction_complete_iff_compatible

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootExtension_extraction_complete_iff_added_rules_pair_free
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootExtension_extraction_complete_iff_added_rules_pair_free

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.pair_free_extension_extraction_complete
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.pair_free_extension_extraction_complete

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.repeated_root_rules_preserve_extraction
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.repeated_root_rules_preserve_extraction

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.spuriousEdge
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.spuriousEdge

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.spurious_not_step
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.spurious_not_step

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.spurious_not_dp
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.spurious_not_dp

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.spurious_extension_pair_free
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.spurious_extension_pair_free

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_step_nonvacuous
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_step_nonvacuous

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_nonvacuous
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_dp_nonvacuous

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootExtension_pair_free_criterion_needs_disjointness
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootExtension_pair_free_criterion_needs_disjointness

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorStep.zero
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorStep.zero

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorStep.succ
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorStep.succ

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorDPPair.succ
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.FreeRecursorDPPair.succ

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_root_deterministic
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_root_deterministic

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_successor_root_cost
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.freeRecursor_successor_root_cost

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.newEdges
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.newEdges

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootExtension_extraction_complete_iff_new_edges_pair_free
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.rootExtension_extraction_complete_iff_new_edges_pair_free

#check @OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.wrong_rhs_extension_not_complete
#print axioms OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel.wrong_rhs_extension_not_complete

namespace OperatorKO7.Test.FreeRecursorKernelReach

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel

example : FreeRecursorStep
    (.recR .void .void (.delta .void))
    (.app .void (.recR .void .void .void)) :=
  freeRecursor_step_nonvacuous

example : extractCall
    (.recR .void .void (.delta .void))
    (.app .void (.recR .void .void .void)) =
      some (.recR .void .void .void) := by
  decide

example : extractCall
    (.recR .void .void (.delta .void)) .void = none := by
  decide

example : ¬ FreeRecursorDPPair
    (.recR .void .void (.delta .void))
    (.app .void (.recR .void .void .void)) := by
  intro h
  cases h

example : dpMachine.cost
    (.recR .void .void (.delta (.delta (.delta .void)))) = 3 := by
  rw [freeRecursor_dp_length]
  rfl

example : dpMachine.normalize
    (.recR .void .void (.delta (.delta (.delta .void)))) =
      .recR .void .void .void := by
  rw [freeRecursor_dp_normalize]
  rfl

example : rootMachine.normalize
    (.recR (.recR .void .void .void) .void .void) = .void := by
  rw [rootMachine.normalize_step (show rootMachine.Step
    (.recR (.recR .void .void .void) .void .void)
    (.recR .void .void .void) from rfl)]
  rw [rootMachine.normalize_step (show rootMachine.Step
    (.recR .void .void .void) .void from rfl)]
  exact rootMachine.normalize_terminal rfl

example : ExtractionComplete (ExtendedStep spuriousEdge) :=
  pair_free_extension_extraction_complete spurious_extension_pair_free

example : ExtractionComplete (ExtendedStep FreeRecursorStep) ∧
    ¬ PairFree FreeRecursorStep :=
  repeated_root_rules_preserve_extraction

example : rootMachine.cost (.recR .void .void (.delta (.delta (.delta .void)))) = 1 :=
  freeRecursor_successor_root_cost _ _ _

example (extra : RecursorTerm → RecursorTerm → Prop) :
    ExtractionComplete (ExtendedStep extra) ↔ PairFree (newEdges extra) :=
  rootExtension_extraction_complete_iff_new_edges_pair_free extra

end OperatorKO7.Test.FreeRecursorKernelReach
