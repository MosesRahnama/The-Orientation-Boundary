import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder

/-! # Free-recursor witness-order declaration and axiom checks -/

set_option autoImplicit false

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder
open OperatorKO7.RepShift

#check @counterObservation
#print axioms counterObservation

#check @payloadObservation
#print axioms payloadObservation

#check @counterTerm
#print axioms counterTerm

#check @payloadTerm
#print axioms payloadTerm

#check @deltaPrefix_counterTerm
#print axioms deltaPrefix_counterTerm

#check @counterObservation_payloadTerm
#print axioms counterObservation_payloadTerm

#check @payloadObservation_payloadTerm
#print axioms payloadObservation_payloadTerm

#check @profileMeasure
#print axioms profileMeasure

#check @successor_profile
#print axioms successor_profile

#check @every_successor_profile_attained
#print axioms every_successor_profile_attained

#check @profile_orients_successors_iff
#print axioms profile_orients_successors_iff

#check @DirectWholeWitness
#print axioms DirectWholeWitness

#check @freeRecursor_no_directWhole
#print axioms freeRecursor_no_directWhole

#check @ImportedWholeWitness
#print axioms ImportedWholeWitness

#check @ImportedWholeWitness.wellFounded
#print axioms ImportedWholeWitness.wellFounded

#check @derivationHeight
#print axioms derivationHeight

#check @derivationHeight_step
#print axioms derivationHeight_step

#check @importedWholeWitness
#print axioms importedWholeWitness

#check @freeRecursor_has_importedWhole
#print axioms freeRecursor_has_importedWhole

#check @ImportedWholeWitness.bounds_steps
#print axioms ImportedWholeWitness.bounds_steps

#check @derivationHeight_pointwise_least
#print axioms derivationHeight_pointwise_least

#check @derivationHeight_zero_rule
#print axioms derivationHeight_zero_rule

#check @derivationHeight_successor
#print axioms derivationHeight_successor

#check @derivationHeight_not_profile_factored
#print axioms derivationHeight_not_profile_factored

#check @TransformedCallWitness
#print axioms TransformedCallWitness

#check @transformedCallWitness
#print axioms transformedCallWitness

#check @TransformedCallWitness.wellFounded
#print axioms TransformedCallWitness.wellFounded

#check @freeRecursor_has_transformedCall
#print axioms freeRecursor_has_transformedCall

#check @erased_counter_cannot_decode_dp
#print axioms erased_counter_cannot_decode_dp

#check @ErasedCounterDecoder
#print axioms ErasedCounterDecoder

#check @no_erasedCounterDecoder
#print axioms no_erasedCounterDecoder

#check @RootTerminates
#print axioms RootTerminates

#check @ExternalWitness
#print axioms ExternalWitness

#check @externalWitness
#print axioms externalWitness

#check @TruthEvidence
#print axioms TruthEvidence

#check @BoundaryEvidence
#print axioms BoundaryEvidence

#check @truthEvidence_sound
#print axioms truthEvidence_sound

#check @boundaryEvidence_sound
#print axioms boundaryEvidence_sound

#check @truthHierarchy
#print axioms truthHierarchy

#check @boundaryHierarchy
#print axioms boundaryHierarchy

#check @truthHierarchy_adequate_iff
#print axioms truthHierarchy_adequate_iff

#check @boundaryHierarchy_adequate_iff
#print axioms boundaryHierarchy_adequate_iff

#check @kappaTruth
#print axioms kappaTruth

#check @kappaBoundary
#print axioms kappaBoundary

#check @freeRecursor_kappaTruth_eq_importedWhole
#print axioms freeRecursor_kappaTruth_eq_importedWhole

#check @freeRecursor_kappaBoundary_eq_transformedCall
#print axioms freeRecursor_kappaBoundary_eq_transformedCall

#check @freeRecursor_truth_representationShiftBottleneck
#print axioms freeRecursor_truth_representationShiftBottleneck

#check @freeRecursor_boundary_representationShiftBottleneck
#print axioms freeRecursor_boundary_representationShiftBottleneck

#check @truth_bottleneck_iff_depth_one
#print axioms truth_bottleneck_iff_depth_one

#check @boundary_bottleneck_iff_depth_two
#print axioms boundary_bottleneck_iff_depth_two

example : counterObservation (.recR (payloadTerm 4) (payloadTerm 6) (.delta (counterTerm 2))) = 3 := by decide
example : payloadObservation (.app (payloadTerm 6) (.recR (payloadTerm 4) (payloadTerm 6) (counterTerm 2))) = 11 := by decide

example : derivationHeight (.recR (.recR .void .void .void) .void .void) = 2 := by
  rw [derivationHeight_zero_rule, derivationHeight_zero_rule]
  have h : derivationHeight .void = 0 := rootMachine.cost_terminal rfl
  rw [h]

example : transformedCallWitness.extractor
    (.recR .void (.delta .void) (.delta .void))
    (.app (.delta .void) (.recR .void (.delta .void) .void)) =
      some (.recR .void (.delta .void) .void) := by
  simp [transformedCallWitness, extractCall]

example : kappaTruth (.merge .void .void) = 1 :=
  freeRecursor_kappaTruth_eq_importedWhole _

example : kappaBoundary (.merge .void .void) = 2 :=
  freeRecursor_kappaBoundary_eq_transformedCall _

example : ¬ RepresentationShiftBottleneck truthHierarchy RootTerminates .void 2 := by
  rw [truth_bottleneck_iff_depth_one]
  decide

example : ¬ RepresentationShiftBottleneck boundaryHierarchy RootTerminates .void 1 := by
  rw [boundary_bottleneck_iff_depth_two]
  decide

example : boundaryHierarchy.hasAdequateAtDepth 20 RootTerminates .void :=
  (boundaryHierarchy_adequate_iff 20 _).mpr (by decide)
