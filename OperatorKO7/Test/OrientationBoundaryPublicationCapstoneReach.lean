import OperatorKO7.Meta.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone

set_option autoImplicit false

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone.free_successor_orientation_iff_payloadBlind_and_counterStrict
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone.free_successor_orientation_iff_payloadBlind_and_counterStrict

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone.free_successor_orientation_allCarriers_iff_payloadBlind_and_counterStrict
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone.free_successor_orientation_allCarriers_iff_payloadBlind_and_counterStrict

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone.free_successor_counterAdmissible_orients_iff_payloadBlind
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone.free_successor_counterAdmissible_orients_iff_payloadBlind

#check @OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone.no_decisive_certificate_of_payload_erasure
#print axioms OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone.no_decisive_certificate_of_payload_erasure

/-! ## Non-vacuity controls at the carrier `Bool` -/

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.AttainedPairs
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone

/-- The left side holds at `Bool` for the counter projection. -/
example : ∀ b s n : FreeTerm Bool,
    profileMeasure MeasureExpr.counter.eval (.wrap s (.recur b s n)) <
      profileMeasure MeasureExpr.counter.eval (.recur b s (.succ n)) :=
  (free_successor_orientation_iff_payloadBlind_and_counterStrict (ν := Bool)
    MeasureExpr.counter).2 ⟨fun _ _ _ => rfl, fun c _ => Nat.lt_succ_self c⟩

/-- The left side fails at `Bool` for the payload projection. -/
example : ¬ ∀ b s n : FreeTerm Bool,
    profileMeasure MeasureExpr.payload.eval (.wrap s (.recur b s n)) <
      profileMeasure MeasureExpr.payload.eval (.recur b s (.succ n)) := by
  intro h
  have hblind :=
    ((free_successor_orientation_iff_payloadBlind_and_counterStrict (ν := Bool)
      MeasureExpr.payload).1 h).1
  have h01 := hblind 0 0 1
  simp [MeasureExpr.eval] at h01
