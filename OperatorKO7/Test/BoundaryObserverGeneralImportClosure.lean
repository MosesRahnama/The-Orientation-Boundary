import OperatorKO7.Meta.BoundaryObserver.AcceptedCertificate
import OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation
import OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation
import OperatorKO7.Meta.BoundaryObserver.BitDivision
import OperatorKO7.Meta.BoundaryObserver.DemandComplex
import OperatorKO7.Meta.BoundaryObserver.DiagonalObservation
import OperatorKO7.Meta.BoundaryObserver.DynamicStopping
import OperatorKO7.Meta.BoundaryObserver.FiberStepOrientation
import OperatorKO7.Meta.BoundaryObserver.InstrumentLoss
import OperatorKO7.Meta.BoundaryObserver.KalmanObservability
import OperatorKO7.Meta.BoundaryObserver.KalmanSideRecord
import OperatorKO7.Meta.BoundaryObserver.KernelCases
import OperatorKO7.Meta.BoundaryObserver.LinearObservability
import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.BoundaryObserver.NoisyResolution
import OperatorKO7.Meta.BoundaryObserver.NullstellensatzObserver
import OperatorKO7.Meta.BoundaryObserver.ObservationTransport
import OperatorKO7.Meta.BoundaryObserver.ObserverDegenerateCases
import OperatorKO7.Meta.BoundaryObserver.ObserverFoundations
import OperatorKO7.Meta.BoundaryObserver.OccurrenceEntropy
import OperatorKO7.Meta.BoundaryObserver.PairInvariants
import OperatorKO7.Meta.BoundaryObserver.PairQuaternion
import OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation
import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
import OperatorKO7.Meta.BoundaryObserver.PlaceExistence
import OperatorKO7.Meta.BoundaryObserver.PlaceOrbitGeneral
import OperatorKO7.Meta.BoundaryObserver.RecursorDecidability
import OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds
import OperatorKO7.Meta.BoundaryObserver.SharedRecordPair
import OperatorKO7.Meta.BoundaryObserver.ThresholdAcceptance
import OperatorKO7.Meta.BoundaryObserver.TupleInvariants

/-!
The general modules of `Meta/BoundaryObserver`: every module of that folder whose import closure
contains none of the rewriting kernel, the quantum modules and the thermodynamic modules.
The import closure of this file, computed from import lines, is the general core named in the
formalization section of the Boundary Observation Principle manuscript.
-/
