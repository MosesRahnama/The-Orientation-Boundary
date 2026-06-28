import OperatorKO7.SchemaExtendedAPI
import OperatorKO7.Meta.FreeStepDuplicatingTraceBridge
import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_Family
import OperatorKO7.Meta.BenchmarkedPrimitiveRecursionFamily
import OperatorKO7.Meta.OperationalIncompleteness
import OperatorKO7.Meta.ProofTheoreticRegister
import OperatorKO7.Meta.ReverseMathSupport
import OperatorKO7.Meta.ReverseMathFramework
import OperatorKO7.Meta.ReverseMath.Substitution
import OperatorKO7.Meta.ReverseMath.ArtsGieslPi02
import OperatorKO7.Meta.ReverseMath.DeductionFO
import OperatorKO7.Meta.ReverseMath.DeductionH
import OperatorKO7.Meta.ReverseMathOmega3WellOrdering
import OperatorKO7.Meta.ReverseMath.ArtsGieslFaithful
import OperatorKO7.Meta.ReverseMath.ArtsGieslKO7Bridge
import OperatorKO7.Meta.ReverseMath.ArtsGieslUpperSemantic
import OperatorKO7.Meta.ReverseMath.ArtsGieslProduct
import OperatorKO7.Meta.ReverseMath.ArtsGieslUpperSyntactic
import OperatorKO7.Meta.ReverseMath.ArtsGieslProductFull
import OperatorKO7.Meta.BoundaryGeneral.ProvenanceLicense
import OperatorKO7.Meta.BoundaryGeneral.C4Classifier
import OperatorKO7.Meta.BoundaryGeneral.WholeTermIndistinguishability
import OperatorKO7.Meta.BoundaryGeneral.WitnessFirst
import OperatorKO7.Meta.BoundaryGeneral.EndogenousProvenance
import OperatorKO7.Meta.TerminationPrincipleRegister
import OperatorKO7.Meta.ArtsGiesl_UpperBound
import OperatorKO7.Meta.ArtsGiesl_LowerBound
import OperatorKO7.Meta.ArtsGiesl_ReverseMathCalibration
import OperatorKO7.Meta.ReflectionSchema
import OperatorKO7.Meta.ClassicalAscentProfile
import OperatorKO7.Meta.StructuralIdentityComparison
import OperatorKO7.Meta.ProjectionAsConservativeExtension
import OperatorKO7.Meta.SafeStep

/-!
# Cross-the orientation-boundary manuscriptPI

Project-facing public root above `SchemaExtendedAPI`.

This file adds the KO7-facing primitive-fragment bridge inside `Trace`, the
confession-method convergence and family packaging, and the broader
primitive-recursion / operational-incompleteness interfaces used across the
paper stack. It also re-exports the conditional LCEL
route-classification lift in `Meta/LCELRouteSemanticsClassification.lean`
and the named P4C residual-obligation package/reduction in
`Meta/LCELP4CResidualObligation.lean`, together with the theorem-facing
LCEL/P4C closeout surface: universal certification, universal certified
route-lift blueprint, the exact certified boundary closeout, the
unconditional raw bare P4C theorem, and the final status catalog. The
usable-rules concrete / universal / bridge-attempt / final-status closeout
surface is also exported here
because they are paper-facing governance/package artifacts rather than
schema-only primitives.

- `LCELP4CExactCertifiedBoundary` is the explicit conjunction form of the
	closed universal certification and universal certified route-lift blueprint
	theorems, `LCELP4CCertifiedBoundaryCatalog` remains the paper-facing
	packaged surface, and `LCELP4CRawTarget.unconditional` together with
	`lcel_p4c_unconditional_rawTarget` records the unconditional raw bare P4C
	closeout.

Use this root when you explicitly want the cross-manuscript KO7-facing layer. Use
`PrimitiveSchemaAPI` or `SchemaExtendedAPI` when you want a stricter boundary.
-/
