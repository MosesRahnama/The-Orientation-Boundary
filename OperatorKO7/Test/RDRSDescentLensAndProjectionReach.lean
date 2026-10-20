import OperatorKO7.Meta.RDRSDescentLens
import OperatorKO7.Meta.RDRSProjectionSyntax

/-!
# Reachability check: RDRS Descent Lens and Projection Syntax

The file checks that every declaration is resolvable and that the abstract
interface is inhabited (`trivialStep` on `Unit`).
-/

set_option autoImplicit false

namespace RDRSDescentLensAndProjectionReach

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSProjectionSyntax

#check RDRSStep
#check Orients
#check DescentLens
#check HasPumpViolation
#check no_orients_of_lens_violation
#check rdrs_descent_lens_local_contradiction_anchor

#check PayloadForgetErasure
#check ProjectionEscape
#check ProjectionEscape.liftedMeasure
#check ProjectionEscape.lifted_orients
#check ProjectionEscape.requires_positive_evidence
#check rdrs_projection_escape_positive_evidence_anchor

/--
Proves: the abstract `RDRSStep Unit Unit Unit Unit` interface is
  inhabited by a trivial step whose `lhs` and `rhs` are both the
  constant `()`.
Does not prove: anything about concrete RDRS instances; this is a
  reach probe only.
Relation: abstract `RDRSStep Unit Unit Unit Unit`; not a concrete
  rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only (pure constructor application).
Scope: used by the reach-probe theorems below.
-/
def trivialStep : RDRSStep Unit Unit Unit Unit where
  lhs _ _ _ := ()
  rhs _ _ _ := ()

/--
Proves: the local contradiction theorem typechecks against the
  trivial `Unit` step and an arbitrary `μ`/`ltA`/`L`/`hBad`.
Does not prove: anything about a concrete RDRS instance; this is a
  reach probe only.
Relation: abstract `RDRSStep Unit Unit Unit Unit`; not a concrete
  rewriting relation.
Closure: one-step on the abstract step pair.
Strategy: not applicable.
Trust: kernel-only (delegates to `no_orients_of_lens_violation`).
Scope: parametric over `μ`, `ltA`, `L`, `hBad`.
-/
theorem reach_no_orients_of_lens_violation_typechecks
    (μ : Unit → Unit) (ltA : Unit → Unit → Prop)
    (L : DescentLens trivialStep μ ltA)
    (hBad : HasPumpViolation L) :
    ¬ Orients trivialStep μ ltA :=
  no_orients_of_lens_violation L hBad

/--
Proves: the audit anchor String for the local-contradiction theorem
  is exactly the expected fully-qualified Lean name.
Does not prove: anything about the local-contradiction theorem
  itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only `rfl`.
Scope: the audit anchor constant in `RDRSDescentLens`.
-/
theorem reach_local_contradiction_anchor_value :
    rdrs_descent_lens_local_contradiction_anchor =
      "OperatorKO7.RDRSDescentLens.no_orients_of_lens_violation" := rfl

/--
Proves: the audit anchor String for the projection-escape
  positive-evidence discipline is exactly the expected fully-qualified
  Lean name.
Does not prove: anything about `ProjectionEscape.requires_positive_evidence`
  itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only `rfl`.
Scope: the audit anchor constant in `RDRSProjectionSyntax`.
-/
theorem reach_projection_escape_anchor_value :
    rdrs_projection_escape_positive_evidence_anchor =
      "OperatorKO7.RDRSProjectionSyntax.ProjectionEscape.requires_positive_evidence" := rfl

end RDRSDescentLensAndProjectionReach
