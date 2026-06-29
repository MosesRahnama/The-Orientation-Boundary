import OperatorKO7.Meta.DistinctionBoundary.SemanticsPreservingMaximality
import OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence
import OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.EqualityModeCertificate

open OperatorKO7 Trace
open MetaSN_KO7

/-- Certified classification payload for an equality mode. -/
structure ModeCertificate (m : EqualityMode) : Prop where
  forkLabel : EqualityMode.CanDiagonalFork m
  reflectedByEnum :
    EqualityMode.CanDiagonalFork m <-> m = EqualityMode.unguardedTotalizedRewrite

/-- The raw mode is the only equality mode in the enum that carries the diagonal fork label. -/
theorem raw_mode_certificate :
    ModeCertificate EqualityMode.unguardedTotalizedRewrite :=
  { forkLabel := trivial
    reflectedByEnum := equalityMode_canDiagonalFork_iff EqualityMode.unguardedTotalizedRewrite }

/-- Guarded typed comparison is backed by global SafeStep confluence, not only by an enum label. -/
theorem typed_mode_confluence_certificate :
    Not (EqualityMode.CanDiagonalFork EqualityMode.typed)
      ∧ MetaSN_KO7.ConfluentSafe :=
  ⟨id, OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_globally_confluent⟩

/-- Inert comparison is certified by absence of any fork label. -/
theorem inert_mode_no_fork_certificate :
    Not (EqualityMode.CanDiagonalFork EqualityMode.relational) :=
  id

/-- Collapse mode is certified as the raw diagonal-fork case. -/
theorem collapse_mode_is_raw_fork_certificate :
    EqualityMode.CanDiagonalFork EqualityMode.unguardedTotalizedRewrite
      ∧ ¬ ∃ d, StepStar void d ∧ StepStar (integrate (merge void void)) d :=
  ⟨trivial,
    OperatorKO7.Meta.DistinctionBoundary.void_integrate_merge_self_not_joinable void⟩

#print axioms raw_mode_certificate
#print axioms typed_mode_confluence_certificate
#print axioms collapse_mode_is_raw_fork_certificate

end OperatorKO7.Meta.DistinctionBoundary.EqualityModeCertificate
