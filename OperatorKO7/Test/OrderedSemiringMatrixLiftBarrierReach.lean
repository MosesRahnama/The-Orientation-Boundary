import OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrier

set_option autoImplicit false

namespace OrderedSemiringMatrixLiftBarrierReach

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.OrderedSemiringMatrixLift
open OperatorKO7.Meta.OrderedSemiringMatrixLiftBarrier

-- Force elaboration of every public declaration in the Phase B module.

#check @LiftBarrierCertificate
#check @LiftBarrierCertificate.Vec
#check @LiftBarrierCertificate.eval
#check @LiftBarrierCertificate.lt
#check @LiftBarrierCertificate.affineProjection
#check @LiftBarrierCertificate.projectionNatValued
#check @LiftBarrierCertificate.nonstrict
#check @LiftBarrierCertificate.heval
#check @LiftBarrierCertificate.hunbounded
#check @ordered_semiring_matrix_lift_barrier_arbitrary
#check @ordered_semiring_matrix_lift_barrier_arbitrary_global
#check @arcticLiftBarrierCertificateOf
#check @ordered_semiring_matrix_lift_barrier_arcticSemiring_unconditional
#check @tropicalLiftBarrierCertificateOf
#check @ordered_semiring_matrix_lift_barrier_tropicalSemiring_unconditional
#check @naturalLiftBarrierCertificateOf
#check @ordered_semiring_matrix_lift_barrier_naturalSemiring_unconditional
#check @arctic_tropical_distinct_in_baseSemiringList
#check @natural_in_baseSemiringList
#check @audit_theory_expansion_ordered_semiring_matrix_lift_barrier_module_anchor

-- The headline UNCONDITIONAL theorem is reachable as a value.
example {S : StepDuplicatingSchema} {d : Nat} (k : BaseSemiringKind)
    (C : LiftBarrierCertificate S d k) :
    ¬ (∀ b s n : S.T,
        C.lt (C.eval (S.wrap s (S.recur b s n)))
             (C.eval (S.recur b s (S.succ n)))) :=
  ordered_semiring_matrix_lift_barrier_arbitrary k C

-- Arctic and tropical barrier corollaries are reachable as values.
example {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticMatrixMeasure S d)
    (Cert : ArcticMatrixCertificate d)
    (hweight : Cert.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : S.T, Cert.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ b s n : S.T,
        Cert.lt (M.eval (S.wrap s (S.recur b s n)))
                (M.eval (S.recur b s (S.succ n)))) :=
  ordered_semiring_matrix_lift_barrier_arcticSemiring_unconditional
    M Cert hweight hscalarize hunbounded

example {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalMatrixMeasure S d)
    (Cert : TropicalMatrixCertificate d)
    (hweight : Cert.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : S.T, Cert.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ (∀ b s n : S.T,
        Cert.lt (M.eval (S.wrap s (S.recur b s n)))
                (M.eval (S.recur b s (S.succ n)))) :=
  ordered_semiring_matrix_lift_barrier_tropicalSemiring_unconditional
    M Cert hweight hscalarize hunbounded

-- The natural-semiring discharge is reachable.
example {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixArbitraryMeasure S d)
    {Rel : MatrixVec d → MatrixVec d → Prop}
    (D : MatrixScalarDominance M.weight Rel)
    (hunbounded : HasUnboundedScalarizedRange M) :
    ¬ (∀ b s n : S.T,
        Rel (M.eval (S.wrap s (S.recur b s n)))
            (M.eval (S.recur b s (S.succ n)))) :=
  ordered_semiring_matrix_lift_barrier_naturalSemiring_unconditional
    M D hunbounded

end OrderedSemiringMatrixLiftBarrierReach
