import OperatorKO7.Meta.BarrierWitness_Extended
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
# Checked fixed-system non-orientation certificates

This module unifies the existing barrier extractors into one proof object. A
certificate records the exact root duplicating rule, its concrete substitution,
the evaluated codomain and order, and the declared direct family for which the
counterexample was extracted.

Trust: kernel-checked imported extractors only; no external tool output is used
as a proof certificate.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- Exact root relation containing only the schema's duplicating successor
rule. -/
inductive DupStep (S : StepDuplicatingSchema) : S.T → S.T → Prop where
  | recurSucc (b s n : S.T) :
      DupStep S (S.recur b s (S.succ n))
        (S.wrap s (S.recur b s n))

/-- The theorem-backed direct families admitted by this certificate surface. -/
inductive DeclaredDirectFamily where
  | additive
  | transparentCompositional
  | affineWithPump
  | restrictedQuadraticWithPump
  | maxPlusWithPump
  | matrixFunctionalWithProjectedAffinePump
  deriving DecidableEq, Repr

/-- Orientation of the exact root duplicating relation by an evaluator and
codomain order. -/
def OrientsDupStepRelation {S : StepDuplicatingSchema} {Codomain : Type}
    (eval : S.T → Codomain) (order : Codomain → Codomain → Prop) : Prop :=
  ∀ {a b : S.T}, DupStep S a b → order (eval b) (eval a)

/-- A checked counterexample to orientation for one declared direct family.

`b`, `s`, and `n` are the exact substitution for `sourceRule`; the final field
proves that the selected codomain order does not decrease on its target. -/
structure CheckedNonOrientationCertificate (S : StepDuplicatingSchema) where
  Codomain : Type
  order : Codomain → Codomain → Prop
  eval : S.T → Codomain
  family : DeclaredDirectFamily
  b : S.T
  s : S.T
  n : S.T
  sourceRule : DupStep S (S.recur b s (S.succ n))
    (S.wrap s (S.recur b s n))
  violatesDecrease :
    ¬ order (eval (S.wrap s (S.recur b s n)))
      (eval (S.recur b s (S.succ n)))

/-- Generic soundness for the exact relation and exact order stored in the
certificate. -/
theorem CheckedNonOrientationCertificate.not_global_orients
    {S : StepDuplicatingSchema}
    (cert : CheckedNonOrientationCertificate S) :
    ¬ OrientsDupStepRelation cert.eval cert.order := by
  intro h
  exact cert.violatesDecrease (h cert.sourceRule)

/-- A certificate over a system's schema also refutes global orientation of
that exact system, because its `dup_step` field realizes the recorded rule. -/
theorem CheckedNonOrientationCertificate.not_system_global_orients
    {Sys : StepDuplicatingSystem}
    (cert : CheckedNonOrientationCertificate Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys cert.eval cert.order := by
  intro h
  exact cert.violatesDecrease (h (Sys.dup_step cert.b cert.s cert.n))

/-- System-indexed wrapper used when a paper-facing certificate must name the
fixed rewrite system, not only its constructor schema. -/
structure CheckedSystemNonOrientationCertificate
    (Sys : StepDuplicatingSystem) where
  certificate :
    CheckedNonOrientationCertificate Sys.toStepDuplicatingSchema

/-- Soundness of the system-indexed certificate wrapper. -/
theorem CheckedSystemNonOrientationCertificate.not_global_orients
    {Sys : StepDuplicatingSystem}
    (cert : CheckedSystemNonOrientationCertificate Sys) :
    ¬ GlobalOrients Sys cert.certificate.eval cert.certificate.order :=
  cert.certificate.not_system_global_orients

/-- Attach a schema certificate to an exact fixed system with that schema. -/
def CheckedNonOrientationCertificate.forSystem
    {Sys : StepDuplicatingSystem}
    (cert : CheckedNonOrientationCertificate Sys.toStepDuplicatingSchema) :
    CheckedSystemNonOrientationCertificate Sys :=
  ⟨cert⟩

/-! ## Adapters from the existing extractor surface -/

/-- Lift a scalar `BarrierCertificate` into the checked common object. -/
def CheckedNonOrientationCertificate.ofBarrierCertificate
    {S : StepDuplicatingSchema} {eval : S.T → Nat}
    (family : DeclaredDirectFamily)
    (cert : BarrierCertificate S eval) :
    CheckedNonOrientationCertificate S where
  Codomain := Nat
  order := fun x y => x < y
  eval := eval
  family := family
  b := cert.b
  s := cert.s
  n := cert.n
  sourceRule := DupStep.recurSucc cert.b cert.s cert.n
  violatesDecrease := cert.fails

/-- Lift an arbitrary-codomain `RelationBarrierCertificate` into the checked
common object. -/
def CheckedNonOrientationCertificate.ofRelationBarrierCertificate
    {S : StepDuplicatingSchema} {Codomain : Type}
    {eval : S.T → Codomain} {order : Codomain → Codomain → Prop}
    (family : DeclaredDirectFamily)
    (cert : RelationBarrierCertificate S Codomain eval order) :
    CheckedNonOrientationCertificate S where
  Codomain := Codomain
  order := order
  eval := eval
  family := family
  b := cert.b
  s := cert.s
  n := cert.n
  sourceRule := DupStep.recurSucc cert.b cert.s cert.n
  violatesDecrease := cert.fails

/-- Checked additive-family extractor. -/
def additive_checkedCertificate {S : StepDuplicatingSchema}
    (M : AdditiveMeasure S) : CheckedNonOrientationCertificate S :=
  CheckedNonOrientationCertificate.ofBarrierCertificate .additive
    (additive_witness M)

/-- Checked transparent-compositional-family extractor. -/
def transparentCompositional_checkedCertificate
    {S : StepDuplicatingSchema}
    (M : CompositionalMeasure S)
    (htransparent : M.c_succ M.c_base = M.c_base) :
    CheckedNonOrientationCertificate S :=
  CheckedNonOrientationCertificate.ofBarrierCertificate
    .transparentCompositional (compositional_witness M htransparent)

/-- Checked internally pumped affine-family extractor. -/
def affineWithPump_checkedCertificate {S : StepDuplicatingSchema}
    (M : AffineMeasureWithPump S) : CheckedNonOrientationCertificate S :=
  CheckedNonOrientationCertificate.ofBarrierCertificate .affineWithPump
    (affine_with_pump_witness M)

/-- Checked internally pumped restricted-quadratic-family extractor. -/
def restrictedQuadraticWithPump_checkedCertificate
    {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasureWithPump S) :
    CheckedNonOrientationCertificate S :=
  CheckedNonOrientationCertificate.ofBarrierCertificate
    .restrictedQuadraticWithPump (quadratic_with_pump_witness M)

/-- Checked internally pumped max-plus-family extractor. -/
def maxPlusWithPump_checkedCertificate {S : StepDuplicatingSchema}
    (M : MaxMeasureWithPump S) : CheckedNonOrientationCertificate S :=
  CheckedNonOrientationCertificate.ofBarrierCertificate .maxPlusWithPump
    (max_with_pump_witness M)

/-- Checked matrix-functional extractor, retaining its vector codomain and
strict componentwise relation exactly. -/
def matrixFunctionalWithProjectedAffinePump_checkedCertificate
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasureWithProjectedAffinePump S d) :
    CheckedNonOrientationCertificate S :=
  CheckedNonOrientationCertificate.ofRelationBarrierCertificate
    .matrixFunctionalWithProjectedAffinePump
    (matrixFunctional_with_projected_affine_pump_witness M)

/-! ## Fixed KO7 system adapters -/

/-- Paper-facing additive certificate indexed by the exact KO7 system. -/
def ko7Additive_checkedSystemCertificate
    (M : AdditiveMeasure
      OperatorKO7.CompositionalImpossibility.ko7Schema) :
    CheckedSystemNonOrientationCertificate
      OperatorKO7.CompositionalImpossibility.ko7System :=
  CheckedNonOrientationCertificate.forSystem
    (Sys := OperatorKO7.CompositionalImpossibility.ko7System)
    (additive_checkedCertificate M)

/-- Closed non-vacuity witness for A-02: the concrete KO7 `simpleSize`
measure produces a checked certificate indexed by the fixed KO7 system. -/
def ko7SimpleSize_checkedSystemCertificate :
    CheckedSystemNonOrientationCertificate
      OperatorKO7.CompositionalImpossibility.ko7System :=
  ko7Additive_checkedSystemCertificate
    OperatorKO7.CompositionalImpossibility.simpleSize_ACM.toSchemaMeasure

/-- The closed `simpleSize` certificate refutes global orientation of the
exact KO7 rewrite system by the evaluator and order stored in that
certificate. -/
theorem ko7SimpleSize_checkedSystemCertificate_not_global_orients :
    ¬ GlobalOrients OperatorKO7.CompositionalImpossibility.ko7System
      ko7SimpleSize_checkedSystemCertificate.certificate.eval
      ko7SimpleSize_checkedSystemCertificate.certificate.order :=
  ko7SimpleSize_checkedSystemCertificate.not_global_orients

/-- Paper-facing transparent-compositional certificate indexed by the exact
KO7 system. -/
def ko7TransparentCompositional_checkedSystemCertificate
    (M : CompositionalMeasure
      OperatorKO7.CompositionalImpossibility.ko7Schema)
    (htransparent : M.c_succ M.c_base = M.c_base) :
    CheckedSystemNonOrientationCertificate
      OperatorKO7.CompositionalImpossibility.ko7System :=
  CheckedNonOrientationCertificate.forSystem
    (Sys := OperatorKO7.CompositionalImpossibility.ko7System)
    (transparentCompositional_checkedCertificate M htransparent)

/-- Paper-facing pumped-affine certificate indexed by the exact KO7 system. -/
def ko7AffineWithPump_checkedSystemCertificate
    (M : AffineMeasureWithPump
      OperatorKO7.CompositionalImpossibility.ko7Schema) :
    CheckedSystemNonOrientationCertificate
      OperatorKO7.CompositionalImpossibility.ko7System :=
  CheckedNonOrientationCertificate.forSystem
    (Sys := OperatorKO7.CompositionalImpossibility.ko7System)
    (affineWithPump_checkedCertificate M)

/-- Paper-facing pumped restricted-quadratic certificate indexed by the exact
KO7 system. -/
def ko7RestrictedQuadraticWithPump_checkedSystemCertificate
    (M : QuadraticCounterMeasureWithPump
      OperatorKO7.CompositionalImpossibility.ko7Schema) :
    CheckedSystemNonOrientationCertificate
      OperatorKO7.CompositionalImpossibility.ko7System :=
  CheckedNonOrientationCertificate.forSystem
    (Sys := OperatorKO7.CompositionalImpossibility.ko7System)
    (restrictedQuadraticWithPump_checkedCertificate M)

/-- Paper-facing pumped max-plus certificate indexed by the exact KO7 system. -/
def ko7MaxPlusWithPump_checkedSystemCertificate
    (M : MaxMeasureWithPump
      OperatorKO7.CompositionalImpossibility.ko7Schema) :
    CheckedSystemNonOrientationCertificate
      OperatorKO7.CompositionalImpossibility.ko7System :=
  CheckedNonOrientationCertificate.forSystem
    (Sys := OperatorKO7.CompositionalImpossibility.ko7System)
    (maxPlusWithPump_checkedCertificate M)

/-- Paper-facing projected matrix-functional certificate indexed by the exact
KO7 system and retaining its vector codomain relation. -/
def ko7MatrixFunctionalWithProjectedAffinePump_checkedSystemCertificate
    {d : Nat}
    (M : MatrixFunctionalMeasureWithProjectedAffinePump
      OperatorKO7.CompositionalImpossibility.ko7Schema d) :
    CheckedSystemNonOrientationCertificate
      OperatorKO7.CompositionalImpossibility.ko7System :=
  CheckedNonOrientationCertificate.forSystem
    (Sys := OperatorKO7.CompositionalImpossibility.ko7System)
    (matrixFunctionalWithProjectedAffinePump_checkedCertificate M)

end OperatorKO7.Meta.BoundaryGeneral
