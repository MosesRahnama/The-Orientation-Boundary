import OperatorKO7.Meta.MutualDuplication_FiniteSchema_Instances

/-!
# Finite-Cycle Search-Certificate Mapping

This module packages the H3 finite-cycle builder surface as an M4-style
search-certificate transport. The certificate still exposes the local
successor-edge family. The point is to separate the certificate object from the
builder object, not to claim that the search itself derives the local step
family automatically.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

namespace FiniteCycleBuilderMapping

/-- First-class search certificate for a discovered finite cycle of length `k + 1`.
The local successor-edge proof is explicit certificate data. -/
structure SearchCertificate (k : Nat) where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : Fin (k + 1) → T → T → T → T
  Step : T → T → Prop
  local_step_succ :
    ∀ (i : Fin (k + 1)) b s n,
      Step (recur i b s (succ n))
        (wrap s (recur (FiniteCycleBuilder.advance i) b s n))

namespace SearchCertificate

/-- Transport a finite-cycle search certificate to the H3 builder surface. -/
def toBuilder {k : Nat} (C : SearchCertificate k) : FiniteCycleBuilder.Builder k where
  T := C.T
  base := C.base
  succ := C.succ
  wrap := C.wrap
  recur := C.recur
  Step := C.Step
  step_succ := C.local_step_succ

/-- The realized finite-cycle contextual relation carried by the certificate. -/
abbrev StepCtx {k : Nat} (C : SearchCertificate k) : C.T → C.T → Prop :=
  FiniteCycleBuilder.Builder.StepCtx C.toBuilder

/-- The realized finite-cycle contextual orientation predicate carried by the certificate. -/
def GlobalOrientsCtx {k : Nat} {α : Type} (C : SearchCertificate k) (m : C.T → α)
    (lt : α → α → Prop) : Prop :=
  FiniteCycleBuilder.Builder.GlobalOrientsCtx C.toBuilder m lt

/-- The certificate-level affine one-cycle witness at node `i`. -/
abbrev KCycleAffineAt {k : Nat} {C : SearchCertificate k}
    (i : Fin (k + 1)) (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema) :=
  FiniteCycleBuilder.Builder.KCycleAffineAt i M

/-- The certificate-level affine one-cycle witness at node `0`. -/
abbrev KCycleAffineAtZero {k : Nat} {C : SearchCertificate k}
    (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema) :=
  FiniteCycleBuilder.Builder.KCycleAffineAtZero M

/-- Every discovered node on the certified finite cycle realizes the induced cycle path. -/
theorem cycle_realized_at
    {k : Nat} (C : SearchCertificate k) (i : Fin (k + 1)) (b s n : C.T) :
    Relation.TransGen (C.StepCtx)
      (KCycleSchema.cycleSource C.toBuilder.toKCycleSystem.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget C.toBuilder.toKCycleSystem.toKCycleSchema i b s n) := by
  exact FiniteCycleBuilder.Builder.cycle_realized_at C.toBuilder i b s n

/-- Additive contextual barriers transport from the builder through the certificate. -/
theorem no_global_orients_ctx_additive
    {k : Nat} {C : SearchCertificate k}
    (M : KCycleSchema.AdditiveMeasure C.toBuilder.toKCycleSystem.toKCycleSchema) :
    ¬ C.GlobalOrientsCtx M.eval (· < ·) := by
  exact FiniteCycleBuilder.Builder.no_global_orients_ctx_additive M

/-- Arbitrary-node affine contextual barriers transport from the builder through the
certificate once the chosen-node derived one-cycle witness is unbounded. -/
theorem no_global_orients_ctx_affine_of_unbounded_at
    {k : Nat} {C : SearchCertificate k}
    (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema)
    (i : Fin (k + 1))
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (C.KCycleAffineAt i M)) :
    ¬ C.GlobalOrientsCtx M.eval (· < ·) := by
  exact FiniteCycleBuilder.Builder.no_global_orients_ctx_affine_of_unbounded_at M i hunbounded

/-- Node-`0` compatibility wrapper for the certificate-level affine contextual barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded
    {k : Nat} {C : SearchCertificate k}
    (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (C.KCycleAffineAtZero M)) :
    ¬ C.GlobalOrientsCtx M.eval (· < ·) := by
  exact FiniteCycleBuilder.Builder.no_global_orients_ctx_affine_of_unbounded M hunbounded

end SearchCertificate

end FiniteCycleBuilderMapping

namespace Constructors

/-- Two-rule constructor data as a finite-cycle search certificate. -/
def TwoRuleData.toSearchCertificate (D : TwoRuleData) : FiniteCycleBuilderMapping.SearchCertificate 1 where
  T := D.T
  base := D.base
  succ := D.succ
  wrap := D.wrap
  recur := fun i =>
    match i.1 with
    | 0 => D.recurA
    | _ => D.recurB
  Step := D.Step
  local_step_succ := by
    intro i b s n
    fin_cases i
    · simpa [FiniteCycleBuilder.advance] using D.stepA_succ b s n
    · simpa [FiniteCycleBuilder.advance] using D.stepB_succ b s n

@[simp] theorem TwoRuleData.toSearchCertificate_toBuilder_eq (D : TwoRuleData) :
    D.toSearchCertificate.toBuilder = D.toFiniteCycleBuilder :=
  rfl

/-- Three-rule constructor data as a finite-cycle search certificate. -/
def ThreeRuleData.toSearchCertificate (D : ThreeRuleData) : FiniteCycleBuilderMapping.SearchCertificate 2 where
  T := D.T
  base := D.base
  succ := D.succ
  wrap := D.wrap
  recur := fun i =>
    match i.1 with
    | 0 => D.recur0
    | 1 => D.recur1
    | _ => D.recur2
  Step := D.Step
  local_step_succ := by
    intro i b s n
    fin_cases i
    · simpa [FiniteCycleBuilder.advance] using D.step0_succ b s n
    · simpa [FiniteCycleBuilder.advance] using D.step1_succ b s n
    · simpa [FiniteCycleBuilder.advance] using D.step2_succ b s n

@[simp] theorem ThreeRuleData.toSearchCertificate_toBuilder_eq (D : ThreeRuleData) :
    D.toSearchCertificate.toBuilder = D.toFiniteCycleBuilder :=
  rfl

end Constructors

namespace KCycleSystem

/-- Concrete search-certificate wrapper for the two-rule witness data. -/
def twoRuleWitnessSearchCertificate : FiniteCycleBuilderMapping.SearchCertificate 1 :=
  twoRuleWitnessData.toSearchCertificate

/-- Concrete search-certificate wrapper for the three-rule witness data. -/
def threeRuleWitnessSearchCertificate : FiniteCycleBuilderMapping.SearchCertificate 2 :=
  threeRuleWitnessData.toSearchCertificate

@[simp] theorem twoRuleWitnessSearchCertificate_toBuilder_eq :
    twoRuleWitnessSearchCertificate.toBuilder = twoRuleWitnessData.toFiniteCycleBuilder :=
  rfl

@[simp] theorem threeRuleWitnessSearchCertificate_toBuilder_eq :
    threeRuleWitnessSearchCertificate.toBuilder = threeRuleWitnessData.toFiniteCycleBuilder :=
  rfl

end KCycleSystem

end OperatorKO7.MutualDuplicationFiniteSchema
