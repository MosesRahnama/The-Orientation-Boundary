import OperatorKO7.Meta.Methods.SemanticStructuralRows
import OperatorKO7.Meta.Methods.AlgebraicInterpretationRows
import OperatorKO7.Meta.SafeStep_Complexity

/-!
# Native semantic and structural semantics for ORI-3

The match-bound part is rebuilt around a raised transition certificate. The
linear complexity statement is derived from the transition decrease and size
bound, rather than stored as a field. The file also supplies concrete controls
for finite models, extended algebras, and labelled rewriting.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SemanticStructuralNativeSemantics

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.Methods.SemanticStructuralRows

/-! ## Extended monotone algebra -/

/-- Concrete weak/strict algebra based on constructor size. -/
def unitExtendedMonotoneAlgebra : ExtendedMonotoneAlgebra freeSchema where
  eval := OperatorKO7.Methods.AlgebraicInterpretationRows.unitAffineNatEval
  weak := (fun a b => a <= b)
  strict := (fun a b => a < b)
  weak_refl := fun _ => le_rfl
  strict_to_lt := fun h => h
  wrapCost := 0
  wrap_keeps_arguments := by
    intro x y
    simp [freeSchema,
      OperatorKO7.Methods.AlgebraicInterpretationRows.unitAffineNatEval]
  succGain := 1
  counter_gain := by
    intro b s n
    simp [freeSchema,
      OperatorKO7.Methods.AlgebraicInterpretationRows.unitAffineNatEval]
    omega

/-- The concrete extended algebra has a strict comparison. -/
theorem unitExtendedMonotoneAlgebra_nonconstant :
    unitExtendedMonotoneAlgebra.strict
      (unitExtendedMonotoneAlgebra.eval .base)
      (unitExtendedMonotoneAlgebra.eval (.succ .base)) := by
  simp [unitExtendedMonotoneAlgebra, freeSchema,
    OperatorKO7.Methods.AlgebraicInterpretationRows.unitAffineNatEval]

/-! ## Finite-model control -/

/-- A finite interpretation with only a weak wrapper law. This is the control
showing that finiteness itself is consistent; strict wrapper growth is the
incompatible method requirement. -/
structure WeakFiniteModelInterpretation
    (S : StepDuplicatingSchema) (α : Type) [Fintype α] where
  eval : S.T -> α
  rank : α -> Nat
  wrap_weak : forall x y, rank (eval y) <= rank (eval (S.wrap x y))

/-- Constant one-point finite model after the strict law is removed. -/
def onePointWeakFiniteModel : WeakFiniteModelInterpretation freeSchema (Fin 1) where
  eval := fun _ => 0
  rank := fun _ => 0
  wrap_weak := by intro x y; exact le_rfl

/-- The strict wrapper law is the incompatible part of the finite method. -/
theorem finiteModel_strictness_is_method_boundary :
    Nonempty (WeakFiniteModelInterpretation freeSchema (Fin 1)) ∧
      ¬ Nonempty (FiniteModelInterpretation freeSchema (Fin 1)) := by
  constructor
  · exact ⟨onePointWeakFiniteModel⟩
  · exact finiteModelTermination_row_anchor freeSchema (Fin 1)

/-! ## Raised match-bound semantics -/

/-- Exact-length closure for an arbitrary relation. -/
inductive RelPow {α : Type} (R : α -> α -> Prop) : α -> Nat -> α -> Prop
  | refl (a : α) : RelPow R a 0 a
  | tail {a b c : α} {n : Nat} : R a b -> RelPow R b n c -> RelPow R a (n + 1) c

/-- A proof-carrying raised system. The `height` field is the state assigned by
the raised method. Every source transition consumes one unit, and the initial
height is bounded by a constant times source size. The linear consequence is
proved below. -/
structure RaisedMatchBoundCertificate
    (α : Type) (R : α -> α -> Prop) (size : α -> Nat) where
  bound : Nat
  height : α -> Nat
  transition_decreases : forall {a b}, R a b -> height b + 1 <= height a
  initial_height_bound : forall a, height a <= bound * size a

/-- Counted derivations consume at most the source height. -/
theorem RelPow.length_le_height
    {α : Type} {R : α -> α -> Prop} {size : α -> Nat}
    (C : RaisedMatchBoundCertificate α R size) :
    forall {a b n}, RelPow R a n b -> n <= C.height a
  | _, _, _, RelPow.refl _ => Nat.zero_le _
  | _, _, _, RelPow.tail hab hbc => by
      have htail := RelPow.length_le_height C hbc
      have hstep := C.transition_decreases hab
      omega

/-- Linear complexity follows from the raised transition semantics. -/
theorem RaisedMatchBoundCertificate.linear_bound
    {α : Type} {R : α -> α -> Prop} {size : α -> Nat}
    (C : RaisedMatchBoundCertificate α R size)
    {a b : α} {n : Nat} (h : RelPow R a n b) :
    n <= C.bound * size a :=
  le_trans (RelPow.length_le_height C h) (C.initial_height_bound a)

/-- A nonempty control system for the method: natural countdown. -/
inductive CountdownStep : Nat -> Nat -> Prop
  | step (n : Nat) : CountdownStep (n + 1) n

/-- Countdown has a one-state-per-unit raised certificate. -/
def countdownRaisedCertificate :
    RaisedMatchBoundCertificate Nat CountdownStep (fun n => n + 1) where
  bound := 1
  height := fun n => n
  transition_decreases := by
    intro a b h
    cases h
    omega
  initial_height_bound := by
    intro n
    omega

/-- The positive control has an actual nonempty derivation. -/
theorem countdownRaisedCertificate_nonempty_step : CountdownStep 2 1 := by
  simpa using CountdownStep.step 1

/-- Convert the existing counted contextual relation to the generic counted
relation used by the raised certificate. -/
theorem stepCtxFullPow_to_relPow {a b : Trace} {n : Nat}
    (h : MetaSN_KO7.StepCtxFullPow a n b) :
    RelPow MetaSN_KO7.StepCtxFull a n b := by
  induction h with
  | refl t => exact RelPow.refl t
  | tail hab hbc ih => exact RelPow.tail hab ih

/-- KO7 specialization of the method data. -/
abbrev KO7RaisedMatchBoundCertificate :=
  RaisedMatchBoundCertificate Trace MetaSN_KO7.StepCtxFull MetaSN_KO7.termSize

/-- A raised certificate derives the same linear statement used by the paper
row. The conclusion is not a field of the certificate. -/
theorem ko7RaisedMatchBoundCertificate_certifiesLinear
    (C : KO7RaisedMatchBoundCertificate) :
    CertifiesLinearComplexity C.bound := by
  intro t u n hpow
  exact C.linear_bound (stepCtxFullPow_to_relPow hpow)

/-- The exponential lower family excludes every raised match-bound certificate
on the KO7 full-context relation. -/
theorem no_ko7RaisedMatchBoundCertificate :
    Not (Nonempty KO7RaisedMatchBoundCertificate) := by
  rintro ⟨C⟩
  exact no_linear_complexity_certificate C.bound
    (ko7RaisedMatchBoundCertificate_certifiesLinear C)

/-- Raise-consistency is now a consequence of the actual transition law. -/
theorem raisedMatchBound_root_raise_consistent
    (C : KO7RaisedMatchBoundCertificate) {a b : Trace} (h : Step a b) :
    C.height b <= C.height a + 1 := by
  have hctx : MetaSN_KO7.StepCtxFull a b := MetaSN_KO7.StepCtxFull.root h
  have hd := C.transition_decreases hctx
  omega

/-- Native match-bound row statement with a positive method control. -/
abbrev NativeMatchBoundsRowClaim : Prop :=
  Nonempty (RaisedMatchBoundCertificate Nat CountdownStep (fun n => n + 1)) ∧
    Not (Nonempty KO7RaisedMatchBoundCertificate) ∧
    (forall C : KO7RaisedMatchBoundCertificate, CertifiesLinearComplexity C.bound) ∧
    MatchBoundsRowClaim

/-- Native raised-system classification. -/
theorem nativeMatchBounds_row_anchor : NativeMatchBoundsRowClaim :=
  ⟨⟨countdownRaisedCertificate⟩,
    no_ko7RaisedMatchBoundCertificate,
    ko7RaisedMatchBoundCertificate_certifiesLinear,
    matchBounds_row_anchor⟩

/-! ## Labelled rewriting and simulation -/

/-- The labelled instance of the duplicating schema rule. -/
inductive LabelledDupStep {L : Type} (labelling : Labelling L) :
    LabelledSTerm L -> LabelledSTerm L -> Prop
  | dup : LabelledDupStep labelling
      (labelTerm labelling dupSrc) (labelTerm labelling dupTgt)

/-- Erasure sends each labelled rule instance to the unlabelled schema rule. -/
theorem labelledDupStep_erases
    {L : Type} {labelling : Labelling L} {a b : LabelledSTerm L}
    (h : LabelledDupStep labelling a b) :
    eraseLabels a = dupSrc ∧ eraseLabels b = dupTgt := by
  cases h
  exact ⟨eraseLabels_labelTerm _ _, eraseLabels_labelTerm _ _⟩

/-- The constructor-sensitive method orients its labelled rule by the native
root-label order. -/
theorem constructorRootLabelling_orients_step
    {a b : LabelledSTerm Bool}
    (h : LabelledDupStep constructorRootLabelling a b) :
    RootLabelGt boolLabelValue a b := by
  cases h
  exact constructorRootLabelling_orients_duplication

/-- Hence the reverse labelled duplicator relation is well founded. -/
theorem constructorRootLabelling_step_wellFounded :
    WellFounded (fun a b : LabelledSTerm Bool =>
      LabelledDupStep constructorRootLabelling b a) := by
  apply Subrelation.wf
    (r := fun a b : LabelledSTerm Bool => RootLabelGt boolLabelValue b a)
  · intro a b h
    exact constructorRootLabelling_orients_step h
  · exact rootLabelGt_wellFounded boolLabelValue

/-- Predictive and self-labelled policies are actual labelling objects. -/
structure LabelMethodControls where
  semantic : Labelling Bool
  semanticExact : semantic = constructorRootLabelling
  predictive : Labelling Bool
  predictiveExact : predictive = predictiveLabelling (fun t => decide (t = dupSrc))
  self : Labelling (List STerm)
  selfExact : self = selfLabelling
  semanticOrients : RootLabelGt boolLabelValue
    (labelTerm semantic dupSrc) (labelTerm semantic dupTgt)
  semanticContextFailure : Not (SuccContextCompatible (RootLabelGt boolLabelValue))
  selfDistinguishes :
    [STerm.var SchemaVar.b, STerm.var SchemaVar.s,
      STerm.succ (STerm.var SchemaVar.n)] ≠
    [STerm.var SchemaVar.s,
      STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s)
        (STerm.var SchemaVar.n)]

/-- Concrete controls for label-sensitive behavior. -/
def labelMethodControls : LabelMethodControls where
  semantic := constructorRootLabelling
  semanticExact := rfl
  predictive := predictiveLabelling (fun t => decide (t = dupSrc))
  predictiveExact := rfl
  self := selfLabelling
  selfExact := rfl
  semanticOrients := constructorRootLabelling_orients_duplication
  semanticContextFailure := rootLabelGt_not_succContextCompatible
  selfDistinguishes := selfLabelling_dup_root_labels_ne

/-! ## Categorical, forward-closure and quasi-decreasing carriers -/

/-- The categorical row is represented by the relational category that the
source file constructs. Its scope remains relational-category separation. -/
def categoricalMethod : RelationalCategoryCarrier := ko7RelationalCategory

/-- Forward-closure applicability is represented by its actual failed
right-linearity requirement. -/
def forwardClosureMethodBoundary : NotApplicableRecord := forwardClosuresRecord

/-- The unconditional quasi-decreasing core is an actual inhabited property. -/
theorem quasiDecreasingMethod :
    AbstractQuasiDecreasing Step NoConditionalPremise :=
  quasiDecreasingness_row_anchor.2

/-- Package of the ORI-3 method data. -/
structure SemanticStructuralNativeBundle where
  extended : ExtendedMonotoneAlgebra freeSchema
  weakFinite : WeakFiniteModelInterpretation freeSchema (Fin 1)
  countdownMatchBound :
    RaisedMatchBoundCertificate Nat CountdownStep (fun n => n + 1)
  labels : LabelMethodControls
  category : RelationalCategoryCarrier
  forwardBoundary : NotApplicableRecord
  quasiDecreasing : AbstractQuasiDecreasing Step NoConditionalPremise

/-- Concrete ORI-3 bundle. -/
def semanticStructuralNativeBundle : SemanticStructuralNativeBundle where
  extended := unitExtendedMonotoneAlgebra
  weakFinite := onePointWeakFiniteModel
  countdownMatchBound := countdownRaisedCertificate
  labels := labelMethodControls
  category := categoricalMethod
  forwardBoundary := forwardClosureMethodBoundary
  quasiDecreasing := quasiDecreasingMethod

end OperatorKO7.Methods.OrientationClosure.SemanticStructuralNativeSemantics
