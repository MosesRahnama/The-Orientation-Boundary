import OperatorKO7.Meta.Methods.AdmittanceInapplicabilityRows
import OperatorKO7.Meta.Methods.DependencyPairTypedRows
import OperatorKO7.Meta.HigherOrderRewriting_Syntax

/-!
# Native higher-order admission and typing semantics for ORI-5

This file gives the higher-order and type-system rows concrete syntax and
proof rules over `HigherOrderRewritingSyntax.HOTerm`. The HORPO and CPO rows
remain specialized admission fragments: they use the accessible-subterm and
computability-closure rules needed by the displayed recursor call. The file
also records the repository substitution behavior, guarded recursion, sized
indices, resource typing, ramified typing, and finite versus infinite
reduction controls.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.HigherOrderNativeSemantics

open OperatorKO7
open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.Methods.AdmittanceInapplicabilityRows
open OperatorKO7.Methods.DependencyPairTypedRows

/-! ## Higher-order syntax and proper subterms -/

/-- Structural size on the repository higher-order syntax. -/
def hoSize : HOTerm -> Nat
  | .var _ => 1
  | .atom => 1
  | .succ t => 1 + hoSize t
  | .app f a => 1 + hoSize f + hoSize a
  | .lam _ body => 1 + hoSize body
  | .recur b s n => 1 + hoSize b + hoSize s + hoSize n
  | .share x y => 1 + hoSize x + hoSize y

/-- Proper subterm relation including binder, application, recursor and sharing
positions. -/
inductive HOStrictSubterm : HOTerm -> HOTerm -> Prop
  | succ (t : HOTerm) : HOStrictSubterm t (.succ t)
  | appLeft (f a : HOTerm) : HOStrictSubterm f (.app f a)
  | appRight (f a : HOTerm) : HOStrictSubterm a (.app f a)
  | lam (name : Nat) (body : HOTerm) : HOStrictSubterm body (.lam name body)
  | recurBase (b s n : HOTerm) : HOStrictSubterm b (.recur b s n)
  | recurStep (b s n : HOTerm) : HOStrictSubterm s (.recur b s n)
  | recurCounter (b s n : HOTerm) : HOStrictSubterm n (.recur b s n)
  | shareLeft (x y : HOTerm) : HOStrictSubterm x (.share x y)
  | shareRight (x y : HOTerm) : HOStrictSubterm y (.share x y)
  | trans {x y z : HOTerm} : HOStrictSubterm x y -> HOStrictSubterm y z -> HOStrictSubterm x z

/-- Proper higher-order subterms have smaller structural size. -/
theorem hoStrictSubterm_size_lt {x y : HOTerm} (h : HOStrictSubterm x y) :
    hoSize x < hoSize y := by
  induction h with
  | succ t => simp [hoSize]
  | appLeft f a => simp [hoSize]; omega
  | appRight f a => simp [hoSize]
  | lam name body => simp [hoSize]
  | recurBase b s n => simp [hoSize]; omega
  | recurStep b s n => simp [hoSize]; omega
  | recurCounter b s n => simp [hoSize]
  | shareLeft x y => simp [hoSize]; omega
  | shareRight x y => simp [hoSize]
  | trans hxy hyz ihxy ihyz => exact Nat.lt_trans ihxy ihyz

/-- The proper-subterm relation is well founded. -/
theorem hoStrictSubterm_wellFounded : WellFounded HOStrictSubterm := by
  apply Subrelation.wf
    (r := fun x y : HOTerm => hoSize x < hoSize y)
  · intro x y h
    exact hoStrictSubterm_size_lt h
  · exact InvImage.wf hoSize Nat.lt_wfRel.wf

/-- Matched and recursive counters in the higher-order recursor schema. -/
def hoMatchedCounter : HOTerm := .succ (.var 0)

def hoRecursiveCounter : HOTerm := .var 0

/-- The recursive counter is an accessible proper subterm of the matched
constructor argument. -/
theorem ho_recursive_counter_subterm :
    HOStrictSubterm hoRecursiveCounter hoMatchedCounter :=
  HOStrictSubterm.succ _

/-- The same structural fact is stable under the repository substitution on
the counter variable. -/
theorem ho_recursive_counter_subterm_after_substitution (replacement : HOTerm) :
    HOStrictSubterm
      (substitute 0 replacement hoRecursiveCounter)
      (substitute 0 replacement hoMatchedCounter) := by
  simp [hoRecursiveCounter, hoMatchedCounter]
  exact HOStrictSubterm.succ replacement

/-- A nondecreasing recursive call is rejected by proper-subterm admission. -/
theorem ho_non_decreasing_call_rejected :
    Not (HOStrictSubterm hoMatchedCounter hoRecursiveCounter) := by
  intro h
  have hs := hoStrictSubterm_size_lt h
  simp [hoMatchedCounter, hoRecursiveCounter, hoSize] at hs

/-! ## HORPO admission fragment -/

/-- Root tags used by the specialized higher-order path-order carrier. -/
inductive HORPORoot
  | atom | succ | app | lam | recur | share
  deriving DecidableEq, Repr

/-- Root tag of a higher-order term. -/
def hoRoot : HOTerm -> HORPORoot
  | .var _ => .atom
  | .atom => .atom
  | .succ _ => .succ
  | .app _ _ => .app
  | .lam _ _ => .lam
  | .recur _ _ _ => .recur
  | .share _ _ => .share

/-- A specialized HORPO method. The relation is generated from native proper
subterms and strict root precedence. -/
structure HORPOAdmissionMethod where
  precedence : HORPORoot -> Nat
  status : HORPORoot -> OperatorKO7.Methods.PathOrderRows.ArgStatus

/-- Numeric status tag used only as the second component of the root tie-break. -/
def horpoStatusRank : OperatorKO7.Methods.PathOrderRows.ArgStatus -> Nat
  | .lex => 0
  | .mul => 1

/-- Root key computed from both stored method fields. -/
def horpoRootKey (M : HORPOAdmissionMethod) (t : HOTerm) : Nat × Nat :=
  (M.precedence (hoRoot t), horpoStatusRank (M.status (hoRoot t)))

/-- Root comparison computed from precedence and argument status. -/
def HORPORootLt (M : HORPOAdmissionMethod) (x y : HOTerm) : Prop :=
  Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
    (horpoRootKey M x) (horpoRootKey M y)

/-- Method-defined strict comparison. -/
inductive HORPOGt (M : HORPOAdmissionMethod) : HOTerm -> HOTerm -> Prop
  | subterm {x y : HOTerm} : HOStrictSubterm y x -> HORPOGt M x y
  | precedence {x y : HOTerm} : HORPORootLt M y x ->
      hoSize y <= hoSize x -> HORPOGt M x y

/-- Every comparison decreases the pair of structural size and native root key. -/
theorem horpoGt_key_decreases {M : HORPOAdmissionMethod} {x y : HOTerm}
    (h : HORPOGt M x y) :
    Prod.Lex (fun a b : Nat => a < b)
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      (hoSize y, horpoRootKey M y) (hoSize x, horpoRootKey M x) := by
  cases h with
  | subterm hsub =>
      exact Prod.Lex.left _ _ (hoStrictSubterm_size_lt hsub)
  | precedence hroot hsize =>
      by_cases hs : hoSize y = hoSize x
      · rw [hs]
        exact Prod.Lex.right _ hroot
      · have hlt : hoSize y < hoSize x := lt_of_le_of_ne hsize hs
        exact Prod.Lex.left _ _ hlt

/-- The specialized HORPO comparison has a well-founded reverse. -/
theorem horpoGt_wellFounded (M : HORPOAdmissionMethod) :
    WellFounded (fun y x : HOTerm => HORPOGt M x y) := by
  have hroot : WellFounded
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)) :=
    WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  have hkey : WellFounded
      (Prod.Lex (fun a b : Nat => a < b)
        (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))) :=
    WellFounded.prod_lex Nat.lt_wfRel.wf hroot
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex (fun a b : Nat => a < b)
        (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)))
      (fun t => (hoSize t, horpoRootKey M t)))
  · intro y x h
    exact horpoGt_key_decreases h
  · exact InvImage.wf (fun t => (hoSize t, horpoRootKey M t)) hkey

/-- The recursive call is admitted through the native subterm rule. -/
theorem HORPOGt_admits_recursive_call (M : HORPOAdmissionMethod) :
    HORPOGt M hoMatchedCounter hoRecursiveCounter :=
  HORPOGt.subterm ho_recursive_counter_subterm

/-- A concrete precedence and status assignment. -/
def ko7HORPOAdmissionMethod : HORPOAdmissionMethod where
  precedence
    | .atom => 0
    | .succ => 1
    | .app => 2
    | .lam => 3
    | .share => 4
    | .recur => 5
  status
    | .app | .recur => .lex
    | _ => .mul

/-- The precedence branch is nonempty and uses the stored precedence. -/
theorem ko7HORPO_precedence_branch_nonempty :
    HORPOGt ko7HORPOAdmissionMethod (.recur .atom .atom .atom) (.app .atom .atom) := by
  apply HORPOGt.precedence
  · exact Prod.Lex.left _ _ (by decide)
  · simp [hoSize]

/-! ## Computability-path admission fragment -/

/-- Computability closure rules needed by the displayed first-order recursor
inside higher-order syntax. -/
inductive HOComputabilityClosure : HOTerm -> HOTerm -> Prop
  | accessible {x y : HOTerm} : HOStrictSubterm x y -> HOComputabilityClosure x y
  | underBinder {x y : HOTerm} (name : Nat) :
      HOComputabilityClosure x y -> HOComputabilityClosure (.lam name x) (.lam name y)

/-- Every native computability-closure step is structurally decreasing. -/
theorem hoComputabilityClosure_size_lt {x y : HOTerm}
    (h : HOComputabilityClosure x y) : hoSize x < hoSize y := by
  induction h with
  | accessible hsub => exact hoStrictSubterm_size_lt hsub
  | underBinder name h ih =>
      simp [hoSize]
      omega

/-- The native computability closure is well founded. -/
theorem hoComputabilityClosure_wellFounded : WellFounded HOComputabilityClosure := by
  apply Subrelation.wf (r := fun x y : HOTerm => hoSize x < hoSize y)
  · intro x y h
    exact hoComputabilityClosure_size_lt h
  · exact InvImage.wf hoSize Nat.lt_wfRel.wf

/-- Recursive counter belongs to the native computability closure. -/
theorem ho_recursive_counter_computable :
    HOComputabilityClosure hoRecursiveCounter hoMatchedCounter :=
  HOComputabilityClosure.accessible ho_recursive_counter_subterm

/-- Binder closure is an actual proof rule. -/
theorem ho_computability_under_binder :
    HOComputabilityClosure (.lam 7 hoRecursiveCounter) (.lam 7 hoMatchedCounter) :=
  HOComputabilityClosure.underBinder 7 ho_recursive_counter_computable

/-- Substitution exposes the recursive-call witness for every replacement. -/
theorem ho_computability_after_counter_substitution (replacement : HOTerm) :
    HOComputabilityClosure
      (substitute 0 replacement hoRecursiveCounter)
      (substitute 0 replacement hoMatchedCounter) :=
  HOComputabilityClosure.accessible
    (ho_recursive_counter_subterm_after_substitution replacement)

/-! ## General schema and guarded recursion -/

/-- A recursive-call record ties source and target counters to an actual
proper-subterm derivation. -/
structure GeneralSchemaCall where
  matched : HOTerm
  recursive : HOTerm
  descent : HOStrictSubterm recursive matched

/-- Concrete recursor call. -/
def ko7GeneralSchemaCall : GeneralSchemaCall where
  matched := hoMatchedCounter
  recursive := hoRecursiveCounter
  descent := ho_recursive_counter_subterm

/-- Guard derivations are explicit proof objects. -/
inductive GuardDerivation : HOTerm -> HOTerm -> Prop
  | structural {recursive matched : HOTerm} :
      HOStrictSubterm recursive matched -> GuardDerivation recursive matched

/-- The displayed recursive call satisfies the guard. -/
theorem ko7GuardDerivation : GuardDerivation hoRecursiveCounter hoMatchedCounter :=
  GuardDerivation.structural ho_recursive_counter_subterm

/-- The reversed call has no guard derivation. -/
theorem ko7ReverseGuard_rejected :
    Not (GuardDerivation hoMatchedCounter hoRecursiveCounter) := by
  intro h
  cases h with
  | structural hsub => exact ho_non_decreasing_call_rejected hsub

/-! ## Sized types -/

/-- A term paired with a size index. -/
structure SizedHOTerm where
  term : HOTerm
  size : Nat

/-- Sized recursive-call derivation. -/
inductive SizedCall : SizedHOTerm -> SizedHOTerm -> Prop
  | descend {source target : SizedHOTerm} :
      HOStrictSubterm target.term source.term -> target.size < source.size ->
      SizedCall source target

/-- Concrete size-indexed accepted recursive call. -/
theorem sizedCall_accepted :
    SizedCall ⟨hoMatchedCounter, 1⟩ ⟨hoRecursiveCounter, 0⟩ :=
  SizedCall.descend ho_recursive_counter_subterm (by decide)

/-- Equal size indices reject the same structural call. -/
theorem sizedCall_equal_index_rejected :
    Not (SizedCall ⟨hoMatchedCounter, 0⟩ ⟨hoRecursiveCounter, 0⟩) := by
  intro h
  cases h with
  | descend _ hs => exact Nat.lt_irrefl 0 hs

/-! ## Bellantoni-Cook and ramified rule data -/

/-- Generic safe/normal resource condition for a schema rule. -/
def SafePayloadLinear (source target : STerm) : Prop :=
  countVar SchemaVar.s target <= countVar SchemaVar.s source

/-- A safe/normal rule derivation with an explicit tier assignment. -/
structure SafeNormalRuleDerivation (source target : STerm) where
  tier : Fin 3 -> Tier
  counterNormal : tier 2 = .normal
  payloadSafe : tier 1 = .safe
  safeLinear : SafePayloadLinear source target

/-- A positive nonduplicating safe/normal control. -/
def safeNormalIdentity : SafeNormalRuleDerivation dupSrc dupSrc where
  tier := ko7Tier
  counterNormal := rfl
  payloadSafe := rfl
  safeLinear := le_rfl

/-- The duplicating rule has no safe/normal derivation under this method
semantics. -/
theorem no_safeNormalDupDerivation :
    Not (Nonempty (SafeNormalRuleDerivation dupSrc dupTgt)) := by
  rintro ⟨D⟩
  have hs := D.safeLinear
  unfold SafePayloadLinear at hs
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

/-- Generic ramified rule derivation. -/
structure RamifiedRuleDerivation (source target : STerm) where
  level : Fin 3 -> Nat
  baseBelowCounter : level 0 < level 2
  payloadBelowCounter : level 1 < level 2
  resource : countVar SchemaVar.s target <= countVar SchemaVar.s source

/-- Positive ramified identity control. -/
def ramifiedIdentity : RamifiedRuleDerivation dupSrc dupSrc where
  level := fun i => if i = 2 then 1 else 0
  baseBelowCounter := by simp
  payloadBelowCounter := by simp
  resource := le_rfl

/-- The duplicating rule has no ramified derivation. -/
theorem no_ramifiedDupDerivation :
    Not (Nonempty (RamifiedRuleDerivation dupSrc dupTgt)) := by
  rintro ⟨D⟩
  have hs := D.resource
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

/-! ## Linear resource typing controls -/

/-- Existing resource-sound rule typing accepts identity and rejects the
payload-duplicating rule. -/
theorem resourceTyping_positive_negative :
    maximalResourceSoundRuleTyping.Derivable dupSrc dupSrc ∧
      Not (maximalResourceSoundRuleTyping.Derivable dupSrc dupTgt) := by
  exact ⟨maximalResourceSoundRuleTyping_accepts_identity dupSrc,
    no_resourceSoundRuleTyping_derives_dup maximalResourceSoundRuleTyping⟩

/-! ## Finite and infinite reduction semantics -/

/-- A one-state self-loop relation with an explicit infinite reduction. -/
def UnitLoop (_ _ : Unit) : Prop := True

/-- The unit self-loop admits an infinite forward reduction. -/
theorem unitLoop_has_infinite_reduction : InfiniteForwardReduction UnitLoop := by
  refine ⟨⟨fun _ => (), ?_⟩⟩
  intro n
  trivial

/-- KO7 full contextual rewriting excludes the same object. -/
theorem finite_infinite_semantics_separated :
    InfiniteForwardReduction UnitLoop ∧
      Not (InfiniteForwardReduction MetaSN_KO7.StepCtxFull) :=
  ⟨unitLoop_has_infinite_reduction, no_infinite_stepCtxFull_reduction⟩

/-! ## Abstract interpretation as a computed call state -/

/-- Three-coordinate abstract state for base, payload and counter sizes. -/
def abstractCallState (t : STerm) : Fin 3 -> Nat :=
  match t with
  | .recur b s n => fun i =>
      if i = 0 then OperatorKO7.Methods.PathOrderRows.stermSize b
      else if i = 1 then OperatorKO7.Methods.PathOrderRows.stermSize s
      else OperatorKO7.Methods.PathOrderRows.stermSize n
  | _ => fun _ => 0

/-- The displayed recursor source and recursive call keep base/payload sizes and
strictly decrease the counter coordinate. -/
theorem abstractCallState_dup_counter_descent :
    abstractCallState dupTgt 0 = 0 ∧
    abstractCallState dupSrc 0 = 1 ∧
    abstractCallState
      (STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s)
        recursiveCallCounter) 2 <
      abstractCallState dupSrc 2 := by
  simp [abstractCallState, dupSrc, dupTgt, recursiveCallCounter,
    OperatorKO7.Methods.PathOrderRows.stermSize]

/-- Native abstract interpretation package connected to the size-change graph. -/
structure AbstractInterpretationMethod where
  abstract : STerm -> Fin 3 -> Nat
  counterDescent :
    abstract
      (STerm.recur (STerm.var SchemaVar.b) (STerm.var SchemaVar.s)
        recursiveCallCounter) 2 <
      abstract dupSrc 2
  sct : OperatorKO7.ConfessionMethodFamily.sctSatisfied
    OperatorKO7.ConfessionMethodFamily.schemaRecCallGraph

/-- Concrete abstract interpretation. -/
def abstractInterpretationMethod : AbstractInterpretationMethod where
  abstract := abstractCallState
  counterDescent := abstractCallState_dup_counter_descent.2.2
  sct := OperatorKO7.ConfessionMethodFamily.schema_sct_satisfied

/-! ## ORI-5 package -/

structure HigherOrderNativeBundle where
  horpo : HORPOAdmissionMethod
  horpoCall : HORPOGt horpo hoMatchedCounter hoRecursiveCounter
  cpoCall : HOComputabilityClosure hoRecursiveCounter hoMatchedCounter
  generalSchema : GeneralSchemaCall
  guard : GuardDerivation hoRecursiveCounter hoMatchedCounter
  sized : SizedCall ⟨hoMatchedCounter, 1⟩ ⟨hoRecursiveCounter, 0⟩
  safeNormalPositive : SafeNormalRuleDerivation dupSrc dupSrc
  resourcePositive : maximalResourceSoundRuleTyping.Derivable dupSrc dupSrc
  resourceDupBlocked : Not (maximalResourceSoundRuleTyping.Derivable dupSrc dupTgt)
  ramifiedPositive : RamifiedRuleDerivation dupSrc dupSrc
  abstractMethod : AbstractInterpretationMethod
  infiniteControl : InfiniteForwardReduction UnitLoop

/-- Concrete ORI-5 method package. -/
def higherOrderNativeBundle : HigherOrderNativeBundle where
  horpo := ko7HORPOAdmissionMethod
  horpoCall := HORPOGt_admits_recursive_call ko7HORPOAdmissionMethod
  cpoCall := ho_recursive_counter_computable
  generalSchema := ko7GeneralSchemaCall
  guard := ko7GuardDerivation
  sized := sizedCall_accepted
  safeNormalPositive := safeNormalIdentity
  resourcePositive := maximalResourceSoundRuleTyping_accepts_identity dupSrc
  resourceDupBlocked := no_resourceSoundRuleTyping_derives_dup maximalResourceSoundRuleTyping
  ramifiedPositive := ramifiedIdentity
  abstractMethod := abstractInterpretationMethod
  infiniteControl := unitLoop_has_infinite_reduction

end OperatorKO7.Methods.OrientationClosure.HigherOrderNativeSemantics
