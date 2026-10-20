import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import Mathlib.Data.Prod.Lex

/-!
# Same-source call extraction and dependency-chain soundness

This module is independent of the concrete KO7 term type.  It gives the free
recursor an exact recursive-call extractor and separates three obligations:
source rule membership, transformed-call descent, and weak connector control.
Pair well-foundedness by itself is deliberately not promoted to source
termination.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SourceChainSoundness

open OperatorKO7.Methods.OrientationClosure.SchemaCore

universe u

/-! ## Exact free-recursive-call extraction -/

/-- Universe-polymorphic leading-successor depth. -/
def succDepth {ν : Type u} : FreeTerm ν → Nat
  | .succ t => succDepth t + 1
  | _ => 0

/-- Recursive-call rank used only for the transformed call relation. -/
def recursiveCallRank {ν : Type u} : FreeTerm ν → Nat
  | .recur b _ n => succDepth n + recursiveCallRank b
  | .wrap _ t => recursiveCallRank t
  | _ => 0

/-- The transformed recursive call of the successor rule.  The zero rule has no
recursive call. -/
inductive FreeRecursiveCallPair {ν : Type u} : FreeTerm ν → FreeTerm ν → Prop
  | successor (b s n : FreeTerm ν) :
      FreeRecursiveCallPair (.recur b s (.succ n)) (.recur b s n)

/-- The occurrence relation records the source term, its actual rewrite target,
and the recursive call occurring under the wrapper in that same target. -/
inductive FreeCallOccurrence {ν : Type u} :
    FreeTerm ν → FreeTerm ν → FreeTerm ν → Prop
  | successor (b s n : FreeTerm ν) :
      FreeCallOccurrence
        (.recur b s (.succ n))
        (.wrap s (.recur b s n))
        (.recur b s n)

/-- Executable recursive-call extractor. -/
def extractRecursiveCall {ν : Type u} : FreeTerm ν → Option (FreeTerm ν)
  | .recur b s (.succ n) => some (.recur b s n)
  | _ => none

/-- Exact source/target/call specification of the executable extractor. -/
theorem extractRecursiveCall_some_iff
    {ν : Type u} (a c : FreeTerm ν) :
    extractRecursiveCall a = some c ↔
      ∃ rhs, RootStep a rhs ∧ FreeCallOccurrence a rhs c := by
  constructor
  · intro h
    cases a <;> simp [extractRecursiveCall] at h
    case recur b s n =>
      cases n <;> simp at h
      case succ n =>
        cases h
        exact ⟨.wrap s (.recur b s n), .recurSucc b s n,
          .successor b s n⟩
  · rintro ⟨rhs, hstep, hocc⟩
    cases hocc
    rfl

/-- The relational pair is exactly the graph of the successful extractor. -/
theorem freeRecursiveCallPair_iff_extract
    {ν : Type u} (a c : FreeTerm ν) :
    FreeRecursiveCallPair a c ↔ extractRecursiveCall a = some c := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases a <;> simp [extractRecursiveCall] at h
    case recur b s n =>
      cases n <;> simp at h
      case succ n =>
        cases h
        exact .successor b s n

/-- Every extracted call comes from the successor source rule and from no other
root rule. -/
theorem freeRecursiveCallPair_has_source
    {ν : Type u} {a c : FreeTerm ν} (h : FreeRecursiveCallPair a c) :
    ∃ rhs, RootStep a rhs ∧ FreeCallOccurrence a rhs c :=
  (extractRecursiveCall_some_iff a c).1
    ((freeRecursiveCallPair_iff_extract a c).1 h)

/-- The extracted recursive call strictly decreases its universe-polymorphic
call rank. -/
theorem freeRecursiveCallPair_rank_decreases
    {ν : Type u} {a c : FreeTerm ν} (h : FreeRecursiveCallPair a c) :
    recursiveCallRank c < recursiveCallRank a := by
  cases h with
  | successor b s n =>
      simp [recursiveCallRank, succDepth]

/-- Hence the transformed-call relation itself is well founded. -/
theorem freeRecursiveCallPair_wellFounded (ν : Type u) :
    WellFounded (fun y x : FreeTerm ν => FreeRecursiveCallPair x y) := by
  apply Subrelation.wf
    (r := fun y x : FreeTerm ν => recursiveCallRank y < recursiveCallRank x)
  · intro y x h
    exact freeRecursiveCallPair_rank_decreases h
  · exact InvImage.wf recursiveCallRank Nat.lt_wfRel.wf

/-- The zero rule has no extracted recursive call. -/
theorem extractRecursiveCall_zero_rule_none
    {ν : Type u} (b s : FreeTerm ν) :
    extractRecursiveCall (.recur b s .zero) = none := rfl

/-- The successor rule has exactly its recursive call. -/
theorem extractRecursiveCall_successor_exact
    {ν : Type u} (b s n : FreeTerm ν) :
    extractRecursiveCall (.recur b s (.succ n)) = some (.recur b s n) := rfl

/-! ## Generic connector-aware dependency chains -/

/-- One dependency-chain step consists of one strict pair edge followed by a
possibly empty connector path. -/
def ChainStep {α : Type u} (Pair Connect : α → α → Prop) (a c : α) : Prop :=
  ∃ b, Pair a b ∧ Relation.ReflTransGen Connect b c

/-- Reduction-pair data sufficient to orient the chain relation.  Strict pair
edges and weak connectors are properties of the same supplied relations. -/
structure ChainReductionPair (α : Type u)
    (Pair Connect : α → α → Prop) where
  weak : α → α → Prop
  strict : α → α → Prop
  weak_refl : Reflexive weak
  weak_trans : Transitive weak
  strict_reverse_wellFounded : WellFounded (fun y x => strict x y)
  pair_strict : ∀ {a b}, Pair a b → strict a b
  connector_weak : ∀ {a b}, Connect a b → weak a b
  strict_weak : ∀ {a b c}, strict a b → weak b c → strict a c

/-- A finite connector path is weak for any reduction-pair interface. -/
theorem connectorStar_weak
    {α : Type u} {Pair Connect : α → α → Prop}
    (P : ChainReductionPair α Pair Connect)
    {a b : α} (h : Relation.ReflTransGen Connect a b) : P.weak a b := by
  induction h with
  | refl => exact P.weak_refl _
  | tail hpre hstep ih =>
      exact P.weak_trans ih (P.connector_weak hstep)

/-- Every dependency-chain step is strict in the same reduction pair. -/
theorem chainStep_strict
    {α : Type u} {Pair Connect : α → α → Prop}
    (P : ChainReductionPair α Pair Connect)
    {a c : α} (h : ChainStep Pair Connect a c) : P.strict a c := by
  rcases h with ⟨b, hab, hbc⟩
  exact P.strict_weak (P.pair_strict hab) (connectorStar_weak P hbc)

/-- Pair strictness plus connector weakness proves dependency-chain
well-foundedness. -/
theorem chainStep_wellFounded
    {α : Type u} {Pair Connect : α → α → Prop}
    (P : ChainReductionPair α Pair Connect) :
    WellFounded (fun y x => ChainStep Pair Connect x y) := by
  apply Subrelation.wf (r := fun y x => P.strict x y)
  · intro y x h
    exact chainStep_strict P h
  · exact P.strict_reverse_wellFounded

/-! ## Source termination is a separate bridge obligation -/

/-- Source-side lexicographic bridge.  This is intentionally not a field of the
pair problem: pair termination alone is not source termination. -/
structure SourceLexBridge (α : Type u) (Source : α → α → Prop) where
  primary : α → Nat
  secondary : α → Nat
  decreases : ∀ {a b}, Source a b →
    Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
      (primary b, secondary b) (primary a, secondary a)

/-- A genuine source bridge proves source strong normalization. -/
theorem source_wellFounded_of_lexBridge
    {α : Type u} {Source : α → α → Prop} (B : SourceLexBridge α Source) :
    WellFounded (fun y x => Source x y) := by
  have hlex : WellFounded
      (Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)) :=
    WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y))
      (fun a => (B.primary a, B.secondary a)))
  · intro y x h
    exact B.decreases h
  · exact InvImage.wf (fun a => (B.primary a, B.secondary a)) hlex

/-! ## Pair-only control -/

/-- A source with a self-loop and no transformed calls. -/
def pairFreeLoopSource (_ _ : Unit) : Prop := True

def emptyPair (_ _ : Unit) : Prop := False

/-- Empty transformed calls are trivially well founded. -/
theorem emptyPair_wellFounded :
    WellFounded (fun y x : Unit => emptyPair x y) := by
  exact ⟨fun a => Acc.intro a (fun _ h => False.elim h)⟩

/-- The source self-loop is not well founded. -/
theorem pairFreeLoopSource_not_wellFounded :
    ¬ WellFounded (fun y x : Unit => pairFreeLoopSource x y) := by
  intro hwf
  have hloop : pairFreeLoopSource () () := trivial
  exact (hwf.asymmetric () () hloop) hloop

/-- Machine-checked separation: transformed-call well-foundedness alone cannot
serve as a source-termination theorem. -/
theorem pair_wellFounded_does_not_imply_source_wellFounded :
    WellFounded (fun y x : Unit => emptyPair x y) ∧
      ¬ WellFounded (fun y x : Unit => pairFreeLoopSource x y) :=
  ⟨emptyPair_wellFounded, pairFreeLoopSource_not_wellFounded⟩

end OperatorKO7.Methods.OrientationClosure.SourceChainSoundness
