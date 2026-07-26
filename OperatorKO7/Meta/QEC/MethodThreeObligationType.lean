import OperatorKO7.Meta.Physics.QECSyndromeAsStage2

/-!
# QEC Method 3 obligation carrier

## Formal Scope

QECMethodThreeObligation stores two-round syndrome data and gauge-invariant counts. This module defines no leakage predicate or offset theorem, and its bookkeeping anchor does not consume WellFormed or the count fields.
-/

namespace OperatorKO7.Meta.QEC.MethodThreeObligationType

open OperatorKO7.Meta.Physics.QECSyndromeAsStage2
open OperatorKO7.Meta.Physics.RecordFormation

/-- Concrete two-point round carrier for Method 3. The nontrivial gauge action
swaps the two labels. -/
inductive SyndromeRound
  | reference
  | gaugeTwin
  deriving DecidableEq, Repr

/-- The nontrivial gauge orbit swaps the two Method 3 round labels. -/
def flipRound : SyndromeRound → SyndromeRound
  | .reference => .gaugeTwin
  | .gaugeTwin => .reference

@[simp] theorem flipRound_flipRound (t : SyndromeRound) : flipRound (flipRound t) = t := by
  cases t <;> rfl

/-- Carrier storing a QEC stage-2 syndrome record and two natural-number counts
for each typed round label. The structure itself defines no leakage or offset
predicate. -/
structure QECMethodThreeObligation where
  syndrome : SyndromeRound → QECSyndromeRound
  a_q : SyndromeRound → Nat
  c_q : SyndromeRound → Nat
  gaugeInvariant :
    ∀ t, a_q (flipRound t) = a_q t ∧ c_q (flipRound t) = c_q t

/-- Count-pair view of the Method 3 carrier. -/
def countPair (obligation : QECMethodThreeObligation) (t : SyndromeRound) : Nat × Nat :=
  (obligation.a_q t, obligation.c_q t)

/-- Basic well-formedness gate for the Method 3 obligation. Every stored
syndrome round is stage-2 ready. -/
def WellFormedQECMethodThreeObligation (obligation : QECMethodThreeObligation) : Prop :=
  ∀ t,
    0 < (obligation.syndrome t).syndromeBitCount ∧
    (obligation.syndrome t).redundancyThreshold ≤ (obligation.syndrome t).redundancyCount

/-- Apply the imported syndrome-bookkeeping theorem to the stored syndrome at
one round. This theorem is independent of `WellFormedQECMethodThreeObligation`
and the two count fields. -/
theorem qec_method_three_obligation_anchor
    (obligation : QECMethodThreeObligation)
    (t : SyndromeRound) :
    C6_HonestBitBookkeeping
      (qecSyndromeAsRecordFormation (obligation.syndrome t)) :=
  qecSyndromeAsRecordFormation_honestBitBookkeeping (obligation.syndrome t)

end OperatorKO7.Meta.QEC.MethodThreeObligationType
