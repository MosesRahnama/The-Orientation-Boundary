import OperatorKO7.Meta.RightDuplicatingRecursorSchema

/-!
# Non-KO7 RDRS Instances

Phase A.3 (Sprint 3) of the recursive-family expansion roadmap.

This module ships three concrete `RightDuplicatingRecursorSchema` (RDRS)
instances that are deliberately not KO7. The point is to prevent vacuous
universality: the RDRS shell of `Meta/RightDuplicatingRecursorSchema.lean`
must classify more than one named system before any later canonical-witness
universality claim is honest. The three instances also exercise the three
shapes the roadmap (`THEORY_EXPANSION.md` Phase A.3) names:

1. `textbookRDRS` -- the standard duplicating rule `f(x, s(y)) -> g(x, f(x, y))`.
2. `taggedBinaryRDRS` -- a binary-tag recursor with `Bit0` and `Bit1` branches.
3. `depthCounterRDRS` -- a depth-counter recursor whose distinguished payload
   is a depth coordinate, not a step argument carried over from KO7.

These are small structural witnesses, not full termination developments. No
direct measure barrier is proved here. The RDRS interface contracts
(`lhs_has_payload`, `rhs_duplicates_payload`, `firesOnClosedTerms`) are the
only obligations discharged.

The module touches no existing 12-base-class theorem name or signature and uses
no proof placeholders.
-/

namespace OperatorKO7.StepDuplicating
namespace RDRSNonKO7Instances

-- ---------------------------------------------------------------------------
-- Instance 1: textbook duplication TRS  f(x, s(y)) -> g(x, f(x, y))
-- ---------------------------------------------------------------------------

/-- Minimal syntax for the textbook duplicating rule
`f(x, s(y)) -> g(x, f(x, y))`. The carrier is small enough that the
distinguished payload (the first argument of `f`) is captured by a single
constructor-counting function. -/
inductive TextbookTerm
  | x : TextbookTerm
  | y : TextbookTerm
  | zero : TextbookTerm
  | succ : TextbookTerm → TextbookTerm
  | f : TextbookTerm → TextbookTerm → TextbookTerm
  | g : TextbookTerm → TextbookTerm → TextbookTerm
  deriving DecidableEq, Repr

namespace TextbookTerm

/-- One coordinate: the distinguished payload variable `x`. -/
inductive Coord
  | xCoord
  deriving DecidableEq, Repr

/-- A small position type: every place `x` can syntactically occur in the
two-rule duplicating pattern. The position set is finite and contains
exactly the occurrences that appear on the lhs or rhs of the rule. -/
inductive Pos
  | lhsArg1
  | rhsOuterArg1
  | rhsInnerArg1
  deriving DecidableEq, Repr

/-- `xOccurAt p t` records that the textbook variable `x` is at structural
position `p` inside term `t`. The predicate is the literal-equality
flattening of `Coord = xCoord` cases at each enumerated position. -/
def xOccurAt : Coord → Pos → TextbookTerm → Prop
  | .xCoord, .lhsArg1,      .f .x _                       => True
  | .xCoord, .rhsOuterArg1, .g .x _                       => True
  | .xCoord, .rhsInnerArg1, .g _ (.f .x _)                => True
  | _,       _,             _                             => False

/-- Count occurrences of `x` in a term. The function is structural recursion
over the carrier; for the lhs and rhs of the rule the value is read off the
enumerated `Pos` cases above. -/
def xCount : Coord → TextbookTerm → Nat
  | .xCoord, .x                 => 1
  | .xCoord, .y                 => 0
  | .xCoord, .zero              => 0
  | .xCoord, .succ t            => xCount .xCoord t
  | .xCoord, .f t1 t2           => xCount .xCoord t1 + xCount .xCoord t2
  | .xCoord, .g t1 t2           => xCount .xCoord t1 + xCount .xCoord t2

/-- Left-hand side of the textbook rule: `f(x, s(y))`. -/
def lhsTerm : TextbookTerm := .f .x (.succ .y)

/-- Right-hand side of the textbook rule: `g(x, f(x, y))`. -/
def rhsTerm : TextbookTerm := .g .x (.f .x .y)

theorem lhs_x_count_eq_one :
    xCount .xCoord lhsTerm = 1 := by
  rfl

theorem rhs_x_count_eq_two :
    xCount .xCoord rhsTerm = 2 := by
  rfl

end TextbookTerm

/-- RDRS view of the textbook duplicating rule. -/
def textbookRDRS : RightDuplicatingRecursorSchema where
  Term := TextbookTerm
  PayloadCoord := TextbookTerm.Coord
  Position := TextbookTerm.Pos
  lhs := TextbookTerm.lhsTerm
  rhs := TextbookTerm.rhsTerm
  payloadOccursAt := TextbookTerm.xOccurAt
  payloadCount := TextbookTerm.xCount
  distinguishedPayload := .xCoord
  lhs_has_payload := TextbookTerm.lhs_x_count_eq_one
  rhs_duplicates_payload := by
    rw [TextbookTerm.rhs_x_count_eq_two]; decide
  firesOnClosedTerms := True

-- ---------------------------------------------------------------------------
-- Instance 2: tagged-binary recursor with `Bit0` / `Bit1` branches
-- ---------------------------------------------------------------------------

/-- A tagged-binary recursor calculus: tags are `Bit0` and `Bit1`, the
distinguished payload `s` is the step argument, and the right-duplicating
rule fires on the `Bit1` branch.

Rule:  `recBin(s, Bit1(n)) -> pair(s, recBin(s, n))`.

The companion `Bit0` rule
`recBin(s, Bit0(n)) -> recBin(s, n)` is not right-duplicating; only the
`Bit1` branch instantiates the RDRS contract. -/
inductive TaggedBinaryTerm
  | sVar : TaggedBinaryTerm
  | nVar : TaggedBinaryTerm
  | bit0 : TaggedBinaryTerm → TaggedBinaryTerm
  | bit1 : TaggedBinaryTerm → TaggedBinaryTerm
  | recBin : TaggedBinaryTerm → TaggedBinaryTerm → TaggedBinaryTerm
  | pair   : TaggedBinaryTerm → TaggedBinaryTerm → TaggedBinaryTerm
  deriving DecidableEq, Repr

namespace TaggedBinaryTerm

inductive Coord
  | sCoord
  deriving DecidableEq, Repr

inductive Pos
  | lhsArg1
  | rhsOuterArg1
  | rhsInnerArg1
  deriving DecidableEq, Repr

def sOccurAt : Coord → Pos → TaggedBinaryTerm → Prop
  | .sCoord, .lhsArg1,      .recBin .sVar _                  => True
  | .sCoord, .rhsOuterArg1, .pair .sVar _                    => True
  | .sCoord, .rhsInnerArg1, .pair _ (.recBin .sVar _)        => True
  | _,       _,             _                                => False

def sCount : Coord → TaggedBinaryTerm → Nat
  | .sCoord, .sVar         => 1
  | .sCoord, .nVar         => 0
  | .sCoord, .bit0 t       => sCount .sCoord t
  | .sCoord, .bit1 t       => sCount .sCoord t
  | .sCoord, .recBin t1 t2 => sCount .sCoord t1 + sCount .sCoord t2
  | .sCoord, .pair t1 t2   => sCount .sCoord t1 + sCount .sCoord t2

/-- Left-hand side: `recBin(s, Bit1(n))`. -/
def lhsTerm : TaggedBinaryTerm := .recBin .sVar (.bit1 .nVar)

/-- Right-hand side: `pair(s, recBin(s, n))`. -/
def rhsTerm : TaggedBinaryTerm := .pair .sVar (.recBin .sVar .nVar)

theorem lhs_s_count_eq_one :
    sCount .sCoord lhsTerm = 1 := by
  rfl

theorem rhs_s_count_eq_two :
    sCount .sCoord rhsTerm = 2 := by
  rfl

end TaggedBinaryTerm

/-- RDRS view of the `Bit1` branch of the tagged-binary recursor. -/
def taggedBinaryRDRS : RightDuplicatingRecursorSchema where
  Term := TaggedBinaryTerm
  PayloadCoord := TaggedBinaryTerm.Coord
  Position := TaggedBinaryTerm.Pos
  lhs := TaggedBinaryTerm.lhsTerm
  rhs := TaggedBinaryTerm.rhsTerm
  payloadOccursAt := TaggedBinaryTerm.sOccurAt
  payloadCount := TaggedBinaryTerm.sCount
  distinguishedPayload := .sCoord
  lhs_has_payload := TaggedBinaryTerm.lhs_s_count_eq_one
  rhs_duplicates_payload := by
    rw [TaggedBinaryTerm.rhs_s_count_eq_two]; decide
  firesOnClosedTerms := True

-- ---------------------------------------------------------------------------
-- Instance 3: depth-counter recursor whose duplicated payload is a depth
-- coordinate, not a step argument.
-- ---------------------------------------------------------------------------

/-- A depth-counter recursor: the duplicated payload is a depth-tagged
variable `d`, not a step argument inherited from KO7.

Rule:  `recDepth(d, succ(n)) -> g(d, recDepth(d, n))`.

The distinguishing feature: `d` is the depth coordinate (intuitively a
`Nat`-like measure passed unchanged through every recursive call), and the
right-hand side duplicates it. This is structurally different from the
textbook and KO7 cases where the duplicated argument is a step input. -/
inductive DepthCounterTerm
  | dVar : DepthCounterTerm
  | nVar : DepthCounterTerm
  | zero : DepthCounterTerm
  | succ : DepthCounterTerm → DepthCounterTerm
  | recDepth : DepthCounterTerm → DepthCounterTerm → DepthCounterTerm
  | g        : DepthCounterTerm → DepthCounterTerm → DepthCounterTerm
  deriving DecidableEq, Repr

namespace DepthCounterTerm

inductive Coord
  | dCoord
  deriving DecidableEq, Repr

inductive Pos
  | lhsArg1
  | rhsOuterArg1
  | rhsInnerArg1
  deriving DecidableEq, Repr

def dOccurAt : Coord → Pos → DepthCounterTerm → Prop
  | .dCoord, .lhsArg1,      .recDepth .dVar _                  => True
  | .dCoord, .rhsOuterArg1, .g .dVar _                         => True
  | .dCoord, .rhsInnerArg1, .g _ (.recDepth .dVar _)           => True
  | _,       _,             _                                  => False

def dCount : Coord → DepthCounterTerm → Nat
  | .dCoord, .dVar             => 1
  | .dCoord, .nVar             => 0
  | .dCoord, .zero             => 0
  | .dCoord, .succ t           => dCount .dCoord t
  | .dCoord, .recDepth t1 t2   => dCount .dCoord t1 + dCount .dCoord t2
  | .dCoord, .g t1 t2          => dCount .dCoord t1 + dCount .dCoord t2

/-- Left-hand side: `recDepth(d, succ(n))`. -/
def lhsTerm : DepthCounterTerm := .recDepth .dVar (.succ .nVar)

/-- Right-hand side: `g(d, recDepth(d, n))`. -/
def rhsTerm : DepthCounterTerm := .g .dVar (.recDepth .dVar .nVar)

theorem lhs_d_count_eq_one :
    dCount .dCoord lhsTerm = 1 := by
  rfl

theorem rhs_d_count_eq_two :
    dCount .dCoord rhsTerm = 2 := by
  rfl

end DepthCounterTerm

/-- RDRS view of the depth-counter recursor. -/
def depthCounterRDRS : RightDuplicatingRecursorSchema where
  Term := DepthCounterTerm
  PayloadCoord := DepthCounterTerm.Coord
  Position := DepthCounterTerm.Pos
  lhs := DepthCounterTerm.lhsTerm
  rhs := DepthCounterTerm.rhsTerm
  payloadOccursAt := DepthCounterTerm.dOccurAt
  payloadCount := DepthCounterTerm.dCount
  distinguishedPayload := .dCoord
  lhs_has_payload := DepthCounterTerm.lhs_d_count_eq_one
  rhs_duplicates_payload := by
    rw [DepthCounterTerm.rhs_d_count_eq_two]; decide
  firesOnClosedTerms := True

-- ---------------------------------------------------------------------------
-- Per-instance smoke theorems: the RDRS contracts hold and the duplication
-- gap is at least one. These reuse the generic lemmas of the RDRS shell.
-- ---------------------------------------------------------------------------

theorem textbookRDRS_gap_pos :
    1 ≤ textbookRDRS.distinguishedDuplicationGap :=
  textbookRDRS.one_le_distinguishedDuplicationGap

theorem taggedBinaryRDRS_gap_pos :
    1 ≤ taggedBinaryRDRS.distinguishedDuplicationGap :=
  taggedBinaryRDRS.one_le_distinguishedDuplicationGap

theorem depthCounterRDRS_gap_pos :
    1 ≤ depthCounterRDRS.distinguishedDuplicationGap :=
  depthCounterRDRS.one_le_distinguishedDuplicationGap

theorem textbookRDRS_rhs_strict :
    textbookRDRS.payloadCount textbookRDRS.distinguishedPayload textbookRDRS.lhs <
      textbookRDRS.payloadCount textbookRDRS.distinguishedPayload textbookRDRS.rhs :=
  textbookRDRS.rhs_count_gt_lhs_count

theorem taggedBinaryRDRS_rhs_strict :
    taggedBinaryRDRS.payloadCount taggedBinaryRDRS.distinguishedPayload taggedBinaryRDRS.lhs <
      taggedBinaryRDRS.payloadCount taggedBinaryRDRS.distinguishedPayload taggedBinaryRDRS.rhs :=
  taggedBinaryRDRS.rhs_count_gt_lhs_count

theorem depthCounterRDRS_rhs_strict :
    depthCounterRDRS.payloadCount depthCounterRDRS.distinguishedPayload depthCounterRDRS.lhs <
      depthCounterRDRS.payloadCount depthCounterRDRS.distinguishedPayload depthCounterRDRS.rhs :=
  depthCounterRDRS.rhs_count_gt_lhs_count

end RDRSNonKO7Instances
end OperatorKO7.StepDuplicating
