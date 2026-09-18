/-!
# RDRS Raw Direct-Measure Syntax (U2 Route B, milestone foundation)

Closed-grammar syntax for raw direct measures and raw direct orders, with no
semantic content and no U1 dependencies. The grammar is intentionally small
and reviewable; it is the obligation surface Milestone U2 (Route B) needs in
order to define a decidable `payloadSensitive?` predicate and prove
soundness + completeness over the raw direct-measure syntax.

Scope explicitly carved out by the dispatch:

* No DP processors (DP framework lives downstream of U2).
* No full MSPO (MSPO carries semantic content that U2 cannot import).
* No arbitrary monotone algebras (the universe is closed-grammar, not
  algebra-parametric).
* No arbitrary semantic quotients (semantic quotients are non-syntactic).
* No unrestricted semantic labeling (semantic labeling is U5+ scope).

Every constructor in `RawDirectMeasure` and `RawDirectOrder` is a finite
syntactic AST node with no implicit semantic side condition. The grammar is
total; every well-typed application of a constructor produces a well-formed
term in the syntax. `DecidableEq` and `Repr` are derived so downstream
modules can structurally decide equality and pretty-print witnesses without
inviting heavier semantics.

No proof placeholder is used and no top-level postulate is declared.
-/

namespace OperatorKO7.RDRSRawDirectMeasure

/-- Variable role tag used inside the raw measure grammar. The payload role
identifies the duplicated argument (`s` in the RDRS rewrite rule
`recur(b, s, succ(n)) -> wrap(s, recur(b, s, n))`); the base role identifies
`b`; the counter role identifies `n`. The grammar treats every other
position as `other` so the universe does not implicitly require a fixed
arity beyond the three named roles. -/
inductive PayloadRole
  | payload
  | base
  | counter
  | other
  deriving DecidableEq, Repr

/-- Raw direct-measure syntax over RDRS terms.

The grammar is closed: every measure is a finite tree whose leaves are
constants, variable-occurrence counters, term size, or term depth, and
whose internal nodes are the addition, scalar multiplication, max, and
pump-projection constructors. No semantic content is attached. -/
inductive RawDirectMeasure
  /-- A constant natural-number contribution to the measure. -/
  | constant       (n : Nat)
  /-- Count occurrences of a variable in the given role at the term level. -/
  | occurCount     (role : PayloadRole)
  /-- The symbol-count of the input term (a closed-grammar surrogate for
  ``|t|`` in the literature; payload occurrences contribute via
  `occurCount .payload`, not via this constructor). -/
  | termSize
  /-- The depth of the input term. -/
  | termDepth
  /-- Sum of two raw direct measures. -/
  | addM           (a b : RawDirectMeasure)
  /-- Scalar multiplication of a raw direct measure by a constant. -/
  | mulConst       (c : Nat) (a : RawDirectMeasure)
  /-- Pointwise max of two raw direct measures. -/
  | maxM           (a b : RawDirectMeasure)
  deriving DecidableEq, Repr

/-- Raw direct-order syntax.

The grammar is closed: every order is a finite tree built from the basic
natural-number strict / non-strict comparisons and the pair / lexicographic
combinators. The pair combinator carries the strict-product comparison
(strict in both components); the lex combinator carries the leading-first
lexicographic comparison. -/
inductive RawDirectOrder
  /-- Strict natural-number order `<`. -/
  | natLt
  /-- Non-strict natural-number order `<=`. -/
  | natLe
  /-- Lexicographic pair order: leading component strict; then trailing. -/
  | productLex     (h t : RawDirectOrder)
  /-- Componentwise pair order: both components in the underlying orders. -/
  | productPair    (h t : RawDirectOrder)
  deriving DecidableEq, Repr

/-! ### Decidable syntactic payload presence

`containsPayloadOccur` is a decidable Boolean predicate on
`RawDirectMeasure` that returns `true` iff the measure tree mentions a
payload-role variable-occurrence counter. The predicate is the syntactic
core of the downstream `payloadSensitive?` decision: a raw direct measure
whose grammar witnesses zero references to the payload role cannot be
payload-sensitive at the level of syntax, regardless of any semantic
content the certificate might carry.
-/

/-- Recursively check whether the measure tree mentions
`occurCount PayloadRole.payload`. -/
def RawDirectMeasure.containsPayloadOccur : RawDirectMeasure → Bool
  | .constant _                  => false
  | .occurCount .payload         => true
  | .occurCount _                => false
  | .termSize                    => false
  | .termDepth                   => false
  | .addM a b                    =>
      a.containsPayloadOccur || b.containsPayloadOccur
  | .mulConst _ a                => a.containsPayloadOccur
  | .maxM a b                    =>
      a.containsPayloadOccur || b.containsPayloadOccur

/-- Recursive non-recursive check that the order is the strict natural-
number comparison anywhere in its tree (necessary for any descent-style
certificate to encode a strict step on the payload coordinate). -/
def RawDirectOrder.containsNatLt : RawDirectOrder → Bool
  | .natLt          => true
  | .natLe          => false
  | .productLex h t => h.containsNatLt || t.containsNatLt
  | .productPair h t => h.containsNatLt || t.containsNatLt

/-! ### Per-constructor smoke lemmas

The lemmas below confirm the recursive predicate evaluates to the expected
Boolean on each leaf constructor. They are by `rfl` and serve as both a
sanity audit of the recursive definition and as reach pins for downstream
modules. -/

theorem containsPayloadOccur_payload :
    (RawDirectMeasure.occurCount PayloadRole.payload).containsPayloadOccur
      = true := rfl

theorem containsPayloadOccur_base :
    (RawDirectMeasure.occurCount PayloadRole.base).containsPayloadOccur
      = false := rfl

theorem containsPayloadOccur_counter :
    (RawDirectMeasure.occurCount PayloadRole.counter).containsPayloadOccur
      = false := rfl

theorem containsPayloadOccur_other :
    (RawDirectMeasure.occurCount PayloadRole.other).containsPayloadOccur
      = false := rfl

theorem containsPayloadOccur_constant (n : Nat) :
    (RawDirectMeasure.constant n).containsPayloadOccur = false := rfl

theorem containsPayloadOccur_termSize :
    RawDirectMeasure.termSize.containsPayloadOccur = false := rfl

theorem containsPayloadOccur_termDepth :
    RawDirectMeasure.termDepth.containsPayloadOccur = false := rfl

theorem containsNatLt_natLt : RawDirectOrder.natLt.containsNatLt = true := rfl

theorem containsNatLt_natLe : RawDirectOrder.natLe.containsNatLt = false := rfl

end OperatorKO7.RDRSRawDirectMeasure
