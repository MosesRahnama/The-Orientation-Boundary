import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

set_option autoImplicit false

/-!
# The left/right non-linearity dichotomy as a theorem

This module upgrades the last analogy of the Distinction Boundary paper, the
"raw-mechanism correspondence" between the confluence-side and termination-side
boundaries, from a stated principle to a proven structural theorem.

The honest content of the correspondence is the variable-linearity dichotomy of
Klop and Toyama: left-linearity governs confluence, right-linearity (non-
duplication) governs termination. The naive form "non-linearity implies failure"
is *false* (non-linearity is necessary, not sufficient: the recursor duplicates and
still terminates), which is exactly why the program had stated it as a principle
rather than a theorem. What is true, and is proved here, is the structural fact: the
two KO7 boundary source rules are dual instances of one repeated-variable predicate,
on the left-hand side for the confluence boundary and on the right-hand side for the
termination boundary. The confluence side additionally carries the actual unjoinable
fork it produces (`EqWVoidAnomaly`).

Necessity (linearizing either side dissolves the corresponding boundary) is the
existing ablation surface: `Meta/LinearRec_Ablation.lean` for termination and the
guarded-confluence / SafeStep results for confluence. Sufficiency is not claimed and
does not hold in general; that gap is a real fact, not a missing proof.

No `sorry`, no new `axiom`, no `native_decide`, no `@[csimp]`; the public theorems
are spot-checked with `#print axioms` (baseline whitelist or fewer).
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

namespace OperatorKO7.Meta.SafeStep.NonlinearityDichotomy

/-- The metavariables of the two KO7 rule schemas. -/
inductive RVar | b | s | n | a
  deriving DecidableEq, Repr

/-- Rule-schema terms over the seven KO7 constructors with metavariables. -/
inductive RTerm
  | var : RVar → RTerm
  | void : RTerm
  | delta : RTerm → RTerm
  | integrate : RTerm → RTerm
  | merge : RTerm → RTerm → RTerm
  | app : RTerm → RTerm → RTerm
  | recd : RTerm → RTerm → RTerm → RTerm
  | eqw : RTerm → RTerm → RTerm
  deriving DecidableEq, Repr

/-- Number of occurrences of a metavariable in a rule-schema term. -/
def occ (v : RVar) : RTerm → Nat
  | .var w => if w = v then 1 else 0
  | .void => 0
  | .delta t => occ v t
  | .integrate t => occ v t
  | .merge p q => occ v p + occ v q
  | .app p q => occ v p + occ v q
  | .recd p q r => occ v p + occ v q + occ v r
  | .eqw p q => occ v p + occ v q

/-- LHS of the reflexive equality rule, `eqW a a`. -/
def eqwReflLhs : RTerm := .eqw (.var .a) (.var .a)
/-- LHS of the successor recursor rule, `recΔ b s (delta n)`. -/
def recdSuccLhs : RTerm := .recd (.var .b) (.var .s) (.delta (.var .n))
/-- RHS of the successor recursor rule, `app s (recΔ b s n)`. -/
def recdSuccRhs : RTerm := .app (.var .s) (.recd (.var .b) (.var .s) (.var .n))

/-- A rule left-hand side is left-non-linear when some metavariable occurs at least
twice (an embedded equality test in the matcher). -/
def LeftNonlinear (lhs : RTerm) : Prop := ∃ v : RVar, 2 ≤ occ v lhs

/-- A rule is right-duplicating when some metavariable occurs strictly more often on
the right-hand side than on the left-hand side. -/
def RightDuplicating (lhs rhs : RTerm) : Prop := ∃ v : RVar, occ v lhs < occ v rhs

/-- The confluence-side rule is left-non-linear: `a` occurs twice in `eqW a a`. -/
theorem eqwRefl_leftNonlinear : LeftNonlinear eqwReflLhs := ⟨.a, by decide⟩

/-- The termination-side rule is right-duplicating: `s` occurs once on the left and
twice on the right of `recΔ b s (delta n) → app s (recΔ b s n)`. -/
theorem recdSucc_rightDuplicating : RightDuplicating recdSuccLhs recdSuccRhs :=
  ⟨.s, by decide⟩

/-- The dichotomy made uniform: the same double-occurrence predicate fires, on the
left-hand side for the confluence boundary and on the right-hand side for the
termination boundary. -/
theorem nonlinearity_dichotomy :
    (∃ v : RVar, 2 ≤ occ v eqwReflLhs) ∧ (∃ v : RVar, 2 ≤ occ v recdSuccRhs) :=
  ⟨⟨.a, by decide⟩, ⟨.s, by decide⟩⟩

/-- The two boundary source rules are dual instances of non-linear variable
occurrence: the confluence rule is left-non-linear and the termination rule is
right-duplicating, by the same repeated-variable mechanism on opposite sides. -/
theorem boundary_rules_dual_nonlinear :
    LeftNonlinear eqwReflLhs ∧ RightDuplicating recdSuccLhs recdSuccRhs :=
  ⟨eqwRefl_leftNonlinear, recdSucc_rightDuplicating⟩

/-- The raw-mechanism correspondence as a single object: the confluence and
termination boundaries arise from the dual non-linearity of their source rules, and
the confluence side carries the actual unjoinable fork it produces. Sufficiency is
deliberately absent: this records the shared structural source, not a causal law. -/
structure RawMechanismCorrespondence : Prop where
  confluence_rule_left_nonlinear : LeftNonlinear eqwReflLhs
  termination_rule_right_duplicating : RightDuplicating recdSuccLhs recdSuccRhs
  confluence_fork :
    CriticalPairAt (eqW void void) void (integrate (merge void void))

/-- The KO7 instance of the raw-mechanism correspondence. This is the theorem that
replaces the former analogy: both boundary source rules are dual-non-linear, and the
confluence rule's non-linearity yields the named unjoinable fork. -/
theorem ko7_raw_mechanism_correspondence : RawMechanismCorrespondence where
  confluence_rule_left_nonlinear := eqwRefl_leftNonlinear
  termination_rule_right_duplicating := recdSucc_rightDuplicating
  confluence_fork := local_confluence_fails_at_eqW_void_void

#print axioms eqwRefl_leftNonlinear
#print axioms recdSucc_rightDuplicating
#print axioms nonlinearity_dichotomy
#print axioms boundary_rules_dual_nonlinear
#print axioms ko7_raw_mechanism_correspondence

end OperatorKO7.Meta.SafeStep.NonlinearityDichotomy
