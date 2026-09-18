import OperatorKO7.Meta.UniqueNormalization.HubSplitConditions

/-!
# RTA #79 route R2: the generic hub linearization `linHub`

The four preceding hub modules prove the per-rule invariants separately: the
split left-hand side collapses back to the original one, it is left-linear, every
generated condition is a valid hub pair, every split variable is fixed by the
collapse or carries its own hub condition, and the right-hand side survives the
collapse verbatim. This module assembles them.

`hubCRule` is the conditional rule produced from one unconditional rule, and
`linHub` maps it across a whole system. `isMethodLinearization_linHub` proves the
result is a conditional linearization in the named-method sense of
`Linearization.lean`, that is with a left-linear conditional left-hand side, and
`isLinearization_linHub` forgets that to the transfer specification the UN=
proof consumes.

The crown composes `linHub` with the mechanized decreasing-diagrams pipeline:
for an arbitrary term rewriting system over `Nat` variables, local decreasingness
of the canonical minimal-conditional-level labelling of `linHub R` gives UN= and
UN-> of `R`. No hand-built linearization appears anywhere in that statement.

Relation: `CStep` of the conditional system against `Step` of the original.
Closure: reflexive-transitive, through the existing transfer theorems.
Strategy: full rewriting; no strategy annotation is introduced.
Trust: kernel checked. No `sorry`, `axiom`, `native_decide`, `partial`, `unsafe`
or external certificate. Axiom footprints are reported at the end of the file.
Scope: variables are `Nat`, which is where the fresh-name segment lives; the
signature `sigma` is arbitrary.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u

variable {sigma : Type u}

/-! ## The rule transform -/

/-- Splitting preserves application shape, so the transformed left-hand side is
still a legal rule left-hand side. -/
theorem hubSplitTerm_isApp (base : Nat) {t : Term sigma Nat}
    (h : t.isApp = true) : (hubSplitTerm base t).isApp = true := by
  cases t with
  | var x => simp at h
  | app f args => rfl

/-- Every left-hand-side occurrence of a rule lies below that rule's fresh base.
This is the `AllBelowNat` form consumed by the hub invariants. -/
theorem rule_lhs_allBelowNat (rule : Rule sigma Nat) :
    AllBelowNat (ruleFreshBase rule) (Term.varOccurrences rule.lhs) :=
  fun _ hx => lhs_occ_lt_ruleFreshBase hx

/-- **The hub linearization of one rule.** The left-hand side is the occurrence
split, the right-hand side is the original one verbatim, and the conditions are
exactly the emitted hub equalities. -/
def hubCRule (rule : Rule sigma Nat) : CRule sigma Nat where
  lhs := hubSplitTerm (ruleFreshBase rule) rule.lhs
  rhs := rule.rhs
  conds := hubSplitConditions (ruleFreshBase rule) rule.lhs
  lhs_isApp := hubSplitTerm_isApp _ rule.lhs_isApp

@[simp] theorem hubCRule_lhs (rule : Rule sigma Nat) :
    (hubCRule rule).lhs = hubSplitTerm (ruleFreshBase rule) rule.lhs := rfl

@[simp] theorem hubCRule_rhs (rule : Rule sigma Nat) :
    (hubCRule rule).rhs = rule.rhs := rfl

@[simp] theorem hubCRule_conds (rule : Rule sigma Nat) :
    (hubCRule rule).conds = hubSplitConditions (ruleFreshBase rule) rule.lhs := rfl

/-- **The hub linearization of a system.** -/
def linHub (R : TRS sigma Nat) : CTRS sigma Nat :=
  R.map hubCRule

@[simp] theorem linHub_length (R : TRS sigma Nat) :
    (linHub R).length = R.length := List.length_map ..

/-! ## The five clauses of `LinearizesRule` -/

/-- **The hub transform meets the transfer specification, rule by rule.** The
collapse map is `hubCollapse (ruleFreshBase rule)`. -/
theorem hubCRule_linearizesRule (rule : Rule sigma Nat) :
    LinearizesRule rule (hubCRule rule) := by
  refine ⟨rfl, hubCollapse (ruleFreshBase rule), ?_, ?_, ?_, ?_⟩
  · -- the split left-hand side collapses back to the original one
    exact hubSplitRuleLhs_collapse rule
  · -- every generated condition is a hub pair of occurring variables
    intro p hp
    obtain ⟨x, y, hp1, hp2, hxOcc, hyOcc, hyx, hxx⟩ :=
      hubSplitConditions_valid (ruleFreshBase rule) rule.lhs
        (rule_lhs_allBelowNat rule) p hp
    exact ⟨x, y, Prod.ext hp1 hp2, hxx, hyx, hxOcc, hyOcc⟩
  · -- every split variable is fixed by the collapse or has its hub pair listed
    intro v hv
    exact hubSplitTerm_fixed_or_cond (ruleFreshBase rule) rule.lhs
      (rule_lhs_allBelowNat rule) hv
  · -- the collapse fixes the verbatim right-hand side
    intro v hv
    exact hubCollapse_rhs_occ hv.mem_varOccurrences

/-- **The hub transform is the named conditional-linearization method.** Beyond
the transfer specification it delivers the method's defining property: the
conditional left-hand side is left-linear. -/
theorem hubCRule_methodLinearizesRule (rule : Rule sigma Nat) :
    MethodLinearizesRule rule (hubCRule rule) :=
  ⟨hubCRule_linearizesRule rule, hubSplitRuleLhs_leftLinear rule⟩

/-- **`linHub R` is a method-faithful conditional linearization of `R`.**

Relation: rule-by-rule correspondence in both directions.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel checked.
Scope: arbitrary signature, `Nat` variables, arbitrary finite rule list. -/
theorem isMethodLinearization_linHub (R : TRS sigma Nat) :
    IsMethodLinearization R (linHub R) := by
  constructor
  · intro crule hc
    obtain ⟨rule, hr, hEq⟩ := List.mem_map.mp hc
    subst hEq
    exact ⟨rule, hr, hubCRule_methodLinearizesRule rule⟩
  · intro rule hr
    exact ⟨hubCRule rule, List.mem_map_of_mem hr,
      hubCRule_methodLinearizesRule rule⟩

/-- `linHub R` satisfies the transfer specification consumed by the UN= proof. -/
theorem isLinearization_linHub (R : TRS sigma Nat) :
    IsLinearization R (linHub R) :=
  (isMethodLinearization_linHub R).toIsLinearization

/-! ## Crown: a generic route-R2 UN= criterion -/

/-- **Generic UN= criterion.** For an arbitrary term rewriting system over `Nat`
variables, any valid stepwise labelling of its canonical hub linearization that
is locally decreasing in the route-R2 label order gives UN= of the original
system.

Relation: `Step` of `R`, through `CStep` of `linHub R`.
Closure: reflexive-transitive conversion.
Strategy: full rewriting.
Trust: kernel checked.
Scope: `Nat` variables; the labelling is an input, not a construction. -/
theorem UNconv_of_linHub_localDecreasing {R : TRS sigma Nat}
    {step : LabelledStep (Term sigma Nat) LevelLabel}
    (href : ConditionalLabelRefinement (linHub R) step)
    (hdec : AllLocalPeaksDecreasing step LevelLabelLt) : UNconv R :=
  UNconv_of_linearization_localDecreasing (isLinearization_linHub R) href hdec

/-- The same criterion for UN->. -/
theorem UNred_of_linHub_localDecreasing {R : TRS sigma Nat}
    {step : LabelledStep (Term sigma Nat) LevelLabel}
    (href : ConditionalLabelRefinement (linHub R) step)
    (hdec : AllLocalPeaksDecreasing step LevelLabelLt) : UNred R :=
  UNred_of_linearization_localDecreasing (isLinearization_linHub R) href hdec

/-- **Fully canonical form.** Nothing is supplied by hand: the linearization is
`linHub R` and the labelling is the intrinsic minimal conditional level. Local
decreasingness of that one relation is the entire hypothesis. -/
theorem UNconv_of_linHub_minimalLevel_localDecreasing {R : TRS sigma Nat}
    (hdec : AllLocalPeaksDecreasing
      (minimalLevelStep (linHub R)) LevelLabelLt) : UNconv R :=
  UNconv_of_linHub_localDecreasing (minimalLevelStep_refinement (linHub R)) hdec

/-- Fully canonical form for UN->. -/
theorem UNred_of_linHub_minimalLevel_localDecreasing {R : TRS sigma Nat}
    (hdec : AllLocalPeaksDecreasing
      (minimalLevelStep (linHub R)) LevelLabelLt) : UNred R :=
  UNred_of_linHub_localDecreasing (minimalLevelStep_refinement (linHub R)) hdec

/-! ## Non-vacuity

Two witnesses at the exact quantified domain of the theorems above: a rule whose
left-hand side is already linear, where the transform adds nothing, and the
nonlinear diagonal rule, where it genuinely splits an occurrence and emits the
equality condition. -/

/-- A left-linear rule acquires no conditions, so the transform does not change
what the rule tests. -/
theorem hubCRule_conds_eq_nil_of_leftLinear (rule : Rule sigma Nat)
    (hlin : Term.LeftLinear rule.lhs) : (hubCRule rule).conds = [] :=
  hubSplitConditions_eq_nil_of_leftLinear (ruleFreshBase rule) rule.lhs hlin

/-- The diagonal rule reserves the fresh segment above `0`. -/
theorem ruleFreshBase_diagRule : ruleFreshBase CondExample.diagRule = 1 := by
  simp [ruleFreshBase, CondExample.diagRule, maxNatList, Term.varOccurrences]

/-- On the nonlinear diagonal rule `f(x, x) -> a` the transform splits the second
occurrence to the fresh code `2` and keeps the right-hand side. The hub splitter
is a mutual structural recursion, so these fixtures are discharged through its
equation lemmas rather than by definitional reduction. -/
theorem hubCRule_diagRule_lhs :
    (hubCRule CondExample.diagRule).lhs
      = Term.app 2 [Term.var 0, Term.var 2] := by
  rw [hubCRule_lhs, ruleFreshBase_diagRule]
  simp [CondExample.diagRule, hubSplitTerm, hubSplitTermAux, hubSplitListAux,
    hubFresh, Nat.pair]

/-- The same instance emits exactly the one hub condition `x = y`. -/
theorem hubCRule_diagRule_conds :
    (hubCRule CondExample.diagRule).conds
      = [(Term.var 0, Term.var 2)] := by
  rw [hubCRule_conds, ruleFreshBase_diagRule]
  simp [CondExample.diagRule, hubSplitConditions, hubSplitTermAux, hubSplitListAux,
    hubFresh, Nat.pair]

/-- The right-hand side is kept verbatim, which is the campaign's named error
class for this transform. -/
theorem hubCRule_diagRule_rhs :
    (hubCRule CondExample.diagRule).rhs = CondExample.diagRule.rhs := rfl

/-- The transform is not degenerate on a nonlinear rule: it really emits a
condition, so `hubCRule` is not the trivial self-linearization there. -/
theorem hubCRule_diagRule_conds_ne_nil :
    (hubCRule CondExample.diagRule).conds ≠ [] := by
  rw [hubCRule_diagRule_conds]
  simp

/-- The split diagonal left-hand side is left-linear, which the original is not. -/
theorem hubCRule_diagRule_leftLinear :
    Term.LeftLinear (hubCRule CondExample.diagRule).lhs :=
  hubSplitRuleLhs_leftLinear CondExample.diagRule

/-- The original diagonal left-hand side is not left-linear, so the previous
theorem records a genuine change. -/
theorem diagRule_lhs_not_leftLinear :
    ¬ Term.LeftLinear CondExample.diagRule.lhs := by
  simp [Term.LeftLinear, CondExample.diagRule, Term.varOccurrences]

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_isApp
#check @OperatorKO7.Meta.UniqueNormalization.rule_lhs_allBelowNat
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_lhs
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_rhs
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_conds
#check @OperatorKO7.Meta.UniqueNormalization.linHub
#check @OperatorKO7.Meta.UniqueNormalization.linHub_length
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_linearizesRule
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_methodLinearizesRule
#check @OperatorKO7.Meta.UniqueNormalization.isMethodLinearization_linHub
#check @OperatorKO7.Meta.UniqueNormalization.isLinearization_linHub
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_localDecreasing
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_linHub_localDecreasing
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_minimalLevel_localDecreasing
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_linHub_minimalLevel_localDecreasing
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_conds_eq_nil_of_leftLinear
#check @OperatorKO7.Meta.UniqueNormalization.ruleFreshBase_diagRule
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_lhs
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_conds
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_rhs
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_conds_ne_nil
#check @OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_leftLinear
#check @OperatorKO7.Meta.UniqueNormalization.diagRule_lhs_not_leftLinear

#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_isApp
#print axioms OperatorKO7.Meta.UniqueNormalization.rule_lhs_allBelowNat
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_lhs
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_rhs
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_conds
#print axioms OperatorKO7.Meta.UniqueNormalization.linHub
#print axioms OperatorKO7.Meta.UniqueNormalization.linHub_length
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_linearizesRule
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_methodLinearizesRule
#print axioms OperatorKO7.Meta.UniqueNormalization.isMethodLinearization_linHub
#print axioms OperatorKO7.Meta.UniqueNormalization.isLinearization_linHub
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_linHub_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_linHub_minimalLevel_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_linHub_minimalLevel_localDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_conds_eq_nil_of_leftLinear
#print axioms OperatorKO7.Meta.UniqueNormalization.ruleFreshBase_diagRule
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_lhs
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_conds
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_rhs
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_conds_ne_nil
#print axioms OperatorKO7.Meta.UniqueNormalization.hubCRule_diagRule_leftLinear
#print axioms OperatorKO7.Meta.UniqueNormalization.diagRule_lhs_not_leftLinear
