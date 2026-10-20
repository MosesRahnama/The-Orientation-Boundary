import OperatorKO7.Meta.Methods.OrientationClosure.HypothesisNecessityBase
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsDependencyPairs
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsUsableFormative
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsSubstrate

/-!
# Hypothesis necessity of the dependency-pair, usable/formative, and substrate rows

Thirteen rows of the method universe, each with its necessity kind, its necessity statement on the
row's own laws and acceptance predicate, and the proof of that statement.

Relation: the row's own acceptance predicate for the free duplicating rule.
Property: necessity of one law clause or one data feature, stated by a concrete datum.

Rows whose native data is a list (`dpProcessorClassification`, `sizeChangeTerminationEscape`,
`equationalQuotientNonConservativity`) state the feature change on the one-element position that
the change touches: the laws and acceptance are read on the list built from that element, and the
lens is a field lens on the element.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.HypothesisNecessity

universe v

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics

/-! ## Dependency-pair rows -/

section DependencyPairRows

open OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs

/-- The marked-call coefficients of linear data. -/
def linearMarkedCoeffLens : FeatureLens LinearData (Nat → Nat) where
  get L := L.ma
  set L w := { L with ma := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The zero marked-call coefficients differ from those of the counter interpretation at the
counter position. -/
theorem zeroMarkedCoeff_ne_counterLinear : (fun _ : Nat => (0 : Nat)) ≠ counterLinear.ma :=
  fun h => absurd (congrFun h 2) (by decide)

/-! ### Row: dpSubtermCriterion -/

def dpSubtermCriterionNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Changing the projected position of `recur` keeps the arity law and loses the criterion. -/
def dpSubtermCriterionNecessityStatement : Prop :=
  EscapeFeatureNecessity dpSubtermCriterionLaws dpSubtermCriterionAccepts
    (pointLens (β := Nat) FreeSym.recur)

theorem dpSubtermCriterion_necessity : dpSubtermCriterionNecessityStatement := by
  have hchg : (pointLens (β := Nat) FreeSym.recur).set dpSubtermCriterionWitness 1 =
      payloadProj := by
    funext g
    cases g <;> rfl
  exact ⟨⟨dpSubtermCriterionWitness, dpSubtermCriterionWitness_laws,
    dpSubtermCriterionWitness_result.1, 1, by decide,
    by rw [hchg]; exact dpSubtermCriterion_mutation.1,
    by rw [hchg]; exact dpSubtermCriterion_mutation.2⟩⟩

/-! ### Row: dpReductionPairProcessor -/

def dpReductionPairProcessorNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Zeroing the marked-call coefficients keeps the weak rules and loses the strict pairs. -/
def dpReductionPairProcessorNecessityStatement : Prop :=
  EscapeFeatureNecessity dpReductionPairProcessorLaws dpReductionPairProcessorAccepts
    linearMarkedCoeffLens

theorem dpReductionPairProcessor_necessity : dpReductionPairProcessorNecessityStatement :=
  ⟨⟨dpReductionPairProcessorWitness, dpReductionPairProcessorWitness_laws,
    dpReductionPairProcessorWitness_result.1, fun _ => 0, zeroMarkedCoeff_ne_counterLinear,
    dpReductionPairProcessor_mutation.1.1, dpReductionPairProcessor_mutation.1.2⟩⟩

/-! ### Row: dpReductionTriples -/

def dpReductionTriplesNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Zeroing the marked-call coefficients keeps the weak rules and loses the strict pair edges. -/
def dpReductionTriplesNecessityStatement : Prop :=
  EscapeFeatureNecessity dpReductionTriplesLaws dpReductionTriplesAccepts linearMarkedCoeffLens

theorem dpReductionTriples_necessity : dpReductionTriplesNecessityStatement :=
  ⟨⟨dpReductionTriplesWitness, dpReductionTriplesWitness_laws,
    dpReductionTriplesWitness_result.1, fun _ => 0, zeroMarkedCoeff_ne_counterLinear,
    dpReductionTriples_mutation.1, dpReductionTriples_mutation.2⟩⟩

/-! ### Row: dpArgumentFiltering -/

def dpArgumentFilteringNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- Erasing the counter from the kept positions of `recur` keeps the arity law and loses the
strict pair. -/
def dpArgumentFilteringNecessityStatement : Prop :=
  EscapeFeatureNecessity dpArgumentFilteringLaws dpArgumentFilteringAccepts
    (pointLens (β := List Nat) FreeSym.recur)

theorem dpArgumentFiltering_necessity : dpArgumentFilteringNecessityStatement := by
  have hchg : (pointLens (β := List Nat) FreeSym.recur).set dpArgumentFilteringWitness [0] =
      baseOnlyFilter := by
    funext g
    cases g <;> rfl
  exact ⟨⟨dpArgumentFilteringWitness, dpArgumentFilteringWitness_laws,
    dpArgumentFilteringWitness_accepts, [0], by decide,
    by rw [hchg]; exact dpArgumentFiltering_mutation.2.1,
    by rw [hchg]; exact dpArgumentFiltering_mutation.2.2⟩⟩

/-! ### Row: dpNeutralProcessors -/

def dpNeutralProcessorsNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The neutrality law fixes the output of the processor on the pair problem, so every lawful
processor has the verdict of the identity processor. -/
def dpNeutralProcessorsNecessityStatement : Prop :=
  NoApplicableHypothesis dpNeutralProcessorsLaws dpNeutralProcessorsAccepts .lawsDetermineVerdict

theorem dpNeutralProcessors_necessity : dpNeutralProcessorsNecessityStatement := by
  have hfix : ∀ M : dpNeutralProcessorsData, dpNeutralProcessorsLaws M →
      M (dpPairs freeRecursorTRS) = dpPairs freeRecursorTRS :=
    fun M hM => funext fun c => funext fun d => propext (hM _ c d)
  refine ⟨⟨dpNeutralProcessorsWitness, dpNeutralProcessorsWitness_laws⟩, fun M M' hM hM' => ?_⟩
  show FiniteDP freeRecursorTRS (M (dpPairs freeRecursorTRS)) ↔
    FiniteDP freeRecursorTRS (M' (dpPairs freeRecursorTRS))
  rw [hfix M hM, hfix M' hM']

/-- No feature change of a neutral processor separates acceptance from rejection. -/
theorem dpNeutralProcessors_no_feature_control {V : Sort v}
    (L : FeatureLens dpNeutralProcessorsData V) :
    ¬ EscapeFeatureNecessity dpNeutralProcessorsLaws dpNeutralProcessorsAccepts L :=
  NoApplicableHypothesis.no_feature_control dpNeutralProcessors_necessity L

/-! ### Row: dpProcessorClassification -/

/-- The sequence neutral processor, then the reduction pair of blind linear data, meets its
conditions. -/
theorem blindProcessorSequence_laws :
    dpProcessorClassificationLaws [.neutral, .pair blindLinear] :=
  ⟨trivial, ⟨blindLinear_rulesWeak, fun c d _ => by simp [blindLinear_markedEval]⟩, trivial⟩

/-- The same sequence leaves the dependency pair of the free recursor. -/
theorem blindProcessorSequence_rejects :
    ¬ dpProcessorClassificationAccepts [.neutral, .pair blindLinear] :=
  fun h => h dpSource dpTarget ⟨free_dpPair, by simp [blindLinear_markedEval]⟩

def dpProcessorClassificationNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- In the two-processor sequence of the witness, zeroing the marked-call coefficients of the
reduction-pair processor keeps every processor condition and leaves an edge. -/
def dpProcessorClassificationNecessityStatement : Prop :=
  EscapeFeatureNecessity
    (fun L : LinearData => dpProcessorClassificationLaws [.neutral, .pair L])
    (fun L : LinearData => dpProcessorClassificationAccepts [.neutral, .pair L])
    linearMarkedCoeffLens

theorem dpProcessorClassification_necessity : dpProcessorClassificationNecessityStatement :=
  ⟨⟨counterLinear, dpProcessorClassificationWitness_laws, dpProcessorClassificationWitness_accepts,
    fun _ => 0, zeroMarkedCoeff_ne_counterLinear, blindProcessorSequence_laws,
    blindProcessorSequence_rejects⟩⟩

/-! ### Row: sizeChangeTerminationEscape -/

/-- The right-hand side of a rule. -/
def ruleRhsLens : FeatureLens (Rule FreeSym Nat) (Term FreeSym Nat) where
  get ρ := ρ.rhs
  set ρ w := { ρ with rhs := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The successor rule with its right-hand side replaced by its left-hand side. -/
def sctNonDescendingRule : Rule FreeSym Nat := ruleRhsLens.set succRule succRule.lhs

/-- A ground instance of the left-hand side of the successor rule. -/
def sctLoopTerm : Term FreeSym Nat :=
  .app .recur [.app .zero [], .app .zero [], .app .succ [.app .zero []]]

theorem sctNonDescending_laws : sizeChangeTerminationEscapeLaws [zeroRule, sctNonDescendingRule] := by
  intro rule hrule
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · exact freeRecursorTRS_vars _ List.mem_cons_self
  · exact Finset.Subset.refl _

theorem sctLoop_step :
    OperatorKO7.Meta.Rewriting.Step [zeroRule, sctNonDescendingRule] sctLoopTerm sctLoopTerm :=
  .root ⟨sctNonDescendingRule, List.mem_cons_of_mem _ List.mem_cons_self,
    fun _ => .app .zero [], rfl, rfl⟩

theorem sctLoopTerm_not_sn : ¬ SN [zeroRule, sctNonDescendingRule] sctLoopTerm := by
  intro hsn
  have key : ∀ t, SN [zeroRule, sctNonDescendingRule] t →
      ¬ OperatorKO7.Meta.Rewriting.Step [zeroRule, sctNonDescendingRule] t t := by
    intro t ht
    induction ht with
    | intro x _ ih => exact fun hxx => ih x hxx hxx
  exact key _ hsn sctLoop_step

theorem sctNonDescending_rejects :
    ¬ sizeChangeTerminationEscapeAccepts [zeroRule, sctNonDescendingRule] :=
  fun h => sctLoopTerm_not_sn
    (sizeChangeTerminationEscape_sound _ sctNonDescending_laws h sctLoopTerm)

def sizeChangeTerminationEscapeNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- In the free recursor, replacing the right-hand side of the successor rule by its left-hand
side keeps the variable condition and loses the size-change criterion. -/
def sizeChangeTerminationEscapeNecessityStatement : Prop :=
  EscapeFeatureNecessity
    (fun ρ : Rule FreeSym Nat => sizeChangeTerminationEscapeLaws [zeroRule, ρ])
    (fun ρ : Rule FreeSym Nat => sizeChangeTerminationEscapeAccepts [zeroRule, ρ])
    ruleRhsLens

theorem sizeChangeTerminationEscape_necessity : sizeChangeTerminationEscapeNecessityStatement :=
  ⟨⟨succRule, freeRecursorTRS_vars, SizeChangeTermination.freeRecursorTRS_sctCriterion,
    succRule.lhs, fun h => by simp [ruleRhsLens, succRule] at h, sctNonDescending_laws,
    sctNonDescending_rejects⟩⟩

end DependencyPairRows

/-! ## Usable-rules and formative-rules rows -/

section UsableFormativeRows

open OperatorKO7.Methods.OrientationClosure.MethodRowsUsableFormative

/-! ### Row: usableRulesMinimality -/

/-- The dependency-pair problem of the data. -/
def usableRulesProblemLens : FeatureLens usableRulesMinimalityData FProblem where
  get M := M.P
  set M w := { M with P := w }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The looping recursor rule alone, with the empty problem. -/
def usableEmptyProblemData : usableRulesMinimalityData where
  R := [loopRecRule]
  P := fun _ _ => False

theorem loopRecRule_vars : ∀ r ∈ ([loopRecRule] : FTRS), Term.vars r.rhs ⊆ Term.vars r.lhs := by
  intro r hr
  obtain rfl := List.mem_singleton.1 hr
  exact Finset.Subset.refl _

/-- The self-pair of the looping recursor rule. -/
theorem loopRec_dpPair : dpPairs [loopRecRule] usableControlSource usableControlSource :=
  ⟨loopRecRule, List.mem_singleton.2 rfl, Subst.id,
    by simp [usableControlSource, loopRecRule, Subst.id],
    [.var 0, .var 1, .var 2], IsSubterm.refl _,
    ⟨loopRecRule, List.mem_singleton.2 rfl, [.var 0, .var 1, .var 2], rfl⟩,
    by simp [usableControlSource, Subst.id]⟩

theorem loopRec_var_sn (x : Nat) : SN ([loopRecRule] : FTRS) (.var x) :=
  Acc.intro _ fun u h => absurd h (not_step_var _ x u)

def usableRulesMinimalityNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- With the looping recursor rule, replacing the empty problem by the extracted pairs keeps the
laws and makes the usable chain relation loop. -/
def usableRulesMinimalityNecessityStatement : Prop :=
  EscapeFeatureNecessity usableRulesMinimalityLaws usableRulesMinimalityAccepts
    usableRulesProblemLens

theorem usableRulesMinimality_necessity : usableRulesMinimalityNecessityStatement := by
  have hargs : ∀ a ∈ usableControlSource.2, SN ([loopRecRule] : FTRS) a := by
    intro a ha
    simp only [usableControlSource, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact loopRec_var_sn _
  refine ⟨⟨usableEmptyProblemData, ⟨fun h => False.elim h, loopRecRule_vars⟩,
    ⟨usableRules_closed _ _, usableRules_least _ _,
      ⟨fun c => Acc.intro c fun d h => ?_⟩⟩,
    dpPairs [loopRecRule], ?_, ⟨fun h => h, loopRecRule_vars⟩, ?_⟩⟩
  · obtain ⟨-, -, xs, -, hp⟩ := h
    exact False.elim hp
  · intro h
    exact cast (congrFun (congrFun h usableControlSource) usableControlSource) loopRec_dpPair
  · intro hA
    have hc : UsableChainP [loopRecRule] (dpPairs [loopRecRule]) usableControlSource
        usableControlSource :=
      ⟨hargs, hargs, usableControlSource.2, Relation.ReflTransGen.refl, loopRec_dpPair⟩
    exact (hA.2.2.asymmetric _ _ hc) hc

/-! ### Row: formativeRules -/

/-- A lawful selector is accepted: the single pair tag is selected. -/
theorem formativeRules_accepts_of_laws (M : formativeRulesData) (hL : formativeRulesLaws M) :
    formativeRulesAccepts M := by
  refine ⟨formativeRules_closed_of_laws M hL, formativeRules_sufficient_of_laws M hL,
    fun a b => ⟨?_, ?_⟩⟩
  · rintro ⟨tag, -, hfp⟩
    exact OperatorKO7.Methods.DependencyPairTypedRows.formativePair_iff_dppair.mp ⟨tag, hfp⟩
  · intro h
    obtain ⟨tag, hfp⟩ :=
      OperatorKO7.Methods.DependencyPairTypedRows.formativePair_iff_dppair.mpr h
    cases tag
    exact ⟨.recSucc, hL.2, hfp⟩

def formativeRulesNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The laws select the only formative pair tag, so every lawful selector is accepted. -/
def formativeRulesNecessityStatement : Prop :=
  NoApplicableHypothesis formativeRulesLaws formativeRulesAccepts .lawsDetermineVerdict

theorem formativeRules_necessity : formativeRulesNecessityStatement :=
  ⟨⟨formativeRulesWitness, formativeRulesWitness_laws⟩, fun M M' hM hM' =>
    iff_of_true (formativeRules_accepts_of_laws M hM) (formativeRules_accepts_of_laws M' hM')⟩

/-- No feature change of a lawful selector separates acceptance from rejection. -/
theorem formativeRules_no_feature_control {V : Sort v} (L : FeatureLens formativeRulesData V) :
    ¬ EscapeFeatureNecessity formativeRulesLaws formativeRulesAccepts L :=
  NoApplicableHypothesis.no_feature_control formativeRules_necessity L

end UsableFormativeRows

/-! ## Substrate rows -/

section SubstrateRows

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate

/-! ### Row: sharingNonConservativity -/

def sharingNonConservativityNecessityKind : RowNecessityKind := .noApplicableHypothesis

/-- The simulation law gives termination under every lawful policy. -/
def sharingNonConservativityNecessityStatement : Prop :=
  NoApplicableHypothesis sharingNonConservativityLaws sharingNonConservativityAccepts
    .lawsDetermineVerdict

theorem sharingNonConservativity_necessity : sharingNonConservativityNecessityStatement :=
  ⟨⟨sharingNonConservativityWitness, sharingNonConservativityWitness_laws⟩, fun M M' hM hM' =>
    iff_of_true (sharingNonConservativity_universal M hM)
      (sharingNonConservativity_universal M' hM')⟩

/-- No feature change of a lawful policy separates acceptance from rejection. -/
theorem sharingNonConservativity_no_feature_control {V : Sort v}
    (L : FeatureLens sharingNonConservativityData V) :
    ¬ EscapeFeatureNecessity sharingNonConservativityLaws sharingNonConservativityAccepts L :=
  NoApplicableHypothesis.no_feature_control sharingNonConservativity_necessity L

/-! ### Row: equationalQuotientNonConservativity -/

/-- The right-hand side of an equation. -/
def equationRhsLens : FeatureLens (FreeTerm Nat × FreeTerm Nat) (FreeTerm Nat) where
  get e := e.2
  set e w := (e.1, w)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The commutativity equation with its right-hand side replaced by a recursor redex whose base is
the left-hand side. -/
def reabsorbEquations : List (FreeTerm Nat × FreeTerm Nat) :=
  [(.wrap (.var 0) (.var 1), .recur (.wrap (.var 0) (.var 1)) (.var 1) .zero)]

theorem reabsorbEquations_regular : RegularEquations reabsorbEquations := by
  intro p hp x
  simp only [reabsorbEquations, List.mem_singleton] at hp
  subst hp
  simp only [freeVars, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false]
  tauto

theorem reabsorb_modStep : ModStep reabsorbEquations (.wrap .zero .zero) (.wrap .zero .zero) := by
  refine ⟨.recur (.wrap .zero .zero) .zero .zero, .wrap .zero .zero, ?_,
    rootStep_contextStep (.recurZero _ _), Relation.EqvGen.refl _⟩
  apply Relation.EqvGen.rel
  have h := EqStep.lift (E := reabsorbEquations) FreeContext.hole (fun _ => FreeTerm.zero)
    (l := .wrap (.var 0) (.var 1)) (r := .recur (.wrap (.var 0) (.var 1)) (.var 1) .zero)
    (by simp [reabsorbEquations])
  simpa using h

def equationalQuotientNonConservativityNecessityKind : RowNecessityKind := .deletedEscapeFeature

/-- In the one-equation system of commutativity, replacing the right-hand side of the equation
keeps regularity and makes the quotient loop. -/
def equationalQuotientNonConservativityNecessityStatement : Prop :=
  EscapeFeatureNecessity
    (fun e : FreeTerm Nat × FreeTerm Nat => equationalQuotientNonConservativityLaws [e])
    (fun e : FreeTerm Nat × FreeTerm Nat => equationalQuotientNonConservativityAccepts [e])
    equationRhsLens

theorem equationalQuotientNonConservativity_necessity :
    equationalQuotientNonConservativityNecessityStatement :=
  ⟨⟨(.wrap (.var 0) (.var 1), .wrap (.var 1) (.var 0)), commEquations_regular, comm_modStep_wf,
    .recur (.wrap (.var 0) (.var 1)) (.var 1) .zero,
    fun h => by simp [equationRhsLens] at h,
    reabsorbEquations_regular,
    fun h => (h.asymmetric _ _ reabsorb_modStep) reabsorb_modStep⟩⟩

/-! ### Row: stringRewritingInapplicability -/

/-- The deleted clause: the code of `zero` is nonempty. -/
def stringRewritingInapplicabilityDeletedLaw (M : stringRewritingInapplicabilityData) : Prop :=
  1 ≤ M.cz

/-- The retained clauses of compositional length. -/
def stringRewritingInapplicabilityOtherLaws (M : stringRewritingInapplicabilityData) : Prop :=
  (M.enc .zero).length = M.cz ∧
    (∀ t, (M.enc (.succ t)).length = M.cs + (M.enc t).length) ∧
    (∀ s t, (M.enc (.wrap s t)).length = M.cw + (M.enc s).length + (M.enc t).length) ∧
    (∀ b s n, (M.enc (.recur b s n)).length =
      M.cr + (M.enc b).length + (M.enc s).length + (M.enc n).length)

def stringRewritingInapplicabilityNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- Without the nonempty code of `zero`, the empty encoding keeps the other clauses and performs
every duplicating step as one string step. -/
def stringRewritingInapplicabilityNecessityStatement : Prop :=
  BarrierPremiseNecessity stringRewritingInapplicabilityLaws
    stringRewritingInapplicabilityOtherLaws stringRewritingInapplicabilityDeletedLaw
    stringRewritingInapplicabilityAccepts

theorem stringRewritingInapplicability_necessity :
    stringRewritingInapplicabilityNecessityStatement :=
  ⟨fun _ => and_comm, stringRewritingInapplicability_universal,
    ⟨⟨degenerateStringData, ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩,
      (by decide : ¬ (1 : Nat) ≤ 0), stringRewritingInapplicability_mutation.2⟩⟩⟩

/-! ### Row: cycleRewritingInapplicability -/

/-- The deleted clause: the code of `zero` is nonempty. -/
def cycleRewritingInapplicabilityDeletedLaw (M : cycleRewritingInapplicabilityData) : Prop :=
  1 ≤ M.cz

/-- The retained clauses of compositional length. -/
def cycleRewritingInapplicabilityOtherLaws (M : cycleRewritingInapplicabilityData) : Prop :=
  (M.enc .zero).length = M.cz ∧
    (∀ t, (M.enc (.succ t)).length = M.cs + (M.enc t).length) ∧
    (∀ s t, (M.enc (.wrap s t)).length = M.cw + (M.enc s).length + (M.enc t).length) ∧
    (∀ b s n, (M.enc (.recur b s n)).length =
      M.cr + (M.enc b).length + (M.enc s).length + (M.enc n).length)

def cycleRewritingInapplicabilityNecessityKind : RowNecessityKind := .deletedBarrierPremise

/-- Without the nonempty code of `zero`, the empty encoding keeps the other clauses and performs
every duplicating step as one cycle step. -/
def cycleRewritingInapplicabilityNecessityStatement : Prop :=
  BarrierPremiseNecessity cycleRewritingInapplicabilityLaws
    cycleRewritingInapplicabilityOtherLaws cycleRewritingInapplicabilityDeletedLaw
    cycleRewritingInapplicabilityAccepts

theorem cycleRewritingInapplicability_necessity :
    cycleRewritingInapplicabilityNecessityStatement :=
  ⟨fun _ => and_comm, cycleRewritingInapplicability_universal,
    ⟨⟨degenerateStringData, ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩,
      (by decide : ¬ (1 : Nat) ≤ 0), cycleRewritingInapplicability_mutation.2⟩⟩⟩

end SubstrateRows

end OperatorKO7.Methods.OrientationClosure.HypothesisNecessity
