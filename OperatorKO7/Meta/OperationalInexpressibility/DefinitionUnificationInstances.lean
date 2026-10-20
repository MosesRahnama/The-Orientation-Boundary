import OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification
import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarLicense
import OperatorKO7.Meta.OperationalInexpressibility.KO7FixedInputLanguage
import OperatorKO7.Meta.OperationalInexpressibility.KO7StepArgumentInstance

/-!
# Instances of the unified definition

Every fixed-input language boundary is a sound observed language whose stored counterfactual pair
witnesses the observer level of the definition; the language level follows, and it coincides by
definition with the schema-level operational incompleteness of the boundary's question. The KO7
fixed-input language is an instance.

The canonical direct-grammar instance at the step-argument dimension has the license form: a
grammar expression depends on the dimension exactly when the counter observer does not license its
denotation, so operational incompleteness of the canonical question says that the dimension is
present and every derivable orienting expression is licensed by the counter observer. Both
conjuncts hold, which gives a second proof of the canonical instance through the license
criterion.

Relation: observer fibers of the boundary; the counter observer on `Nat × Nat`.
Property: instances of the language and observer levels of the definition.
Trust: kernel only.
Scope: every fixed-input boundary; the reflected direct grammar.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.FixedInputLanguage
open OperatorKO7.Meta.OperationalInexpressibility.KO7FixedInputLanguage
open OperatorKO7.Meta.OperationalInexpressibility.KO7StepArgumentInstance
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-! ## Fixed-input boundaries -/

/-- The observed language of a fixed-input boundary, without its stored witness pair. -/
def ObservedLanguage.ofFixedInputBoundary (B : FixedInputLanguageBoundary) : ObservedLanguage where
  World := B.World
  Statement := B.Statement
  Observation := B.Observation
  Dimension := B.Dimension
  Verdict := B.Verdict
  denotes := B.denotes
  derivable := B.derivable
  observe := B.observe
  dimension := B.dimension
  target := B.target
  sameContext := B.sameContext

/-- A fixed-input boundary is sound for its observer. -/
theorem ofFixedInputBoundary_sound (B : FixedInputLanguageBoundary) :
    (ObservedLanguage.ofFixedInputBoundary B).Sound :=
  fun _ hψ => derivable_denotation_factorsThrough B hψ

/-- The stored counterfactual pair witnesses the observer level of the definition. -/
theorem ofFixedInputBoundary_observerInexpressible (B : FixedInputLanguageBoundary) :
    (ObservedLanguage.ofFixedInputBoundary B).ObserverInexpressible :=
  ⟨⟨B.w1, B.w2, B.context_eq, B.dimension_ne⟩,
    ⟨B.w1, B.w2, B.context_eq, B.observation_eq, B.target_ne⟩⟩

/-- Every fixed-input boundary satisfies the language level of the definition. -/
theorem ofFixedInputBoundary_languageInexpressible (B : FixedInputLanguageBoundary) :
    (ObservedLanguage.ofFixedInputBoundary B).LanguageInexpressible :=
  ObservedLanguage.languageInexpressible_of_observerInexpressible
    (ofFixedInputBoundary_sound B) (ofFixedInputBoundary_observerInexpressible B)

/-- The language level of the definition is the schema-level operational incompleteness of the
boundary's question. -/
theorem ofFixedInputBoundary_languageInexpressible_iff_operationallyIncomplete
    (B : FixedInputLanguageBoundary) :
    (ObservedLanguage.ofFixedInputBoundary B).LanguageInexpressible ↔
      OperationallyIncomplete (operationalQuestion B) :=
  Iff.rfl

/-- The KO7 fixed-input language satisfies the observer level of the definition. -/
theorem ko7FixedInput_observerInexpressible :
    (ObservedLanguage.ofFixedInputBoundary ko7FixedInputBoundary).ObserverInexpressible :=
  ofFixedInputBoundary_observerInexpressible ko7FixedInputBoundary

/-- The KO7 fixed-input language satisfies the language level of the definition. -/
theorem ko7FixedInput_languageInexpressible :
    (ObservedLanguage.ofFixedInputBoundary ko7FixedInputBoundary).LanguageInexpressible :=
  ofFixedInputBoundary_languageInexpressible ko7FixedInputBoundary

/-! ## The canonical grammar instance in license form -/

/-- The dimension predicate of the canonical instance is failure of the counter license. -/
theorem ko7StepArgument_dependsOnDimension_iff_unlicensed (e : MeasureExpr) :
    ko7StepArgumentQuestion.dependsOnDimension e ↔
      ¬ Licensed (Prod.fst : Nat × Nat → Nat) (evalOnCarrier e) :=
  usesPayload_iff_unlicensed_by_counter e

/-- **License form of the canonical instance.** Operational incompleteness of the canonical
question is dimension presence together with the counter license of every derivable orienting
grammar expression. -/
theorem ko7StepArgument_operationallyIncomplete_iff_license_face :
    OperationallyIncomplete ko7StepArgumentQuestion ↔
      StepArgumentDimensionPresent ∧
        ∀ e, DirectGrammarDerivable e → GloballyOrientsFixedDuplicatingCarrier e →
          Licensed (Prod.fst : Nat × Nat → Nat) (evalOnCarrier e) := by
  unfold OperationallyIncomplete
  exact and_congr Iff.rfl
    (noIncorporation_iff_constraining_licensed_by_forgetful
      ko7StepArgumentQuestion.derivable ko7StepArgumentQuestion.dependsOnDimension
      ko7StepArgumentQuestion.constrainsTarget evalOnCarrier Prod.fst
      ko7StepArgument_dependsOnDimension_iff_unlicensed)

/-- Every derivable orienting grammar expression is licensed by the counter observer. -/
theorem ko7StepArgument_license_face_holds :
    ∀ e, DirectGrammarDerivable e → GloballyOrientsFixedDuplicatingCarrier e →
      Licensed (Prod.fst : Nat × Nat → Nat) (evalOnCarrier e) := by
  intro e _ hglobal
  exact directGrammar_orienting_denotations_licensed_by_counter e
    ((globallyOrientsFixedDuplicatingCarrier_iff_adequateForDupOrientation e).1 hglobal)

/-- The canonical instance, proved through the license criterion. -/
theorem ko7StepArgument_operationallyIncomplete_via_license :
    OperationallyIncomplete ko7StepArgumentQuestion :=
  ko7StepArgument_operationallyIncomplete_iff_license_face.2
    ⟨ko7StepArgument_dimensionPresent, ko7StepArgument_license_face_holds⟩

end OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification
