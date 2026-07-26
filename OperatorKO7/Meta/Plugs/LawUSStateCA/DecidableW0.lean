import OperatorKO7.Meta.Plugs.LawUSStateCA.RoutesExact
import OperatorKO7.Meta.Plugs.LawUSStateCA.DTCFaithfulness
import OperatorKO7.Meta.Universal.ClassifyUniversal

/-!
# LawUSStateCA decidable W0 classifier

This module defines twelve labeled cases, assigns each case a one-row finite
information matrix, and proves by constructor case analysis that the universal
classifier returns the explicitly stated result. The carrier is a declared
finite test surface; the file does not establish that it exhausts statutory
construction canons or their legal semantics.
-/

namespace OperatorKO7.Meta.Plugs.LawUSStateCA.DecidableW0

open OperatorKO7.Meta.Plugs.LawUSStateCA
open OperatorKO7.Meta.Universal.ClassifyUniversal

/-- Twelve labels used by this finite W0 classifier instance. -/
inductive LawUSStateCAW0Carrier
  | PlainMeaningCanonCase
  | ExpressioUniusCanonCase
  | NosciturASociisCanonCase
  | EjusdemGenerisCanonCase
  | ReddendoSingulaSingulisCanonCase
  | ConstitutionalAvoidanceCanonCase
  | RuleOfLenityCanonCase
  | LastAntecedentCanonCase
  | SeriesQualifierExceptionCanonCase
  | HarmoniousReadingCanonCase
  | SurplusageCanonCase
  | LegislativeHistoryCanonCase
  deriving DecidableEq, Repr

/-- The per-plug W0 carrier is finite and constructor-discrete. -/
instance : DecidableEq LawUSStateCAW0Carrier := inferInstance

/-- One-row finite-information matrices assigned to the twelve carrier values.
The strings are data tokens; no legal interpretation of them is proved here. -/
def lawUSStateCAW0Matrix : LawUSStateCAW0Carrier → FiniteInformationMatrix
  | .PlainMeaningCanonCase =>
      { rows := [("plain_meaning", ["plain_meaning_rule"])] }
  | .ExpressioUniusCanonCase =>
      { rows := [("expressio_unius", ["expressio_unius_rule"])] }
  | .NosciturASociisCanonCase =>
      { rows := [("noscitur_a_sociis", ["noscitur_a_sociis_rule"])] }
  | .EjusdemGenerisCanonCase =>
      { rows := [("ejusdem_generis", ["ejusdem_generis_rule"])] }
  | .ReddendoSingulaSingulisCanonCase =>
      { rows := [("reddendo_singula_singulis", ["reddendo_singula_singulis_rule"])] }
  | .ConstitutionalAvoidanceCanonCase =>
      { rows := [("constitutional_avoidance", ["constitutional_avoidance_rule"])] }
  | .RuleOfLenityCanonCase =>
      { rows := [("rule_of_lenity", ["rule_of_lenity_rule"])] }
  | .LastAntecedentCanonCase =>
      { rows := [("last_antecedent", ["last_antecedent_rule"])] }
  | .SeriesQualifierExceptionCanonCase =>
      { rows := [("series_qualifier_exception", ["series_qualifier_exception_rule"])] }
  | .HarmoniousReadingCanonCase =>
      { rows := [("harmonious_reading", ["harmonious_reading_rule"])] }
  | .SurplusageCanonCase =>
      { rows := [("surplusage", ["surplusage_rule"])] }
  | .LegislativeHistoryCanonCase =>
      { rows := [("legislative_history", ["legislative_history_rule"])] }

/-- The per-plug W0 classifier specializes the universal finite-information
matrix scan to the LawUSStateCA twelve-canon carrier. -/
def lawUSStateCAW0Classifier : LawUSStateCAW0Carrier → ClassificationResult
  | c => classifyUniversal (lawUSStateCAW0Matrix c)

/-- Explicit comparison result for each of the twelve carrier values. -/
def lawUSStateCAExpectedW0Result : LawUSStateCAW0Carrier → ClassificationResult
  | .PlainMeaningCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "plain_meaning"
             rules := ["plain_meaning_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .ExpressioUniusCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "expressio_unius"
             rules := ["expressio_unius_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .NosciturASociisCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "noscitur_a_sociis"
             rules := ["noscitur_a_sociis_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .EjusdemGenerisCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "ejusdem_generis"
             rules := ["ejusdem_generis_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .ReddendoSingulaSingulisCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "reddendo_singula_singulis"
             rules := ["reddendo_singula_singulis_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .ConstitutionalAvoidanceCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "constitutional_avoidance"
             rules := ["constitutional_avoidance_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .RuleOfLenityCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "rule_of_lenity"
             rules := ["rule_of_lenity_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .LastAntecedentCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "last_antecedent"
             rules := ["last_antecedent_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .SeriesQualifierExceptionCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "series_qualifier_exception"
             rules := ["series_qualifier_exception_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .HarmoniousReadingCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "harmonious_reading"
             rules := ["harmonious_reading_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .SurplusageCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "surplusage"
             rules := ["surplusage_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .LegislativeHistoryCanonCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "legislative_history"
             rules := ["legislative_history_rule"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }

/-- Decidability of the per-plug W0 classifier against its concrete expected
classification result, derived by finite carrier case analysis. -/
instance lawUSStateCAW0Decidable :
    (c : LawUSStateCAW0Carrier) →
      Decidable (lawUSStateCAW0Classifier c = lawUSStateCAExpectedW0Result c)
  | .PlainMeaningCanonCase => isTrue rfl
  | .ExpressioUniusCanonCase => isTrue rfl
  | .NosciturASociisCanonCase => isTrue rfl
  | .EjusdemGenerisCanonCase => isTrue rfl
  | .ReddendoSingulaSingulisCanonCase => isTrue rfl
  | .ConstitutionalAvoidanceCanonCase => isTrue rfl
  | .RuleOfLenityCanonCase => isTrue rfl
  | .LastAntecedentCanonCase => isTrue rfl
  | .SeriesQualifierExceptionCanonCase => isTrue rfl
  | .HarmoniousReadingCanonCase => isTrue rfl
  | .SurplusageCanonCase => isTrue rfl
  | .LegislativeHistoryCanonCase => isTrue rfl

/-- The classifier agrees with the explicit comparison result on all twelve
constructors of `LawUSStateCAW0Carrier`. -/
theorem legalStatuteTwelveCanonCases :
    lawUSStateCAW0Classifier .PlainMeaningCanonCase =
      lawUSStateCAExpectedW0Result .PlainMeaningCanonCase ∧
    lawUSStateCAW0Classifier .ExpressioUniusCanonCase =
      lawUSStateCAExpectedW0Result .ExpressioUniusCanonCase ∧
    lawUSStateCAW0Classifier .NosciturASociisCanonCase =
      lawUSStateCAExpectedW0Result .NosciturASociisCanonCase ∧
    lawUSStateCAW0Classifier .EjusdemGenerisCanonCase =
      lawUSStateCAExpectedW0Result .EjusdemGenerisCanonCase ∧
    lawUSStateCAW0Classifier .ReddendoSingulaSingulisCanonCase =
      lawUSStateCAExpectedW0Result .ReddendoSingulaSingulisCanonCase ∧
    lawUSStateCAW0Classifier .ConstitutionalAvoidanceCanonCase =
      lawUSStateCAExpectedW0Result .ConstitutionalAvoidanceCanonCase ∧
    lawUSStateCAW0Classifier .RuleOfLenityCanonCase =
      lawUSStateCAExpectedW0Result .RuleOfLenityCanonCase ∧
    lawUSStateCAW0Classifier .LastAntecedentCanonCase =
      lawUSStateCAExpectedW0Result .LastAntecedentCanonCase ∧
    lawUSStateCAW0Classifier .SeriesQualifierExceptionCanonCase =
      lawUSStateCAExpectedW0Result .SeriesQualifierExceptionCanonCase ∧
    lawUSStateCAW0Classifier .HarmoniousReadingCanonCase =
      lawUSStateCAExpectedW0Result .HarmoniousReadingCanonCase ∧
    lawUSStateCAW0Classifier .SurplusageCanonCase =
      lawUSStateCAExpectedW0Result .SurplusageCanonCase ∧
    lawUSStateCAW0Classifier .LegislativeHistoryCanonCase =
      lawUSStateCAExpectedW0Result .LegislativeHistoryCanonCase := by
  decide

/-- Decidability and pointwise agreement of the classifier with the explicit
comparison result on `LawUSStateCAW0Carrier`. The existential in the first
conjunct records a decision procedure and has the trivial proposition `True` as
its remaining component. -/
theorem legalStatuteDecidableW0 :
    (∀ c : LawUSStateCAW0Carrier,
      ∃ _ : Decidable (lawUSStateCAW0Classifier c = lawUSStateCAExpectedW0Result c), True) ∧
    (∀ c : LawUSStateCAW0Carrier,
      lawUSStateCAW0Classifier c = lawUSStateCAExpectedW0Result c) := by
  constructor
  · intro c
    exact ⟨lawUSStateCAW0Decidable c, trivial⟩
  · intro c
    cases c <;> rfl

/-- Stable declaration-name string for `legalStatuteDecidableW0`. -/
def legal_statute_decidable_w0_anchor : String :=
  "OperatorKO7.Meta.Plugs.LawUSStateCA.DecidableW0.legalStatuteDecidableW0"

/-- Stable declaration-name string for `legalStatuteTwelveCanonCases`. -/
def legal_statute_twelve_canon_anchor : String :=
  "OperatorKO7.Meta.Plugs.LawUSStateCA.DecidableW0.legalStatuteTwelveCanonCases"

end OperatorKO7.Meta.Plugs.LawUSStateCA.DecidableW0
