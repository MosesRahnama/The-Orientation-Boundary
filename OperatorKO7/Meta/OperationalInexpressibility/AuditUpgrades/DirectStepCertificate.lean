import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder

/-!
# Direct certificates of the duplicating rule

Proves: no expression of the reflected direct grammar that reads the payload decreases, under
the counter and payload profile, across the successor rule of the free recursor alone; the
payload-free counter expression is derivable and decreases across every successor step; the
zero rule leaves both observations unchanged, so no profile measure decreases across it.
Every direct whole-term certificate restricts to a certificate of the successor rule, so the
emptiness of the whole-term class follows from the duplication argument.
Relation: root steps `FreeRecursorStep` of the free recursor.
Closure: root, one step.
Strategy: not applicable.
Trust: kernel-only.
Scope: profile measures `m (counterObservation t) (payloadObservation t)` of grammar expressions.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.DirectStepCertificate

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder

/-- A direct certificate of the duplicating rule: a derivable grammar expression that reads the
payload and decreases, under the profile, across every successor root step. -/
structure DirectDuplicatingStepCertificate where
  expression : MeasureExpr
  formation : DirectGrammarDerivation expression
  usesPayload : UsesPayload expression
  decreasesOnSuccessor : ∀ b s n : RecursorTerm,
    profileMeasure expression.eval (.app s (.recR b s n)) <
      profileMeasure expression.eval (.recR b s (.delta n))

/-- No payload-reading grammar expression decreases across the successor rule alone. -/
theorem freeRecursor_no_directDuplicatingStepCertificate :
    ¬ Nonempty DirectDuplicatingStepCertificate := by
  rintro ⟨w⟩
  exact no_directGrammar_measure_usesPayload_and_orients w.expression
    ⟨w.usesPayload,
      (profile_orients_successors_iff w.expression.eval).mp w.decreasesOnSuccessor⟩

/-- Every direct whole-term certificate restricts to a certificate of the successor rule. -/
def duplicatingStepCertificateOfDirectWhole (w : DirectWholeWitness) :
    DirectDuplicatingStepCertificate where
  expression := w.expression
  formation := w.formation
  usesPayload := w.usesPayload
  decreasesOnSuccessor := fun b s n => w.decreases (.succ b s n)

/-- The whole-term class is empty because its successor restriction is empty. -/
theorem freeRecursor_no_directWhole_of_duplicatingStep : ¬ Nonempty DirectWholeWitness :=
  fun ⟨w⟩ => freeRecursor_no_directDuplicatingStepCertificate
    ⟨duplicatingStepCertificateOfDirectWhole w⟩

/-- The counter expression ignores the payload. -/
theorem counter_not_usesPayload : ¬ UsesPayload MeasureExpr.counter := by
  intro h
  exact h (fun _ _ _ => rfl)

/-- The counter expression decreases by one across every successor root step. -/
theorem counter_decreases_on_every_successor_step (b s n : RecursorTerm) :
    profileMeasure MeasureExpr.counter.eval (.app s (.recR b s n)) <
      profileMeasure MeasureExpr.counter.eval (.recR b s (.delta n)) := by
  have hc := (successor_profile b s n).1
  show counterObservation (.app s (.recR b s n)) < counterObservation (.recR b s (.delta n))
  omega

/-- Non-vacuity control: with the payload-use field removed, the class is inhabited by the
derivable counter expression, so the payload-use field carries the barrier. -/
theorem payloadFree_duplicatingStep_certificate_exists :
    ∃ e : MeasureExpr, Nonempty (DirectGrammarDerivation e) ∧ ¬ UsesPayload e ∧
      ∀ b s n : RecursorTerm,
        profileMeasure e.eval (.app s (.recR b s n)) <
          profileMeasure e.eval (.recR b s (.delta n)) :=
  ⟨MeasureExpr.counter, ⟨DirectGrammarDerivation.counter⟩, counter_not_usesPayload,
    counter_decreases_on_every_successor_step⟩

/-- The zero rule leaves the counter and the payload observation unchanged. -/
theorem profile_zero_rule_eq (m : Nat → Nat → Nat) (b s : RecursorTerm) :
    profileMeasure m (.recR b s .void) = profileMeasure m b := by
  simp only [profileMeasure, counterObservation, payloadObservation, deltaPrefix, Nat.zero_add]

/-- No profile measure decreases across the zero rule. -/
theorem no_profile_measure_decreases_on_zero_rule (m : Nat → Nat → Nat) :
    ¬ ∀ b s : RecursorTerm, profileMeasure m b < profileMeasure m (.recR b s .void) := by
  intro h
  have h0 := h .void .void
  rw [profile_zero_rule_eq] at h0
  exact Nat.lt_irrefl _ h0

end OperatorKO7.Meta.OperationalInexpressibility.AuditUpgrades.DirectStepCertificate
