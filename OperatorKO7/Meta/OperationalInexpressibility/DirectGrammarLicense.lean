import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore

/-!
# The direct-grammar boundary as a license instance

The grammar boundary of `DirectGrammarBoundary` says that an orienting expression of the reflected
direct grammar is payload-blind. Payload blindness of a two-coordinate measure is exactly the
license of the counter observer `Prod.fst` on the canonical `(counter, payload)` carrier. So the
grammar boundary is an instance of the license criterion: every orienting grammar denotation is
licensed by the counter observer, and the payload target is not, witnessed by the collision of
`(0, 0)` and `(0, 1)`. Outside the grammar the implication from orientation to the counter license
fails, witnessed by `payloadSensitiveOrienter`.

Relation: equality of the counter coordinate on `Nat × Nat`.
Property: licensing of grammar denotations by the counter observer.
Trust: kernel only.
Scope: every expression of the reflected grammar and every denotational subgrammar of it.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

universe u

/-- Payload blindness of a two-coordinate measure is exactly the license of the counter observer
on the canonical carrier. -/
theorem payloadBlind_iff_licensed_by_counter (m : Nat → Nat → Nat) :
    PayloadBlind m ↔ Licensed (Prod.fst : Nat × Nat → Nat) (fun s => m s.1 s.2) := by
  constructor
  · rintro h ⟨c, p⟩ ⟨c', p'⟩ hcc
    dsimp only at hcc ⊢
    subst hcc
    exact h c p p'
  · intro h c p p'
    exact h (c, p) (c, p') rfl

/-- A grammar expression uses the payload exactly when the counter observer does not license its
denotation. -/
theorem usesPayload_iff_unlicensed_by_counter (e : MeasureExpr) :
    UsesPayload e ↔ ¬ Licensed (Prod.fst : Nat × Nat → Nat) (fun s => e.eval s.1 s.2) :=
  not_congr (payloadBlind_iff_licensed_by_counter e.eval)

/-- **The grammar boundary as a license instance.** Every grammar expression that orients the
duplicating step has a denotation licensed by the counter observer. -/
theorem directGrammar_orienting_denotations_licensed_by_counter (e : MeasureExpr)
    (horients : OrientsDupStep e.eval) :
    Licensed (Prod.fst : Nat × Nat → Nat) (fun s => e.eval s.1 s.2) :=
  (payloadBlind_iff_licensed_by_counter e.eval).1 (orients_implies_payload_blind e horients)

/-- The license instance transfers to every syntax whose denotations are realized in the reflected
grammar. -/
theorem orienting_denotations_licensed_by_counter_of_denotational_subgrammar
    {E : Type u} (ev : E → Nat → Nat → Nat)
    (hsub : ∀ x : E, ∃ e : MeasureExpr, ev x = e.eval) (x : E)
    (horients : OrientsDupStep (ev x)) :
    Licensed (Prod.fst : Nat × Nat → Nat) (fun s => ev x s.1 s.2) := by
  obtain ⟨e, he⟩ := hsub x
  rw [he] at horients ⊢
  exact directGrammar_orienting_denotations_licensed_by_counter e horients

/-- The counter observer collides with the payload target at `(0, 0)` and `(0, 1)`. -/
theorem counter_payload_collision :
    OperationallyInexpressibleAt (Prod.fst : Nat × Nat → Nat) (Prod.snd : Nat × Nat → Nat)
      (0, 0) (0, 1) :=
  ⟨rfl, by decide⟩

/-- The payload target is not licensed by the counter observer. -/
theorem payload_target_unlicensed_by_counter :
    ¬ Licensed (Prod.fst : Nat × Nat → Nat) (Prod.snd : Nat × Nat → Nat) :=
  (unlicensed_iff_collision _ _).2 ⟨(0, 0), (0, 1), counter_payload_collision⟩

/-- The counter projection orients the duplicating step and is licensed by the counter observer,
so the license side of the instance is inhabited. -/
theorem counter_projection_orients_and_licensed :
    OrientsDupStep MeasureExpr.counter.eval ∧
      Licensed (Prod.fst : Nat × Nat → Nat) (fun s => MeasureExpr.counter.eval s.1 s.2) :=
  ⟨counter_orients, directGrammar_orienting_denotations_licensed_by_counter _ counter_orients⟩

/-- Outside the grammar, orientation does not imply the counter license:
`payloadSensitiveOrienter` orients the duplicating step and is not licensed by the counter
observer. -/
theorem payloadSensitiveOrienter_orients_and_unlicensed_by_counter :
    OrientsDupStep payloadSensitiveOrienter ∧
      ¬ Licensed (Prod.fst : Nat × Nat → Nat) (fun s => payloadSensitiveOrienter s.1 s.2) :=
  ⟨payloadSensitiveOrienter_orients,
    fun h => payloadSensitiveOrienter_not_payloadBlind
      ((payloadBlind_iff_licensed_by_counter _).2 h)⟩

end OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
