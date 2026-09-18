import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import Mathlib.Tactic

/-!
# Attained counter and payload pairs for the free schema

Every natural counter, payload, and positive duplicated-payload increment occurs
in an actual successor root step of the free recursor syntax.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.AttainedPairs

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

/-- Number of leading successor constructors. -/
def succPrefix {ν : Type} : FreeTerm ν → Nat
  | .succ t => succPrefix t + 1
  | _ => 0

/-- Counter observation used by the two-coordinate direct-measure model. -/
def counterObservation {ν : Type} : FreeTerm ν → Nat
  | .recur b _ n => succPrefix n + counterObservation b
  | .wrap _ t => counterObservation t
  | _ => 0

/-- Payload observation used by the two-coordinate direct-measure model. -/
def payloadObservation {ν : Type} : FreeTerm ν → Nat
  | .recur b _ _ => payloadObservation b
  | .wrap a b => payloadObservation a + payloadObservation b + 1
  | _ => 0

/-- Closed successor tower realizing an arbitrary counter value. -/
def counterTerm : Nat → FreeTerm Empty
  | 0 => .zero
  | n + 1 => .succ (counterTerm n)

/-- Closed wrapper tower realizing an arbitrary payload value. -/
def payloadTerm : Nat → FreeTerm Empty
  | 0 => .zero
  | n + 1 => .wrap .zero (payloadTerm n)

@[simp] theorem succPrefix_counterTerm (n : Nat) :
    succPrefix (counterTerm n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [counterTerm, succPrefix, ih]

@[simp] theorem counterObservation_payloadTerm (n : Nat) :
    counterObservation (payloadTerm n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [payloadTerm, counterObservation] using ih

@[simp] theorem payloadObservation_payloadTerm (n : Nat) :
    payloadObservation (payloadTerm n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [payloadTerm, payloadObservation, ih]

/-- A scalar function on the abstract pair induces a direct measure on free
terms. -/
def profileMeasure {ν : Type} (m : Nat → Nat → Nat) (t : FreeTerm ν) : Nat :=
  m (counterObservation t) (payloadObservation t)

/-- The free successor rule changes the observed pair by one counter unit and a
positive payload increment determined by its step argument. -/
theorem successor_profile {ν : Type} (b s n : FreeTerm ν) :
    counterObservation (.recur b s (.succ n)) =
        counterObservation (.wrap s (.recur b s n)) + 1 ∧
      payloadObservation (.wrap s (.recur b s n)) =
        payloadObservation (.recur b s (.succ n)) + (payloadObservation s + 1) := by
  simp only [counterObservation, payloadObservation, succPrefix]
  omega

/-- Every abstract duplicating-step triple `(c,p,L)` with positive `L` is
realized by an actual successor root step of the free syntax. -/
theorem every_successor_profile_attained (c p L : Nat) (hL : 1 ≤ L) :
    ∃ a b : FreeTerm Empty,
      RootStep a b ∧
      counterObservation a = c + 1 ∧
      payloadObservation a = p ∧
      counterObservation b = c ∧
      payloadObservation b = p + L := by
  let base := payloadTerm p
  let step := payloadTerm (L - 1)
  let ctr := counterTerm c
  refine ⟨.recur base step (.succ ctr),
    .wrap step (.recur base step ctr), .recurSucc _ _ _, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [base, step, ctr, counterObservation, payloadObservation, succPrefix]
  all_goals omega

/-- Uniform orientation of every actual free successor instance is equivalent to
orientation of every abstract pair triple. The reverse direction uses the
attainment theorem above. -/
theorem profile_orients_successors_iff (m : Nat → Nat → Nat) :
    (∀ {ν : Type} (b s n : FreeTerm ν),
      profileMeasure m (.wrap s (.recur b s n)) <
        profileMeasure m (.recur b s (.succ n))) ↔
      OrientsDupStep m := by
  constructor
  · intro h c p L hL
    let base := payloadTerm p
    let step := payloadTerm (L - 1)
    let ctr := counterTerm c
    have he := h base step ctr
    have hL' : L - 1 + p + 1 = p + L := by omega
    simpa [profileMeasure, base, step, ctr, counterObservation,
      payloadObservation, succPrefix, hL'] using he
  · intro h ν b s n
    obtain ⟨hc, hp⟩ := successor_profile b s n
    unfold profileMeasure
    rw [hc, hp]
    exact h _ _ _ (Nat.succ_le_succ (Nat.zero_le _))

/-- The counter projection orients every successor root instance of the free
syntax. -/
theorem counter_profile_orients_successors :
    ∀ {ν : Type} (b s n : FreeTerm ν),
      profileMeasure MeasureExpr.counter.eval (.wrap s (.recur b s n)) <
        profileMeasure MeasureExpr.counter.eval (.recur b s (.succ n)) := by
  exact (profile_orients_successors_iff MeasureExpr.counter.eval).2 counter_orients

/-- Any scalar grammar expression that orients all free successor instances is
payload-blind. -/
theorem free_successor_orientation_implies_payloadBlind (e : MeasureExpr)
    (h : ∀ {ν : Type} (b s n : FreeTerm ν),
      profileMeasure e.eval (.wrap s (.recur b s n)) <
        profileMeasure e.eval (.recur b s (.succ n))) :
    PayloadBlind e.eval := by
  exact orients_implies_payload_blind e ((profile_orients_successors_iff e.eval).1 h)

end OperatorKO7.Methods.OrientationClosure.AttainedPairs
