import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import Mathlib.Tactic

/-!
# Attained counter and payload pairs for the free schema

Every natural counter, payload, and positive duplicated-payload increment occurs
in an actual successor root step of the free recursor syntax, at every variable
type. The attaining terms are closed; `closedEmbed` carries a closed term into
`FreeTerm ν` for every `ν` and keeps both observations, so the attainment theorem
and the orientation equivalence hold carrier by carrier.
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

/-! ## Closed terms inside every carrier -/

/--
Proves: nothing; this is the inclusion of the closed free terms into the free
terms over an arbitrary variable type, constructor by constructor.
Does not prove: any property of the inclusion; the theorems below state
injectivity, the two observation equations and root-step preservation.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: definition only.
Scope: every `ν : Type`.
-/
def closedEmbed {ν : Type} : FreeTerm Empty → FreeTerm ν
  | .var x => x.elim
  | .zero => .zero
  | .succ t => .succ (closedEmbed t)
  | .wrap s t => .wrap (closedEmbed s) (closedEmbed t)
  | .recur b s n => .recur (closedEmbed b) (closedEmbed s) (closedEmbed n)

/--
Proves: the inclusion of closed free terms into `FreeTerm ν` is injective.
Does not prove: surjectivity; a variable of `ν` lies outside the image.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; structural induction.
Scope: every `ν : Type`.
-/
theorem closedEmbed_injective {ν : Type} :
    Function.Injective (closedEmbed : FreeTerm Empty → FreeTerm ν) := by
  intro a
  induction a with
  | var x => exact x.elim
  | zero =>
      intro c h
      cases c with
      | var y => exact y.elim
      | zero => rfl
      | succ u => simp [closedEmbed] at h
      | wrap u v => simp [closedEmbed] at h
      | recur u v w => simp [closedEmbed] at h
  | succ t ih =>
      intro c h
      cases c with
      | var y => exact y.elim
      | zero => simp [closedEmbed] at h
      | succ u =>
          simp only [closedEmbed, FreeTerm.succ.injEq] at h
          rw [ih h]
      | wrap u v => simp [closedEmbed] at h
      | recur u v w => simp [closedEmbed] at h
  | wrap s t ihs iht =>
      intro c h
      cases c with
      | var y => exact y.elim
      | zero => simp [closedEmbed] at h
      | succ u => simp [closedEmbed] at h
      | wrap u v =>
          simp only [closedEmbed, FreeTerm.wrap.injEq] at h
          rw [ihs h.1, iht h.2]
      | recur u v w => simp [closedEmbed] at h
  | recur b s n ihb ihs ihn =>
      intro c h
      cases c with
      | var y => exact y.elim
      | zero => simp [closedEmbed] at h
      | succ u => simp [closedEmbed] at h
      | wrap u v => simp [closedEmbed] at h
      | recur u v w =>
          simp only [closedEmbed, FreeTerm.recur.injEq] at h
          rw [ihb h.1, ihs h.2.1, ihn h.2.2]

/--
Proves: the inclusion keeps the length of the leading successor prefix.
Does not prove: anything about terms outside the image of the inclusion.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; structural induction.
Scope: every `ν : Type` and every closed free term.
-/
theorem succPrefix_closedEmbed {ν : Type} (t : FreeTerm Empty) :
    succPrefix (closedEmbed (ν := ν) t) = succPrefix t := by
  induction t with
  | var x => exact x.elim
  | zero => rfl
  | succ t ih =>
      show succPrefix (closedEmbed (ν := ν) t) + 1 = succPrefix t + 1
      rw [ih]
  | wrap s t _ _ => rfl
  | recur b s n _ _ _ => rfl

/--
Proves: the inclusion keeps the counter observation.
Does not prove: anything about terms outside the image of the inclusion.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; structural induction.
Scope: every `ν : Type` and every closed free term.
-/
theorem counterObservation_closedEmbed {ν : Type} (t : FreeTerm Empty) :
    counterObservation (closedEmbed (ν := ν) t) = counterObservation t := by
  induction t with
  | var x => exact x.elim
  | zero => rfl
  | succ t _ => rfl
  | wrap s t _ iht =>
      show counterObservation (closedEmbed (ν := ν) t) = counterObservation t
      exact iht
  | recur b s n ihb _ _ =>
      show succPrefix (closedEmbed (ν := ν) n) + counterObservation (closedEmbed (ν := ν) b) =
        succPrefix n + counterObservation b
      rw [succPrefix_closedEmbed, ihb]

/--
Proves: the inclusion keeps the payload observation.
Does not prove: anything about terms outside the image of the inclusion.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; structural induction.
Scope: every `ν : Type` and every closed free term.
-/
theorem payloadObservation_closedEmbed {ν : Type} (t : FreeTerm Empty) :
    payloadObservation (closedEmbed (ν := ν) t) = payloadObservation t := by
  induction t with
  | var x => exact x.elim
  | zero => rfl
  | succ t _ => rfl
  | wrap s t ihs iht =>
      show payloadObservation (closedEmbed (ν := ν) s) +
          payloadObservation (closedEmbed (ν := ν) t) + 1 =
        payloadObservation s + payloadObservation t + 1
      rw [ihs, iht]
  | recur b s n ihb _ _ =>
      show payloadObservation (closedEmbed (ν := ν) b) = payloadObservation b
      exact ihb

/--
Proves: every profile measure takes the same value on a closed term and on its
image in `FreeTerm ν`.
Does not prove: anything about terms outside the image of the inclusion.
Relation: none.
Closure: not applicable.
Strategy: not applicable.
Trust: Lean kernel; the two observation equations.
Scope: every `ν : Type`, every `m : Nat → Nat → Nat`, every closed free term.
-/
theorem profileMeasure_closedEmbed {ν : Type} (m : Nat → Nat → Nat) (t : FreeTerm Empty) :
    profileMeasure m (closedEmbed (ν := ν) t) = profileMeasure m t := by
  unfold profileMeasure
  rw [counterObservation_closedEmbed, payloadObservation_closedEmbed]

/--
Proves: the inclusion maps each root step of the closed free terms to a root step
of `FreeTerm ν`, rule to rule.
Does not prove: that every root step out of an included term comes from a closed
root step.
Relation: `RootStep`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; case analysis on the two root rules.
Scope: every `ν : Type` and every closed root step.
-/
theorem rootStep_closedEmbed {ν : Type} {a b : FreeTerm Empty} (h : RootStep a b) :
    RootStep (closedEmbed (ν := ν) a) (closedEmbed (ν := ν) b) := by
  cases h with
  | recurZero b s => exact RootStep.recurZero _ _
  | recurSucc b s n => exact RootStep.recurSucc _ _ _

/-! ## Attainment and orientation at each carrier -/

/--
Proves: at every variable type `ν`, every counter value `c`, payload value `p` and
positive increment `L` is the observed profile of an actual successor root step
of `FreeTerm ν`: the source observes `(c + 1, p)` and the target `(c, p + L)`.
Does not prove: anything about the zero rule, or attainment by contextual steps.
Relation: `RootStep` (its successor rule) on `FreeTerm ν`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; the attaining terms are closed towers carried into
`FreeTerm ν` by `closedEmbed`.
Scope: every `ν : Type`, every `c p L` with `1 ≤ L`.
-/
theorem every_successor_profile_attained {ν : Type} (c p L : Nat) (hL : 1 ≤ L) :
    ∃ a b : FreeTerm ν,
      RootStep a b ∧
      counterObservation a = c + 1 ∧
      payloadObservation a = p ∧
      counterObservation b = c ∧
      payloadObservation b = p + L := by
  have hclosed : ∃ a b : FreeTerm Empty,
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
  obtain ⟨a, b, hab, ha1, ha2, hb1, hb2⟩ := hclosed
  refine ⟨closedEmbed a, closedEmbed b, rootStep_closedEmbed hab, ?_, ?_, ?_, ?_⟩
  · rw [counterObservation_closedEmbed, ha1]
  · rw [payloadObservation_closedEmbed, ha2]
  · rw [counterObservation_closedEmbed, hb1]
  · rw [payloadObservation_closedEmbed, hb2]

/--
Proves: if a profile measure decreases across every successor root instance of
`FreeTerm ν`, then it decreases across every successor root instance of the
closed free terms.
Does not prove: the converse by itself; `successor_orientation_carrier_independent`
gives it through the numeric condition.
Relation: the successor rule of `RootStep`, on `FreeTerm ν` and on `FreeTerm Empty`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; `closedEmbed` and `profileMeasure_closedEmbed`.
Scope: every `ν : Type` and every `m : Nat → Nat → Nat`.
-/
theorem successor_orientation_restricts_to_closed {ν : Type} (m : Nat → Nat → Nat)
    (h : ∀ b s n : FreeTerm ν,
      profileMeasure m (.wrap s (.recur b s n)) <
        profileMeasure m (.recur b s (.succ n))) :
    ∀ b s n : FreeTerm Empty,
      profileMeasure m (.wrap s (.recur b s n)) <
        profileMeasure m (.recur b s (.succ n)) := by
  intro b s n
  have he := h (closedEmbed b) (closedEmbed s) (closedEmbed n)
  have e1 : profileMeasure m
      (FreeTerm.wrap (closedEmbed s)
        (FreeTerm.recur (closedEmbed b) (closedEmbed s) (closedEmbed n)) : FreeTerm ν) =
      profileMeasure m (FreeTerm.wrap s (FreeTerm.recur b s n)) :=
    profileMeasure_closedEmbed m (FreeTerm.wrap s (FreeTerm.recur b s n))
  have e2 : profileMeasure m
      (FreeTerm.recur (closedEmbed b) (closedEmbed s) (FreeTerm.succ (closedEmbed n)) :
        FreeTerm ν) =
      profileMeasure m (FreeTerm.recur b s (FreeTerm.succ n)) :=
    profileMeasure_closedEmbed m (FreeTerm.recur b s (FreeTerm.succ n))
  rw [e1, e2] at he
  exact he

/--
Proves: at every variable type `ν`, a profile measure `m ∘ (c, p)` decreases
across every successor root instance of `FreeTerm ν` if and only if `m` satisfies
the numeric duplicating-step condition `OrientsDupStep m`.
Does not prove: anything about the zero rule or about contextual steps.
Relation: the successor rule of `RootStep` on `FreeTerm ν`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; the forward direction instantiates the closed attaining terms
after `successor_orientation_restricts_to_closed`, the reverse direction uses
`successor_profile`.
Scope: every `ν : Type` and every `m : Nat → Nat → Nat`.
-/
theorem profile_orients_successors_iff {ν : Type} (m : Nat → Nat → Nat) :
    (∀ b s n : FreeTerm ν,
      profileMeasure m (.wrap s (.recur b s n)) <
        profileMeasure m (.recur b s (.succ n))) ↔
      OrientsDupStep m := by
  constructor
  · intro hν c p L hL
    have h := successor_orientation_restricts_to_closed m hν
    let base := payloadTerm p
    let step := payloadTerm (L - 1)
    let ctr := counterTerm c
    have he := h base step ctr
    have hL' : L - 1 + p + 1 = p + L := by omega
    simpa [profileMeasure, base, step, ctr, counterObservation,
      payloadObservation, succPrefix, hL'] using he
  · intro h b s n
    obtain ⟨hc, hp⟩ := successor_profile b s n
    unfold profileMeasure
    rw [hc, hp]
    exact h _ _ _ (Nat.succ_le_succ (Nat.zero_le _))

/--
Proves: for two variable types `ν` and `μ`, a profile measure decreases across
every successor root instance of `FreeTerm ν` if and only if it decreases across
every successor root instance of `FreeTerm μ`.
Does not prove: anything about measures that do not factor through the observed
profile.
Relation: the successor rule of `RootStep` on `FreeTerm ν` and on `FreeTerm μ`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; two instances of `profile_orients_successors_iff`.
Scope: every `ν μ : Type` and every `m : Nat → Nat → Nat`.
-/
theorem successor_orientation_carrier_independent {ν μ : Type} (m : Nat → Nat → Nat) :
    (∀ b s n : FreeTerm ν,
      profileMeasure m (.wrap s (.recur b s n)) <
        profileMeasure m (.recur b s (.succ n))) ↔
    (∀ b s n : FreeTerm μ,
      profileMeasure m (.wrap s (.recur b s n)) <
        profileMeasure m (.recur b s (.succ n))) :=
  (profile_orients_successors_iff m).trans (profile_orients_successors_iff m).symm

/-- The counter projection orients every successor root instance of the free
syntax. -/
theorem counter_profile_orients_successors :
    ∀ {ν : Type} (b s n : FreeTerm ν),
      profileMeasure MeasureExpr.counter.eval (.wrap s (.recur b s n)) <
        profileMeasure MeasureExpr.counter.eval (.recur b s (.succ n)) := by
  intro ν
  exact (profile_orients_successors_iff (ν := ν) MeasureExpr.counter.eval).2 counter_orients

/--
Proves: at every variable type `ν`, a scalar grammar expression whose profile
measure decreases across every successor root instance of `FreeTerm ν` is
payload-blind.
Does not prove: counter strictness, which the capstone biconditional adds.
Relation: the successor rule of `RootStep` on `FreeTerm ν`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the axioms of `orients_implies_payload_blind`.
Scope: every `ν : Type` and every `MeasureExpr`.
-/
theorem free_successor_orientation_implies_payloadBlind {ν : Type} (e : MeasureExpr)
    (h : ∀ b s n : FreeTerm ν,
      profileMeasure e.eval (.wrap s (.recur b s n)) <
        profileMeasure e.eval (.recur b s (.succ n))) :
    PayloadBlind e.eval := by
  exact orients_implies_payload_blind e ((profile_orients_successors_iff e.eval).1 h)

end OperatorKO7.Methods.OrientationClosure.AttainedPairs
