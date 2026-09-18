import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import Mathlib.Tactic

/-!
# Decision procedure for the scalar direct-measure grammar

The existing grammar theorem characterizes orientation semantically by
payload-independence and strict counter response. This module computes both
conditions for the seven-constructor grammar and returns a proof or a concrete
failed duplicating-step instance.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.ScalarGrammarDecision

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

/-- Executable positivity test at the unit input. Evaluation is itself structural
on the reflected grammar. -/
def positiveAtUnit? (e : MeasureExpr) : Bool := decide (0 < e.eval 1 1)

@[simp] theorem positiveAtUnit?_eq_true_iff (e : MeasureExpr) :
    positiveAtUnit? e = true ↔ 0 < e.eval 1 1 := by
  simp [positiveAtUnit?]

/-- Zero at `(1,1)` forces a grammar expression to be the zero function. -/
theorem eval_one_one_eq_zero_implies_zero (e : MeasureExpr)
    (h : e.eval 1 1 = 0) : ∀ c p, e.eval c p = 0 := by
  induction e with
  | counter => simp [MeasureExpr.eval] at h
  | payload => simp [MeasureExpr.eval] at h
  | const n =>
      simp [MeasureExpr.eval] at h ⊢
      exact h
  | add e f ihe ihf =>
      have hz : e.eval 1 1 = 0 ∧ f.eval 1 1 = 0 := by
        simpa [MeasureExpr.eval] using h
      intro c p
      simp [MeasureExpr.eval, ihe hz.1 c p, ihf hz.2 c p]
  | mul e f ihe ihf =>
      have hz : e.eval 1 1 = 0 ∨ f.eval 1 1 = 0 := by
        simpa [MeasureExpr.eval] using h
      intro c p
      rcases hz with he | hf
      · simp [MeasureExpr.eval, ihe he c p]
      · simp [MeasureExpr.eval, ihf hf c p]
  | max e f ihe ihf =>
      have he : e.eval 1 1 = 0 := by
        have : e.eval 1 1 ≤ Nat.max (e.eval 1 1) (f.eval 1 1) := Nat.le_max_left _ _
        rw [show Nat.max (e.eval 1 1) (f.eval 1 1) = 0 by simpa [MeasureExpr.eval] using h] at this
        omega
      have hf : f.eval 1 1 = 0 := by
        have : f.eval 1 1 ≤ Nat.max (e.eval 1 1) (f.eval 1 1) := Nat.le_max_right _ _
        rw [show Nat.max (e.eval 1 1) (f.eval 1 1) = 0 by simpa [MeasureExpr.eval] using h] at this
        omega
      intro c p
      simp [MeasureExpr.eval, ihe he c p, ihf hf c p]
  | smul n e ihe =>
      have hz : n = 0 ∨ e.eval 1 1 = 0 := by
        simpa [MeasureExpr.eval] using h
      intro c p
      rcases hz with hn | he
      · simp [MeasureExpr.eval, hn]
      · simp [MeasureExpr.eval, ihe he c p]

/-- A failed unit positivity test identifies the zero function. -/
theorem positiveAtUnit?_false_implies_zero (e : MeasureExpr)
    (h : positiveAtUnit? e = false) : ∀ c p, e.eval c p = 0 := by
  have hn : ¬ 0 < e.eval 1 1 := by
    simpa [positiveAtUnit?] using h
  have hz : e.eval 1 1 = 0 := by omega
  exact eval_one_one_eq_zero_implies_zero e hz

/-- Unit positivity remains positive at every payload `L ≥ 1` with counter one. -/
theorem positiveAtUnit?_eval_ge_one (e : MeasureExpr)
    (h : positiveAtUnit? e = true) {L : Nat} (hL : 1 ≤ L) :
    1 ≤ e.eval 1 L := by
  have h1 : 1 ≤ e.eval 1 1 := by
    have := (positiveAtUnit?_eq_true_iff e).1 h
    omega
  exact h1.trans (eval_payloadMonotone e 1 1 L hL)

/-- Complete structural payload-dependence test for this grammar. A product reads
payload exactly when one factor reads payload and the other is nonzero. -/
def readsPayload? : MeasureExpr → Bool
  | .counter => false
  | .payload => true
  | .const _ => false
  | .add e f => readsPayload? e || readsPayload? f
  | .mul e f =>
      (readsPayload? e && positiveAtUnit? f) ||
        (readsPayload? f && positiveAtUnit? e)
  | .max e f => readsPayload? e || readsPayload? f
  | .smul n e => decide (0 < n) && readsPayload? e

/-- A positive payload-dependence decision gives an explicit unbounded lower
bound at counter one. -/
theorem readsPayload?_true_lower_bound (e : MeasureExpr)
    (h : readsPayload? e = true) :
    ∀ L, 1 ≤ L → L ≤ e.eval 1 L := by
  induction e with
  | counter => simp [readsPayload?] at h
  | payload =>
      intro L hL
      simp [MeasureExpr.eval]
  | const n => simp [readsPayload?] at h
  | add e f ihe ihf =>
      simp [readsPayload?] at h
      intro L hL
      rcases h with he | hf
      · have hsub := ihe he L hL
        simpa [MeasureExpr.eval] using hsub.trans (Nat.le_add_right _ _)
      · have hsub := ihf hf L hL
        simpa [MeasureExpr.eval] using hsub.trans (Nat.le_add_left _ _)
  | mul e f ihe ihf =>
      simp [readsPayload?] at h
      intro L hL
      rcases h with hleft | hright
      · rcases hleft with ⟨he, hfpos⟩
        have heL := ihe he L hL
        have hfL := positiveAtUnit?_eval_ge_one f
          ((positiveAtUnit?_eq_true_iff f).2 hfpos) hL
        have hmul : e.eval 1 L ≤ e.eval 1 L * f.eval 1 L :=
          Nat.le_mul_of_pos_right _ hfL
        exact heL.trans hmul
      · rcases hright with ⟨hf, hepos⟩
        have hfL := ihf hf L hL
        have heL := positiveAtUnit?_eval_ge_one e
          ((positiveAtUnit?_eq_true_iff e).2 hepos) hL
        have hmul : f.eval 1 L ≤ e.eval 1 L * f.eval 1 L := by
          have h' : f.eval 1 L ≤ f.eval 1 L * e.eval 1 L :=
            Nat.le_mul_of_pos_right _ heL
          simpa [Nat.mul_comm] using h'
        exact hfL.trans hmul
  | max e f ihe ihf =>
      simp [readsPayload?] at h
      intro L hL
      rcases h with he | hf
      · exact (ihe he L hL).trans (Nat.le_max_left _ _)
      · exact (ihf hf L hL).trans (Nat.le_max_right _ _)
  | smul n e ihe =>
      simp [readsPayload?] at h
      rcases h with ⟨hn, he⟩
      intro L hL
      have heL := ihe he L hL
      have hn1 : 1 ≤ n := by omega
      have hmul : e.eval 1 L ≤ n * e.eval 1 L :=
        Nat.le_mul_of_pos_left _ hn1
      exact heL.trans hmul

/-- A negative payload-dependence decision proves semantic payload-independence. -/
theorem readsPayload?_false_payloadBlind (e : MeasureExpr)
    (h : readsPayload? e = false) : PayloadBlind e.eval := by
  induction e with
  | counter => intro c p p'; rfl
  | payload => simp [readsPayload?] at h
  | const n => intro c p p'; rfl
  | add e f ihe ihf =>
      have hz : readsPayload? e = false ∧ readsPayload? f = false := by
        simpa [readsPayload?] using h
      intro c p p'
      simp [MeasureExpr.eval, ihe hz.1 c p p', ihf hz.2 c p p']
  | mul e f ihe ihf =>
      by_cases he : readsPayload? e = true
      · have hpf : positiveAtUnit? f = false := by
          cases hp : positiveAtUnit? f with
          | false => rfl
          | true => simp [readsPayload?, he, hp] at h
        have fzero := positiveAtUnit?_false_implies_zero f hpf
        intro c p p'
        simp [MeasureExpr.eval, fzero c p, fzero c p']
      · have hef : readsPayload? e = false := Bool.eq_false_of_not_eq_true he
        by_cases hf : readsPayload? f = true
        · have hpe : positiveAtUnit? e = false := by
            cases hp : positiveAtUnit? e with
            | false => rfl
            | true => simp [readsPayload?, hf, hp] at h
          have ezero := positiveAtUnit?_false_implies_zero e hpe
          intro c p p'
          simp [MeasureExpr.eval, ezero c p, ezero c p']
        · have hff : readsPayload? f = false := Bool.eq_false_of_not_eq_true hf
          intro c p p'
          simp [MeasureExpr.eval, ihe hef c p p', ihf hff c p p']
  | max e f ihe ihf =>
      have hz : readsPayload? e = false ∧ readsPayload? f = false := by
        simpa [readsPayload?] using h
      intro c p p'
      simp [MeasureExpr.eval, ihe hz.1 c p p', ihf hz.2 c p p']
  | smul n e ihe =>
      by_cases hn : n = 0
      · intro c p p'; simp [MeasureExpr.eval, hn]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have he : readsPayload? e = false := by
          simpa [readsPayload?, hnpos] using h
        intro c p p'
        simp [MeasureExpr.eval, ihe he c p p']

/-- A positive payload-dependence decision refutes payload-independence. -/
theorem readsPayload?_true_not_payloadBlind (e : MeasureExpr)
    (h : readsPayload? e = true) : ¬ PayloadBlind e.eval := by
  intro hblind
  let L := e.eval 1 0 + 1
  have hL : 1 ≤ L := by simp [L]
  have hlower := readsPayload?_true_lower_bound e h L hL
  have heq := hblind 1 L 0
  rw [heq] at hlower
  simp [L] at hlower

/-- The new checker decides semantic payload-independence for the entire grammar. -/
theorem readsPayload?_eq_false_iff_payloadBlind (e : MeasureExpr) :
    readsPayload? e = false ↔ PayloadBlind e.eval := by
  constructor
  · exact readsPayload?_false_payloadBlind e
  · intro hblind
    cases h : readsPayload? e with
    | false => rfl
    | true => exact False.elim ((readsPayload?_true_not_payloadBlind e h) hblind)

/-- Equivalent positive form of the payload-dependence decision. -/
theorem readsPayload?_eq_true_iff_not_payloadBlind (e : MeasureExpr) :
    readsPayload? e = true ↔ ¬ PayloadBlind e.eval := by
  constructor
  · exact readsPayload?_true_not_payloadBlind e
  · intro hnot
    cases h : readsPayload? e with
    | true => rfl
    | false => exact False.elim (hnot (readsPayload?_false_payloadBlind e h))

/-- Every grammar expression is nondecreasing in its counter coordinate. -/
theorem eval_counterMonotone (e : MeasureExpr) :
    ∀ p c, e.eval c p ≤ e.eval (c + 1) p := by
  induction e with
  | counter => intro p c; simp [MeasureExpr.eval]
  | payload => intro p c; rfl
  | const n => intro p c; rfl
  | add e f ihe ihf =>
      intro p c
      exact Nat.add_le_add (ihe p c) (ihf p c)
  | mul e f ihe ihf =>
      intro p c
      exact Nat.mul_le_mul (ihe p c) (ihf p c)
  | max e f ihe ihf =>
      intro p c
      exact max_le_max (ihe p c) (ihf p c)
  | smul n e ihe =>
      intro p c
      exact Nat.mul_le_mul_left n (ihe p c)

/-- Product closure for discrete convexity of nondecreasing natural sequences. -/
theorem mul_step_convex
    (a₀ a₁ a₂ b₀ b₁ b₂ : Nat)
    (ha01 : a₀ ≤ a₁) (ha12 : a₁ ≤ a₂)
    (hb01 : b₀ ≤ b₁) (hb12 : b₁ ≤ b₂)
    (ha : a₁ + a₁ ≤ a₀ + a₂)
    (hb : b₁ + b₁ ≤ b₀ + b₂) :
    a₁ * b₁ + a₁ * b₁ ≤ a₀ * b₀ + a₂ * b₂ := by
  obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le ha01
  obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le ha12
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hb01
  obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hb12
  have hxy : x ≤ y := by omega
  have huv : u ≤ v := by omega
  obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le hxy
  obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le huv
  subst a₁
  subst a₂
  subst b₁
  subst b₂
  subst y
  subst v
  nlinarith [Nat.zero_le (a₀ * w), Nat.zero_le (b₀ * z),
    Nat.zero_le (x * w), Nat.zero_le ((x + z) * (u + (u + w)))]

/-- Counter sections of every grammar expression are discrete convex. -/
theorem eval_counterStepConvex (e : MeasureExpr) :
    ∀ p c,
      e.eval (c + 1) p + e.eval (c + 1) p ≤
        e.eval c p + e.eval (c + 2) p := by
  induction e with
  | counter => intro p c; simp [MeasureExpr.eval]; omega
  | payload => intro p c; simp [MeasureExpr.eval]
  | const n => intro p c; simp [MeasureExpr.eval]
  | add e f ihe ihf =>
      intro p c
      have he := ihe p c
      have hf := ihf p c
      simp [MeasureExpr.eval] at he hf ⊢
      omega
  | mul e f ihe ihf =>
      intro p c
      apply mul_step_convex
      · exact eval_counterMonotone e p c
      · simpa [Nat.add_assoc] using eval_counterMonotone e p (c + 1)
      · exact eval_counterMonotone f p c
      · simpa [Nat.add_assoc] using eval_counterMonotone f p (c + 1)
      · simpa [Nat.add_assoc] using ihe p c
      · simpa [Nat.add_assoc] using ihf p c
  | max e f ihe ihf =>
      intro p c
      by_cases h : e.eval (c + 1) p ≤ f.eval (c + 1) p
      · have hf := ihf p c
        have hsides :
            f.eval c p + f.eval (c + 2) p ≤
              Nat.max (e.eval c p) (f.eval c p) +
                Nat.max (e.eval (c + 2) p) (f.eval (c + 2) p) :=
          Nat.add_le_add (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        simpa [MeasureExpr.eval, Nat.max_eq_right h] using hf.trans hsides
      · have he := ihe p c
        have h' : f.eval (c + 1) p ≤ e.eval (c + 1) p := by omega
        have hsides :
            e.eval c p + e.eval (c + 2) p ≤
              Nat.max (e.eval c p) (f.eval c p) +
                Nat.max (e.eval (c + 2) p) (f.eval (c + 2) p) :=
          Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        simpa [MeasureExpr.eval, Nat.max_eq_left h'] using he.trans hsides
  | smul n e ihe =>
      intro p c
      have h := Nat.mul_le_mul_left n (ihe p c)
      simpa [MeasureExpr.eval, Nat.mul_add] using h

/-- For a discrete-convex counter section, a strict first increment propagates to
every later counter. Payload-independence transfers the first increment from
payload zero to every payload. -/
theorem initialCounterRise_implies_counterStrict (e : MeasureExpr)
    (hblind : PayloadBlind e.eval)
    (h01 : e.eval 0 0 < e.eval 1 0) : CounterStrict e.eval := by
  intro c p
  have hbase : e.eval 0 p < e.eval 1 p := by
    rw [hblind 0 p 0, hblind 1 p 0]
    exact h01
  induction c with
  | zero => simpa using hbase
  | succ c ih =>
      have hconv := eval_counterStepConvex e p c
      have hnext : e.eval (c + 1) p < e.eval (c + 2) p := by omega
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hnext

/-- Under semantic payload-independence, strict counter response is decided by
the first counter increment. -/
theorem counterStrict_iff_initial_of_payloadBlind (e : MeasureExpr)
    (hblind : PayloadBlind e.eval) :
    CounterStrict e.eval ↔ e.eval 0 0 < e.eval 1 0 := by
  constructor
  · intro h
    simpa using h 0 0
  · exact initialCounterRise_implies_counterStrict e hblind

/-- A concrete refutation of one uniform duplicating-step comparison. -/
structure FailedDupWitness (e : MeasureExpr) where
  counter : Nat
  payload : Nat
  increment : Nat
  increment_pos : 1 ≤ increment
  fails : ¬ e.eval counter (payload + increment) < e.eval (counter + 1) payload

/-- Payload dependence yields a computed failed duplicating-step instance. -/
def payloadFailureWitness (e : MeasureExpr)
    (h : readsPayload? e = true) : FailedDupWitness e := by
  let L := e.eval 2 0 + 1
  refine ⟨1, 0, L, by simp [L], ?_⟩
  have hlower := readsPayload?_true_lower_bound e h L (by simp [L])
  simp [L] at hlower ⊢
  omega

/-- Failed first counter growth gives the smallest failed instance once payload
is known to be irrelevant. -/
def counterFailureWitness (e : MeasureExpr)
    (hblind : PayloadBlind e.eval)
    (h01 : ¬ e.eval 0 0 < e.eval 1 0) : FailedDupWitness e := by
  refine ⟨0, 0, 1, by omega, ?_⟩
  have heq := hblind 0 1 0
  simpa using (show ¬ e.eval 0 1 < e.eval 1 0 by
    intro hlt
    rw [heq] at hlt
    exact h01 hlt)

/-- Three-way proof-producing classifier. -/
inductive Decision (e : MeasureExpr) where
  | orients (proof : OrientsDupStep e.eval)
  | blockedPayload (witness : FailedDupWitness e)
  | blockedCounter (witness : FailedDupWitness e)

/-- Execute the complete orientation decision for the reflected scalar grammar. -/
def classify (e : MeasureExpr) : Decision e := by
  by_cases hread : readsPayload? e = true
  · exact .blockedPayload (payloadFailureWitness e hread)
  · have hreadFalse : readsPayload? e = false := Bool.eq_false_of_not_eq_true hread
    have hblind := readsPayload?_false_payloadBlind e hreadFalse
    by_cases h01 : e.eval 0 0 < e.eval 1 0
    · have hcounter := initialCounterRise_implies_counterStrict e hblind h01
      exact .orients (payloadBlind_and_counterStrict_implies_orients hblind hcounter)
    · exact .blockedCounter (counterFailureWitness e hblind h01)

/-- Every classifier result contains either a proof of orientation or a concrete
failed duplicating-step instance. -/
theorem classify_sound (e : MeasureExpr) :
    OrientsDupStep e.eval ∨ Nonempty (FailedDupWitness e) := by
  cases classify e with
  | orients h => exact Or.inl h
  | blockedPayload w => exact Or.inr ⟨w⟩
  | blockedCounter w => exact Or.inr ⟨w⟩

/-- Proof-insensitive predicate selecting the orientation constructor. -/
def Decision.IsOrienting {e : MeasureExpr} : Decision e → Prop
  | .orients _ => True
  | .blockedPayload _ => False
  | .blockedCounter _ => False

/-- The classifier selects its orientation constructor exactly when the semantic
orientation predicate holds. -/
theorem classify_isOrienting_iff (e : MeasureExpr) :
    (classify e).IsOrienting ↔ OrientsDupStep e.eval := by
  unfold classify
  by_cases hread : readsPayload? e = true
  · simp [hread, Decision.IsOrienting]
    intro horient
    exact (readsPayload?_true_not_payloadBlind e hread)
      (orients_implies_payload_blind e horient)
  · have hreadFalse : readsPayload? e = false := Bool.eq_false_of_not_eq_true hread
    have hblind := readsPayload?_false_payloadBlind e hreadFalse
    by_cases h01 : e.eval 0 0 < e.eval 1 0
    · simp [hread, h01, Decision.IsOrienting]
      exact payloadBlind_and_counterStrict_implies_orients hblind
        (initialCounterRise_implies_counterStrict e hblind h01)
    · simp [hread, h01, Decision.IsOrienting]
      intro horient
      exact h01 (by simpa using (orients_implies_counterStrict e horient) 0 0)

/-- The product expression `(1 + payload) * (counter + 1)` used by the
roadmap's retraction control. -/
def productPayloadCounterExpr : MeasureExpr :=
  .mul (.add (.const 1) .payload) (.add .counter (.const 1))

/-- The product expression reads payload and therefore belongs to the blocked
payload branch of the complete scalar grammar classifier. -/
theorem productPayloadCounter_classified_blockedPayload :
    ∃ w : FailedDupWitness productPayloadCounterExpr,
      classify productPayloadCounterExpr = .blockedPayload w := by
  unfold productPayloadCounterExpr classify
  simp [readsPayload?, positiveAtUnit?, MeasureExpr.eval]

/-- `payload * counter` is detected as payload-dependent by the new checker. -/
theorem payload_mul_counter_detected :
    readsPayload? (.mul .payload .counter) = true := by
  rfl

/-- Zero scalar multiplication erases payload dependence. -/
theorem zero_smul_payload_rejected :
    readsPayload? (.smul 0 .payload) = false := by
  rfl

/-- A large constant branch creates an initial counter plateau. -/
theorem max_counter_hundred_initial_plateau :
    ¬ (MeasureExpr.max MeasureExpr.counter (.const 100)).eval 0 0 <
      (MeasureExpr.max MeasureExpr.counter (.const 100)).eval 1 0 := by
  norm_num [MeasureExpr.eval]

/-- Squaring the counter has a strict first increment and therefore orients. -/
theorem counter_square_orients :
    OrientsDupStep (MeasureExpr.mul MeasureExpr.counter MeasureExpr.counter).eval := by
  have hblind :
      PayloadBlind (MeasureExpr.mul MeasureExpr.counter MeasureExpr.counter).eval := by
    intro c p p'
    rfl
  apply payloadBlind_and_counterStrict_implies_orients hblind
  exact initialCounterRise_implies_counterStrict
    (MeasureExpr.mul MeasureExpr.counter MeasureExpr.counter) hblind
    (by norm_num [MeasureExpr.eval])


/-- C03: every constant expression is payload-blind and fails strict counter response. -/
theorem const_payloadBlind_not_counterStrict (n : Nat) :
    PayloadBlind (MeasureExpr.const n).eval ∧ ¬ CounterStrict (MeasureExpr.const n).eval := by
  constructor
  · intro c p p'
    rfl
  · intro h
    have h0 := h 0 0
    simp [MeasureExpr.eval] at h0

end OperatorKO7.Methods.OrientationClosure.ScalarGrammarDecision
