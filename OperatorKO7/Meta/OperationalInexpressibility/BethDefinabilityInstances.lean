import OperatorKO7.Meta.OperationalInexpressibility.BethDefinability
import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarLicense
import Mathlib.Order.Monotone.Basic

/-!
# The Beth property of the direct grammar and of the projection language

On counter and payload readings, with targets that orient the duplicating step: the direct
grammar fails the Beth property for the full reading and for the counter, and the language of
strictly increasing functions of the counter has it.

Relation: denotations on `ℕ × ℕ`; the counter and the full reading as observers.
Property: Beth failure and Beth property on the orienting targets.
Trust: kernel only.
Scope: the reflected direct grammar and the projection language.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.BethDefinabilityInstances

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification

/-- Targets on `ℕ × ℕ` that orient the duplicating step. -/
def Orienting (P : ℕ × ℕ → ℕ) : Prop := OrientsDupStep fun c p => P (c, p)

/-- The direct grammar read with the observer `observe`. -/
def grammarLanguage {O : Type} (observe : ℕ × ℕ → O) : ObservedLanguage.{0, 0, 0, 0, 0} where
  World := ℕ × ℕ
  Statement := MeasureExpr
  Observation := O
  Dimension := ℕ
  Verdict := ℕ
  denotes := fun e s => e.eval s.1 s.2
  derivable := DirectGrammarDerivable
  observe := observe
  dimension := Prod.snd
  target := fun s => payloadSensitiveOrienter s.1 s.2
  sameContext := fun _ _ => True

/-- The projection language: strictly increasing functions of the counter. -/
def projectionLanguage : ObservedLanguage.{0, 0, 0, 0, 0} where
  World := ℕ × ℕ
  Statement := ℕ → ℕ
  Observation := ℕ
  Dimension := ℕ
  Verdict := ℕ
  denotes := fun f s => f s.1
  derivable := StrictMono
  observe := Prod.fst
  dimension := Prod.snd
  target := Prod.fst
  sameContext := fun _ _ => True

/-- (a) **With the full reading, the grammar fails the Beth property** at the payload-sensitive
orienter. -/
theorem grammar_fullReading_not_bethProperty :
    ¬ (grammarLanguage (id : ℕ × ℕ → ℕ × ℕ)).BethPropertyOn Orienting := by
  intro h
  have hlic : Licensed (id : ℕ × ℕ → ℕ × ℕ)
      (fun s => payloadSensitiveOrienter s.1 s.2) := by
    intro x y hxy
    have hxy' : x = y := hxy
    rw [hxy']
  obtain ⟨e, -, hden⟩ := h (fun s => payloadSensitiveOrienter s.1 s.2)
    payloadSensitiveOrienter_orients hlic
  apply payloadSensitiveOrienter_not_grammar_denotable
  exact ⟨e, funext fun c => funext fun p => hden (c, p)⟩

/-- (b) Every orienting grammar expression is licensed by the counter. -/
theorem grammar_counter_sound_on_orienting (e : MeasureExpr)
    (he : Orienting fun s => e.eval s.1 s.2) : Licensed (Prod.fst : ℕ × ℕ → ℕ) fun s => e.eval s.1 s.2 :=
  directGrammar_orienting_denotations_licensed_by_counter e he

/-- Every grammar expression is monotone in the counter. -/
theorem measureExpr_eval_mono_counter (e : MeasureExpr) {c c' : ℕ} (h : c ≤ c') (p : ℕ) :
    e.eval c p ≤ e.eval c' p := by
  induction e generalizing p with
  | counter => exact h
  | payload => exact le_rfl
  | const n => exact le_rfl
  | add e f ihe ihf => exact Nat.add_le_add (ihe p) (ihf p)
  | mul e f ihe ihf => exact Nat.mul_le_mul (ihe p) (ihf p)
  | max e f ihe ihf => exact max_le_max (ihe p) (ihf p)
  | smul n e ihe => exact Nat.mul_le_mul_left n (ihe p)

/-- A grammar expression vanishing at the origin at least doubles from counter `1` to counter `2`. -/
theorem measureExpr_double_step (e : MeasureExpr) (h0 : e.eval 0 0 = 0) :
    2 * e.eval 1 0 ≤ e.eval 2 0 := by
  induction e with
  | counter => norm_num [MeasureExpr.eval]
  | payload => norm_num [MeasureExpr.eval]
  | const n =>
      have h0' : n = 0 := h0
      show 2 * n ≤ n
      omega
  | add e f ihe ihf =>
      have h0' : e.eval 0 0 + f.eval 0 0 = 0 := h0
      have he0 : e.eval 0 0 = 0 := by omega
      have hf0 : f.eval 0 0 = 0 := by omega
      have he := ihe he0
      have hf := ihf hf0
      show 2 * (e.eval 1 0 + f.eval 1 0) ≤ e.eval 2 0 + f.eval 2 0
      omega
  | mul e f ihe ihf =>
      have h0' : e.eval 0 0 * f.eval 0 0 = 0 := h0
      rcases Nat.mul_eq_zero.1 h0' with he0 | hf0
      · have he := ihe he0
        have hmono := measureExpr_eval_mono_counter f (c := 1) (c' := 2) (by norm_num) 0
        show 2 * (e.eval 1 0 * f.eval 1 0) ≤ e.eval 2 0 * f.eval 2 0
        nlinarith
      · have hf := ihf hf0
        have hmono := measureExpr_eval_mono_counter e (c := 1) (c' := 2) (by norm_num) 0
        show 2 * (e.eval 1 0 * f.eval 1 0) ≤ e.eval 2 0 * f.eval 2 0
        nlinarith
  | max e f ihe ihf =>
      have h0' : Nat.max (e.eval 0 0) (f.eval 0 0) = 0 := h0
      have he0 : e.eval 0 0 = 0 :=
        le_antisymm (le_trans (le_max_left _ _) (le_of_eq h0')) (Nat.zero_le _)
      have hf0 : f.eval 0 0 = 0 :=
        le_antisymm (le_trans (le_max_right _ _) (le_of_eq h0')) (Nat.zero_le _)
      have he := ihe he0
      have hf := ihf hf0
      have hmax : 2 * Nat.max (e.eval 1 0) (f.eval 1 0) ≤
          Nat.max (2 * e.eval 1 0) (2 * f.eval 1 0) := by
        rcases le_total (e.eval 1 0) (f.eval 1 0) with hle | hle
        · have hM : (e.eval 1 0).max (f.eval 1 0) = f.eval 1 0 := max_eq_right hle
          rw [hM]
          exact le_max_right _ _
        · have hM : (e.eval 1 0).max (f.eval 1 0) = e.eval 1 0 := max_eq_left hle
          rw [hM]
          exact le_max_left _ _
      exact hmax.trans (max_le_max he hf)
  | smul n e ihe =>
      have h0' : n * e.eval 0 0 = 0 := h0
      rcases Nat.mul_eq_zero.1 h0' with hn | he0
      · rw [hn]
        show 2 * (0 * e.eval 1 0) ≤ 0 * e.eval 2 0
        simp
      · have he := ihe he0
        show 2 * (n * e.eval 1 0) ≤ n * e.eval 2 0
        nlinarith

/-- The counter rank that jumps once. -/
def bethGap (c : ℕ) : ℕ := if c = 0 then 0 else c + 1

theorem bethGap_orienting : Orienting fun s => bethGap s.1 := by
  intro c p L hL
  show bethGap c < bethGap (c + 1)
  unfold bethGap
  by_cases hc : c = 0
  · subst hc
    norm_num
  · have hc1 : c + 1 ≠ 0 := by omega
    rw [if_neg hc, if_neg hc1]
    omega

theorem bethGap_not_grammar_denotable : ¬ ∃ e : MeasureExpr, ∀ c p, e.eval c p = bethGap c := by
  rintro ⟨e, he⟩
  have h0 : e.eval 0 0 = 0 := by rw [he]; simp [bethGap]
  have hdouble := measureExpr_double_step e h0
  have h1 : e.eval 1 0 = 2 := by rw [he]; simp [bethGap]
  have h2 : e.eval 2 0 = 3 := by rw [he]; simp [bethGap]
  rw [h1, h2] at hdouble
  norm_num at hdouble

/-- (b) **With the counter as observer, the grammar still fails the Beth property.** -/
theorem grammar_counter_not_bethProperty :
    ¬ (grammarLanguage (Prod.fst : ℕ × ℕ → ℕ)).BethPropertyOn Orienting := by
  intro h
  have hlic : Licensed (Prod.fst : ℕ × ℕ → ℕ) (fun s => bethGap s.1) := by
    intro x y hxy
    show bethGap x.1 = bethGap y.1
    rw [hxy]
  obtain ⟨e, -, hden⟩ := h (fun s => bethGap s.1) bethGap_orienting hlic
  apply bethGap_not_grammar_denotable
  exact ⟨e, fun c p => hden (c, p)⟩

theorem projection_sound : projectionLanguage.Sound := by
  intro f _ x y hxy
  exact congrArg f hxy

/-- (c) **The projection language has the Beth property on orienting targets.** -/
theorem projection_bethProperty_on_orienting : projectionLanguage.BethPropertyOn Orienting := by
  intro P hP hlic
  let Pn : ℕ × ℕ → ℕ := P
  have hP' : Orienting Pn := hP
  have hlic' : Licensed projectionLanguage.observe Pn := hlic
  let f : ℕ → ℕ := fun c => Pn (c, 0)
  have hf : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro n
    show f n < f (n + 1)
    have hstep : Pn (n, 0 + 1) < Pn (n + 1, 0) := hP' n 0 1 (by norm_num)
    have hsame : Pn (n, 0) = Pn (n, 0 + 1) := hlic' (n, 0) (n, 0 + 1) rfl
    rw [show f n = Pn (n, 0) from rfl, show f (n + 1) = Pn (n + 1, 0) from rfl, hsame]
    exact hstep
  refine ⟨f, hf, fun s => ?_⟩
  show f s.1 = Pn s
  exact (hlic' s (s.1, 0) rfl).symm

theorem projection_explicitlyDefines_iff_licensed (P : ℕ × ℕ → ℕ) (hP : Orienting P) :
    projectionLanguage.ExplicitlyDefines P ↔ Licensed (Prod.fst : ℕ × ℕ → ℕ) P :=
  ⟨ObservedLanguage.licensed_of_explicitlyDefines projection_sound,
    projection_bethProperty_on_orienting P hP⟩

end OperatorKO7.Meta.OperationalInexpressibility.BethDefinabilityInstances
