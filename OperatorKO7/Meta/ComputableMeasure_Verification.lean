import OperatorKO7.Meta.ComputableMeasure

/-!
# Verification Suite for ComputableMeasure

This file verifies that the computable measure handles all cases correctly.

Test categories:
1. τ monotonicity verification
2. DM order properties
3. Measure decrease for each rule
4. Edge cases and corner cases
5. Comparison with original noncomputable measure
-/

namespace OperatorKO7.MetaCM.Verification

open OperatorKO7 Trace MetaCM
open MetaSN_KO7 MetaSN_DM

/-! ## Section 1: τ Monotonicity Tests -/

-- Verify τ is monotone for all constructors except delta
theorem tau_lt_integrate (t : Trace) : tau t < tau (integrate t) := by
  simp [tau]
theorem tau_lt_merge_left (a b : Trace) : tau a < tau (merge a b) := by
  simp [tau]; omega
theorem tau_lt_merge_right (a b : Trace) : tau b < tau (merge a b) := by
  simp [tau]; omega
theorem tau_lt_app_left (a b : Trace) : tau a < tau (app a b) := by
  simp [tau]; omega
theorem tau_lt_app_right (a b : Trace) : tau b < tau (app a b) := by
  simp [tau]; omega
theorem tau_lt_recDelta_base (b s n : Trace) : tau b < tau (recΔ b s n) := by
  simp [tau]; omega
theorem tau_lt_recDelta_step (b s n : Trace) : tau s < tau (recΔ b s n) := by
  simp [tau]; omega
theorem tau_lt_recDelta_counter (b s n : Trace) : tau n < tau (recΔ b s n) := by
  simp [tau]; omega
theorem tau_lt_eqW_left (a b : Trace) : tau a < tau (eqW a b) := by
  simp [tau]; omega
theorem tau_lt_eqW_right (a b : Trace) : tau b < tau (eqW a b) := by
  simp [tau]; omega

-- Verify delta is transparent
theorem tau_delta_transparent (t : Trace) : tau (delta t) = tau t := rfl

-- Verify the required inequality for eq_diff
theorem tau_integrate_merge_lt_eqW (a b : Trace) :
    tau (integrate (merge a b)) < tau (eqW a b) := by
  simp [tau]; omega

/-! ## Section 2: Lexicographic Order Properties -/

-- Verify Lex3c is indeed well-founded
theorem wellFounded_Lex3c : WellFounded Lex3c := wf_Lex3c

-- Verify the lifting lemma works
theorem dm_lifts_to_LexDM_c {X Y : Multiset Nat} {τ₁ τ₂ : Nat} (h : DM X Y) :
    LexDM_c (X, τ₁) (Y, τ₂) := dm_to_LexDM_c_left h

/-! ## Section 3: Measure Decrease Verification -/

-- Test all 8 rules decrease the measure
section RuleTests

-- Rule 1: integrate (delta t) → void
theorem lex3c_drop_int_delta (t : Trace) :
    Lex3c (mu3c void) (mu3c (integrate (delta t))) := by
  apply drop_R_int_delta_c

-- Rule 2: merge void t → t
theorem lex3c_drop_merge_void_left (t : Trace) (hδ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge void t)) := by
  apply drop_R_merge_void_left_c
  exact hδ

-- Rule 3: merge t void → t
theorem lex3c_drop_merge_void_right (t : Trace) (hδ : deltaFlag t = 0) :
    Lex3c (mu3c t) (mu3c (merge t void)) := by
  apply drop_R_merge_void_right_c
  exact hδ

-- Rule 4: merge t t → t (duplication case!)
theorem lex3c_drop_merge_dup (t : Trace) (hδ : deltaFlag t = 0) (h0 : kappaM t = 0) :
    Lex3c (mu3c t) (mu3c (merge t t)) := by
  apply drop_R_merge_cancel_c
  exact hδ
  exact h0

-- Rule 5: recΔ b s void → b
theorem lex3c_drop_rec_zero (b s : Trace) (hδ : deltaFlag b = 0) :
    Lex3c (mu3c b) (mu3c (recΔ b s void)) := by
  apply drop_R_rec_zero_c
  exact hδ

-- Rule 6: recΔ b s (delta n) → app s (recΔ b s n)
theorem lex3c_drop_rec_succ (b s n : Trace) :
    Lex3c (mu3c (app s (recΔ b s n))) (mu3c (recΔ b s (delta n))) := by
  apply drop_R_rec_succ_c

-- Rule 7: eqW a a → void
theorem lex3c_drop_eq_refl (a : Trace) :
    Lex3c (mu3c void) (mu3c (eqW a a)) := by
  apply drop_R_eq_refl_c

-- Rule 8: eqW a b → integrate (merge a b)
theorem lex3c_drop_eq_diff (a b : Trace) :
    Lex3c (mu3c (integrate (merge a b))) (mu3c (eqW a b)) := by
  apply drop_R_eq_diff_c

end RuleTests

/-! ## Section 4: Edge Cases and Corner Cases -/

-- Deeply nested terms still decrease
theorem lex3c_drop_nested_int_delta :
    let t := delta (delta (delta void))
    Lex3c (mu3c void) (mu3c (integrate t)) := by
  apply drop_R_int_delta_c

-- Multiple deltas preserve transparency
lemma tau_delta_iterate (n : Nat) (t : Trace) : tau (delta^[n] t) = tau t := by
  induction n generalizing t with
  | zero =>
    rfl
  | succ n ih =>
    -- `f^[n+1] t = f^[n] (f t)` and `tau (delta t) = tau t` by definition.
    simpa [Function.iterate_succ, tau] using ih (t := delta t)

theorem tau_delta_iterate_void (n : Nat) : tau (delta^[n] void) = tau void := by
  simpa using tau_delta_iterate n void

-- Verify δ-flag is binary (0 or 1)
/--
`deltaFlag` is intentionally a binary phase indicator (0 or 1).

This lemma is used as a sanity check that the computable triple-lex measure does not accidentally
encode additional phases beyond the intended `recΔ _ _ (delta _)` detection.
-/
lemma deltaFlag_binary (t : Trace) : deltaFlag t = 0 ∨ deltaFlag t = 1 := by
  cases t <;> simp
  case recΔ b s n =>
    cases n <;> simp

/-! ## Section 5: SafeStep Decrease Aggregation -/

-- The master theorem works for all SafeStep constructors
theorem lex3c_drop_of_SafeStep {a b : Trace} (h : SafeStep a b) :
    Lex3c (mu3c b) (mu3c a) :=
  measure_decreases_safe_c h

-- SafeStepRev is indeed well-founded
theorem wellFounded_SafeStepRev_check : WellFounded MetaSN_KO7.SafeStepRev :=
  wf_SafeStepRev_c

/-! ## Section 6: Comparison with Noncomputable Measure -/

-- Our computable measure implies the same well-foundedness
/--
The computable development is strictly stronger in the "artifact sense":

We can derive well-foundedness of `SafeStepRev` without appealing to any noncomputable ordinal
payload, by using `wf_SafeStepRev_c` from `Meta/ComputableMeasure.lean`.
-/
theorem computable_implies_original :
    WellFounded MetaSN_KO7.SafeStepRev := by
  exact wf_SafeStepRev_c

-- Both measures agree on well-foundedness (modulo computability)
/--
A deliberately weak "equivalence" statement:

This does *not* claim the ordinal and computable measures are extensionally equal.
It only records that (i) the existence of *some* measure implies well-foundedness, and
(ii) well-foundedness implies the existence of *a* measure (choose `mu3c`).
-/
theorem measures_equivalent_wf :
    (∃ (_μ : Trace → Nat × (Multiset Nat × Nat)), WellFounded MetaSN_KO7.SafeStepRev) ↔
      WellFounded MetaSN_KO7.SafeStepRev := by
  constructor
  · intro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨mu3c, h⟩

/-! ## Section 7: Stress Tests -/

-- Large terms still work
/-- A moderately complex concrete trace used for stress-testing `tau` and `mu3c`. -/
def bigTrace : Trace :=
  recΔ (merge void void) (app void void) (delta (integrate void))

theorem tau_bigTrace_value : tau bigTrace = 3 + 2 + 1 + 1 := by
  simp [bigTrace, tau]

-- Measure works on big terms
theorem lex3c_drop_bigTrace_eqW_diag :
    Lex3c (mu3c void) (mu3c (eqW bigTrace bigTrace)) := by
  apply drop_R_eq_refl_c

/-! ## Section 8: Invariants and Properties -/

-- τ preserves structure under delta
/-- `tau` is transparent under `delta` by definition (restated as a named lemma). -/
lemma tau_delta_preserve (t : Trace) : tau (delta t) = tau t := rfl

-- κᴹ behavior under constructors (from SafeStep core)
/-- Convenience bundle of basic `kappaM` simp-facts (re-exported as a single lemma). -/
lemma kappaM_facts (a b : Trace) :
    kappaM void = 0 ∧
    kappaM (delta a) = kappaM a ∧
    kappaM (integrate a) = kappaM a ∧
    kappaM (merge a b) = kappaM a ∪ kappaM b ∧
    kappaM (app a b) = kappaM a ∪ kappaM b ∧
    kappaM (eqW a b) = kappaM a ∪ kappaM b := by
  simp [kappaM]

-- δ-flag is 1 only for recΔ _ _ (delta _)
/-- Characterization of the `deltaFlag` phase bit. -/
lemma deltaFlag_characterization (t : Trace) :
    deltaFlag t = 1 ↔ ∃ b s n, t = recΔ b s (delta n) := by
  cases t <;> simp [deltaFlag]
  case recΔ b s n =>
    cases n <;> simp

/-! ## Section 9: No Infinite Chains -/

-- Direct proof that no infinite SafeStep chain exists
/-- There is no infinite forward `SafeStep` chain, since `mu3c` strictly decreases and `Lex3c` is WF. -/
theorem no_infinite_safestep_chain :
    ¬∃ (seq : Nat → Trace), ∀ n, SafeStep (seq n) (seq (n + 1)) := by
  intro ⟨seq, h⟩
  -- The measure strictly decreases along the chain
  have dec : ∀ n, Lex3c (mu3c (seq (n + 1))) (mu3c (seq n)) := by
    intro n
    exact measure_decreases_safe_c (h n)
  -- But Lex3c is well-founded, so no infinite descending chain exists.
  exact
    (WellFounded.wellFounded_iff_no_descending_seq.1 wf_Lex3c).elim
      ⟨fun n => mu3c (seq n), dec⟩

end OperatorKO7.MetaCM.Verification
