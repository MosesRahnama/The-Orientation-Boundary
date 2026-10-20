import OperatorKO7.QEC.Codes.Abstention

set_option autoImplicit false

/-!
# Branch evidence and calibrated-confidence bounds

This module maps the Y/N/U/H decisions to correction, identity, undecidable, and halt branches, and associates an evidence proposition with each branch. `DecisionLicensed` states whether the predicate for the selected branch holds; it does not alter the `Abstention.decide` function.

For Y/N outputs, the decoder threshold `tauY` bounds the complement of the corresponding posterior by `1 - tauY`. Under the calibrated-confidence interpretation, this complement is an error proxy. The per-decision and cohort theorems use this threshold condition and do not require a `QECBranchEvidence` witness.
-/

namespace QEC.Codes.BranchLicense

open QEC.Codes.Abstention

/-- The branch selected by a QEC typed decoder output. -/
inductive QECBranch where
  | correction
  | identity
  | undecidable
  | halt
  deriving DecidableEq, Repr

/-- The branch selected by a Y/N/U/H decision. -/
def branchOfDecision : AbstentionDecision → QECBranch
  | .Y => .correction
  | .N => .identity
  | .U => .undecidable
  | .H => .halt

/-- A record associating each branch with its evidence proposition. The decoder does not read this record; `DecisionLicensed` checks whether the selected branch's proposition holds. Concrete propositions may represent syndrome evidence, a Knill-Laflamme condition, posterior confidence, or a resource halt log. -/
structure QECBranchEvidence : Type where
  correctionLicensed : Prop
  identityLicensed : Prop
  undecidableLicensed : Prop
  haltLicensed : Prop

/-- A branch is licensed exactly when its evidence predicate is present. -/
def BranchLicensed (E : QECBranchEvidence) : QECBranch → Prop
  | .correction => E.correctionLicensed
  | .identity => E.identityLicensed
  | .undecidable => E.undecidableLicensed
  | .halt => E.haltLicensed

/-- A decision is licensed exactly when the evidence predicate for its mapped branch holds. -/
def DecisionLicensed (E : QECBranchEvidence) (d : AbstentionDecision) : Prop :=
  BranchLicensed E (branchOfDecision d)

/-- If `DecisionLicensed E .Y` holds, then `E.correctionLicensed` holds. -/
theorem correction_decision_requires_license
    (E : QECBranchEvidence) (h : DecisionLicensed E .Y) :
    E.correctionLicensed :=
  h

/-- If `DecisionLicensed E .N` holds, then `E.identityLicensed` holds. -/
theorem identity_decision_requires_license
    (E : QECBranchEvidence) (h : DecisionLicensed E .N) :
    E.identityLicensed :=
  h

/-- If `DecisionLicensed E .U` holds, then `E.undecidableLicensed` holds. -/
theorem undecidable_decision_requires_license
    (E : QECBranchEvidence) (h : DecisionLicensed E .U) :
    E.undecidableLicensed :=
  h

/-- If `DecisionLicensed E .H` holds, then `E.haltLicensed` holds. -/
theorem halt_decision_requires_license
    (E : QECBranchEvidence) (h : DecisionLicensed E .H) :
    E.haltLicensed :=
  h

private theorem tauY_pos (decoder : AbstentionDecoder) : 0 < decoder.tauY :=
  lt_trans decoder.tauU_pos decoder.tauU_lt_tauY

/-- The in-code posterior selects the identity branch. -/
theorem inCodePosterior_selects_identity (decoder : AbstentionDecoder) :
    Abstention.decide decoder inCodePosterior = .N := by
  have htauY_pos : 0 < decoder.tauY := tauY_pos decoder
  unfold Abstention.decide inCodePosterior
  simp [htauY_pos.not_ge, decoder.tauY_le_one]

/-- The outside-code posterior selects the halt branch. -/
theorem outOfCodePosterior_selects_halt (decoder : AbstentionDecoder) :
    Abstention.decide decoder outOfCodePosterior = .H := by
  have htauY_pos : 0 < decoder.tauY := tauY_pos decoder
  unfold Abstention.decide outOfCodePosterior
  simp [htauY_pos.not_ge, decoder.tauU_pos.not_ge]

/-- A concrete identity-license packet for the in-code posterior. -/
def identityEvidence : QECBranchEvidence where
  correctionLicensed := False
  identityLicensed := True
  undecidableLicensed := False
  haltLicensed := False

/-- A concrete halt-license packet for the outside-code posterior. -/
def haltEvidence : QECBranchEvidence where
  correctionLicensed := False
  identityLicensed := False
  undecidableLicensed := False
  haltLicensed := True

/-- The in-code posterior emits a licensed identity branch. -/
theorem inCodePosterior_emits_licensed_identity
    (decoder : AbstentionDecoder) :
    DecisionLicensed identityEvidence (Abstention.decide decoder inCodePosterior) := by
  rw [inCodePosterior_selects_identity]
  trivial

/-- The outside-code posterior emits a licensed halt branch. -/
theorem outOfCodePosterior_emits_licensed_halt
    (decoder : AbstentionDecoder) :
    DecisionLicensed haltEvidence (Abstention.decide decoder outOfCodePosterior) := by
  rw [outOfCodePosterior_selects_halt]
  trivial

/-- The in-code posterior selects N with identity evidence, and the outside-code posterior selects H with halt evidence. -/
theorem qec_branch_license_nonvacuous
    (decoder : AbstentionDecoder) :
    DecisionLicensed identityEvidence (Abstention.decide decoder inCodePosterior)
      ∧ DecisionLicensed haltEvidence (Abstention.decide decoder outOfCodePosterior) :=
  ⟨inCodePosterior_emits_licensed_identity decoder,
    outOfCodePosterior_emits_licensed_halt decoder⟩

/-! ## Confidence-complement bound for accepted decisions

Under the calibrated-confidence interpretation, one minus the accepted posterior is the error proxy. The Y/N threshold implies that this complement is at most `1 - tauY`. The following theorems apply to decisions selected as Y or N; they do not use `QECBranchEvidence` predicates.
-/

/-- The confidence backing a Y or N decision: the maximum-likelihood posterior for the correction
branch Y, the identity posterior for the identity branch N. The U and H branches carry no accepted
confidence. -/
def acceptedConfidence (p : CalibratedPosterior) : AbstentionDecision → ℝ
  | .Y => p.mlPosterior
  | .N => p.identityPosterior
  | .U => 0
  | .H => 0

/-- Acceptance gate (correction): a Y decision forces its ml posterior to reach `tauY`. -/
theorem decideY_ge_tauY (decoder : AbstentionDecoder) (p : CalibratedPosterior)
    (h : Abstention.decide decoder p = .Y) : decoder.tauY ≤ p.mlPosterior := by
  unfold Abstention.decide at h
  split_ifs at h with h1 h2 h3
  exact h1

/-- Acceptance gate (identity): an N decision forces its identity posterior to reach `tauY`. -/
theorem decideN_ge_tauY (decoder : AbstentionDecoder) (p : CalibratedPosterior)
    (h : Abstention.decide decoder p = .N) : decoder.tauY ≤ p.identityPosterior := by
  unfold Abstention.decide at h
  split_ifs at h with h1 h2 h3
  exact h2

/-- For a Y or N decision, the complement of the accepted posterior is at most `1 - tauY`. Under the calibrated-confidence interpretation, this gives the per-decision error bound. -/
theorem accepted_error_le (decoder : AbstentionDecoder) (p : CalibratedPosterior)
    (h : Abstention.decide decoder p = .Y ∨ Abstention.decide decoder p = .N) :
    1 - acceptedConfidence p (Abstention.decide decoder p) ≤ 1 - decoder.tauY := by
  rcases h with hY | hN
  · rw [hY]; simp only [acceptedConfidence]
    linarith [decideY_ge_tauY decoder p hY]
  · rw [hN]; simp only [acceptedConfidence]
    linarith [decideN_ge_tauY decoder p hN]

/-- For a finite cohort of Y/N decisions with nonnegative weights, the weighted sum of accepted-posterior complements is at most `1 - tauY` times the total weight. Under the calibrated-confidence interpretation, this bounds weighted error. -/
theorem accepted_cohort_error_le {Ω : Type*} (decoder : AbstentionDecoder)
    (cohort : Finset Ω) (p : Ω → CalibratedPosterior) (weight : Ω → ℝ)
    (hw : ∀ ω ∈ cohort, 0 ≤ weight ω)
    (haccept : ∀ ω ∈ cohort,
      Abstention.decide decoder (p ω) = .Y ∨ Abstention.decide decoder (p ω) = .N) :
    (∑ ω ∈ cohort, weight ω *
        (1 - acceptedConfidence (p ω) (Abstention.decide decoder (p ω))))
      ≤ (1 - decoder.tauY) * ∑ ω ∈ cohort, weight ω := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω hω
  have herr := accepted_error_le decoder (p ω) (haccept ω hω)
  have hwω := hw ω hω
  nlinarith [herr, hwω]

/-- For a finite cohort of Y/N decisions with nonnegative weights and positive total weight, the weighted mean of accepted-posterior complements is at most `1 - tauY`. Under the calibrated-confidence interpretation, this bounds mean error. -/
theorem accepted_cohort_mean_error_le {Ω : Type*} (decoder : AbstentionDecoder)
    (cohort : Finset Ω) (p : Ω → CalibratedPosterior) (weight : Ω → ℝ)
    (hw : ∀ ω ∈ cohort, 0 ≤ weight ω)
    (hpos : 0 < ∑ ω ∈ cohort, weight ω)
    (haccept : ∀ ω ∈ cohort,
      Abstention.decide decoder (p ω) = .Y ∨ Abstention.decide decoder (p ω) = .N) :
    (∑ ω ∈ cohort, weight ω *
        (1 - acceptedConfidence (p ω) (Abstention.decide decoder (p ω))))
      / (∑ ω ∈ cohort, weight ω) ≤ 1 - decoder.tauY := by
  rw [div_le_iff₀ hpos]
  exact accepted_cohort_error_le decoder cohort p weight hw haccept

/-- The in-code posterior selects N with identity confidence one, so its confidence complement is zero and satisfies the per-decision bound. -/
theorem accepted_error_witness (decoder : AbstentionDecoder) :
    1 - acceptedConfidence inCodePosterior (Abstention.decide decoder inCodePosterior)
      ≤ 1 - decoder.tauY :=
  accepted_error_le decoder inCodePosterior (Or.inr (inCodePosterior_selects_identity decoder))

#print axioms correction_decision_requires_license
#print axioms identity_decision_requires_license
#print axioms inCodePosterior_selects_identity
#print axioms outOfCodePosterior_selects_halt
#print axioms qec_branch_license_nonvacuous
#print axioms decideY_ge_tauY
#print axioms decideN_ge_tauY
#print axioms accepted_error_le
#print axioms accepted_cohort_error_le
#print axioms accepted_cohort_mean_error_le
#print axioms accepted_error_witness

end QEC.Codes.BranchLicense
