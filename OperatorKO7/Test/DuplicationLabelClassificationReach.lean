import OperatorKO7.Meta.UniqueNormalization.DuplicationLabelClassification

/-!
# Reach and axiom check for `Meta/UniqueNormalization/DuplicationLabelClassification.lean`

Pins every public declaration, structure constructor, field and parent projection, and
inductive constructor of the paired module, each with a paired axiom query, followed by the
package controls. Baseline axioms only. -/

#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep.root
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep.root
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep.arg
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep.arg
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.ruleLabelStep_iff_step
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.ruleLabelStep_iff_step
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.ruleLabelStep_label_of_rule
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.ruleLabelStep_label_of_rule
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep.app_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep.app_inv
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep.not_var
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.RuleLabelStep.not_var
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.aT
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.aT
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.bT
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.bT
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.dupRule
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.dupRule
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atomRule
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atomRule
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.dupRules
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.dupRules
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.dup_root_step
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.dup_root_step
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_root_step
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_root_step
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.dup_step_cases
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.dup_step_cases
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.NoSym
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.NoSym
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.noSym_app_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.noSym_app_iff
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.noSym_var
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.noSym_var
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.noSym_replace
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.noSym_replace
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.noSym_arg
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.noSym_arg
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.step_noF
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.step_noF
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.step_noA
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.step_noA
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.star_noSym_two
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.star_noSym_two
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.g_step_count
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.g_step_count
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.g_vars_no_step
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.g_vars_no_step
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atomPeak
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atomPeak
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.star_below_atoms
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.star_below_atoms
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_decreasing_of_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_decreasing_of_lt
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_decreasing_imp_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_decreasing_imp_lt
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_decreasing_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_decreasing_iff
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_small_arity
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_small_arity
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.priorityLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.priorityLabel
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.priorityLabel_values
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.priorityLabel_values
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_rule_priority_repair
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.atom_peak_rule_priority_repair
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.fv
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.fv
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.gv
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.gv
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nestedPeak
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nestedPeak
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.fv_noA
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.fv_noA
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.gv_noA
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.gv_noA
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_right_step
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_right_step
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_no_low_step
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_no_low_step
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_no_either_step
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_no_either_step
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_peak_not_decreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_peak_not_decreasing
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.no_constant_rule_labeling
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.no_constant_rule_labeling
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.priority_repairs_atom_peak_only
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.priority_repairs_atom_peak_only
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.stepStar_rewrite_copies
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.stepStar_rewrite_copies
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_peak_ordinary_join
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.nested_peak_ordinary_join
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.T
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.T
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.f
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.f
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.g
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.g
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.a
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.a
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.b
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.b
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.duplicate
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.duplicate
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.atom
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.atom
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.rules
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.rules
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.zeroLabel
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.zeroLabel
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.no_label_below_zero
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.no_label_below_zero
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.star_eq_of_no_edges
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.star_eq_of_no_edges
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.zero_valley_has_optional_join
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.zero_valley_has_optional_join
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.hub_rules
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.hub_rules
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.root_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.root_iff
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.app_step_inv
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.app_step_inv
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.step_a
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.step_a
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.no_step_b
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.no_step_b
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.singleton_split
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.singleton_split
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.pair_split
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.pair_split
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.step_gaa
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.step_gaa
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.step_fb
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.step_fb
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.level_one_minimal
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.level_one_minimal
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.peak
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.peak
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.peak_not_decreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.peak_not_decreasing
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.minimalLevel_not_allLocalPeaksDecreasing
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.minimalLevel_not_allLocalPeaksDecreasing
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.app_subterm_unary_var
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.app_subterm_unary_var
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.app_subterm_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.app_subterm_constant
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.omega_heads
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.omega_heads
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.rules_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.rules_nonOmegaOverlapping
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.rules_rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.rules_rhsDetermined
#check @OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.no_universal_minimalLevel_closeout
#print axioms OperatorKO7.Meta.UniqueNormalization.MinimalLevelDuplication.no_universal_minimalLevel_closeout
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.minimum_level_refutation_preserved
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.minimum_level_refutation_preserved
#check @OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.minimalLevel_rules_eq_dupRules
#print axioms OperatorKO7.Meta.UniqueNormalization.DuplicationLabels.minimalLevel_rules_eq_dupRules

open OperatorKO7.Meta.Rewriting OperatorKO7.Meta.UniqueNormalization OperatorKO7.Meta.UniqueNormalization.DuplicationLabels

/-! Controls: the priority repair at sample copy counts, the labeling obstruction for the
priority labels, the small-arity valley for an arbitrary labeling, and the landed system. -/

example : (atomPeak 2 priorityLabel).Decreasing (fun m n : Nat => m < n) :=
  atom_peak_rule_priority_repair 2

example : ¬ AllLocalPeaksDecreasing (RuleLabelStep (dupRules 3) priorityLabel)
    (fun m n : Nat => m < n) :=
  no_constant_rule_labeling (r := 3) (by decide) (fun m n : Nat => m < n)
    (fun l => Nat.lt_irrefl l) priorityLabel

example (lab : Rule Nat Nat → Nat) : (atomPeak 1 lab).Decreasing (fun m n : Nat => m < n) :=
  (atom_peak_small_arity lab (fun m n : Nat => m < n)).2

example : MinimalLevelDuplication.rules = dupRules 2 := minimalLevel_rules_eq_dupRules

example : joinable (dupRules 2) (.app 1 (List.replicate 2 fv)) (.app 0 [gv 2]) :=
  (nested_peak_ordinary_join 2).2.2
