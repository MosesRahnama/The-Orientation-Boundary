import OperatorKO7.Meta.TPDB_Export

/-!
Tiny smoke test for the KO7 TPDB exporter.

Why this file exists:
- Prints the exported full-step TRS so reviewers can regenerate the external
  TTT2 input directly from Lean.
- Checks the exact-match theorem on the generated text.
- Like `Test/Sanity.lean`, this is lightweight and does not contribute to the
  theorem development itself.
-/

#eval IO.println OperatorKO7.ko7_full_step_tpdb
#check OperatorKO7.ko7_full_step_tpdb_matches_artifact_text
#eval IO.println OperatorKO7.free_recursor_tpdb
#check OperatorKO7.free_recursor_tpdb_matches_artifact_text

/-! Paired `#check @` and `#print axioms` for every public declaration of
`OperatorKO7/Meta/TPDB_Export.lean`; the text rendered from the Lean rule objects is checked in
`Test/TPDB_ExportFromRulesReach.lean`. -/

#check @OperatorKO7.TpdbTerm
#print axioms OperatorKO7.TpdbTerm
#check @OperatorKO7.TpdbTerm.var
#print axioms OperatorKO7.TpdbTerm.var
#check @OperatorKO7.TpdbTerm.app
#print axioms OperatorKO7.TpdbTerm.app
#check @OperatorKO7.TpdbRule
#print axioms OperatorKO7.TpdbRule
#check @OperatorKO7.TpdbRule.mk
#print axioms OperatorKO7.TpdbRule.mk
#check @OperatorKO7.TpdbRule.lhs
#print axioms OperatorKO7.TpdbRule.lhs
#check @OperatorKO7.TpdbRule.rhs
#print axioms OperatorKO7.TpdbRule.rhs
#check @OperatorKO7.TpdbTerm.render
#print axioms OperatorKO7.TpdbTerm.render
#check @OperatorKO7.TpdbTerm.renderTail
#print axioms OperatorKO7.TpdbTerm.renderTail
#check @OperatorKO7.TpdbRule.render
#print axioms OperatorKO7.TpdbRule.render
#check @OperatorKO7.renderRuleBlock
#print axioms OperatorKO7.renderRuleBlock
#check @OperatorKO7.tx
#print axioms OperatorKO7.tx
#check @OperatorKO7.ty
#print axioms OperatorKO7.ty
#check @OperatorKO7.tz
#print axioms OperatorKO7.tz
#check @OperatorKO7.tvoid
#print axioms OperatorKO7.tvoid
#check @OperatorKO7.tdelta
#print axioms OperatorKO7.tdelta
#check @OperatorKO7.tintegrate
#print axioms OperatorKO7.tintegrate
#check @OperatorKO7.tmerge
#print axioms OperatorKO7.tmerge
#check @OperatorKO7.tapp
#print axioms OperatorKO7.tapp
#check @OperatorKO7.trecD
#print axioms OperatorKO7.trecD
#check @OperatorKO7.teqW
#print axioms OperatorKO7.teqW
#check @OperatorKO7.ko7FullStepTpdbRules
#print axioms OperatorKO7.ko7FullStepTpdbRules
#check @OperatorKO7.ko7_full_step_tpdb
#print axioms OperatorKO7.ko7_full_step_tpdb
#check @OperatorKO7.ko7_full_step_tpdb_embedded_reference
#print axioms OperatorKO7.ko7_full_step_tpdb_embedded_reference
#check @OperatorKO7.ko7_full_step_tpdb_artifact_text
#print axioms OperatorKO7.ko7_full_step_tpdb_artifact_text
#check @OperatorKO7.ko7_full_step_tpdb_matches_embedded_reference
#print axioms OperatorKO7.ko7_full_step_tpdb_matches_embedded_reference
#check @OperatorKO7.ko7_full_step_tpdb_matches_artifact_text
#print axioms OperatorKO7.ko7_full_step_tpdb_matches_artifact_text
#check @OperatorKO7.ko7_full_step_tpdb_rule_count
#print axioms OperatorKO7.ko7_full_step_tpdb_rule_count
#check @OperatorKO7.tb
#print axioms OperatorKO7.tb
#check @OperatorKO7.ts
#print axioms OperatorKO7.ts
#check @OperatorKO7.tn
#print axioms OperatorKO7.tn
#check @OperatorKO7.tzero
#print axioms OperatorKO7.tzero
#check @OperatorKO7.tsucc
#print axioms OperatorKO7.tsucc
#check @OperatorKO7.twrap
#print axioms OperatorKO7.twrap
#check @OperatorKO7.trecur
#print axioms OperatorKO7.trecur
#check @OperatorKO7.freeRecursorTpdbRules
#print axioms OperatorKO7.freeRecursorTpdbRules
#check @OperatorKO7.free_recursor_tpdb
#print axioms OperatorKO7.free_recursor_tpdb
#check @OperatorKO7.free_recursor_tpdb_embedded_reference
#print axioms OperatorKO7.free_recursor_tpdb_embedded_reference
#check @OperatorKO7.free_recursor_tpdb_artifact_text
#print axioms OperatorKO7.free_recursor_tpdb_artifact_text
#check @OperatorKO7.free_recursor_tpdb_matches_embedded_reference
#print axioms OperatorKO7.free_recursor_tpdb_matches_embedded_reference
#check @OperatorKO7.free_recursor_tpdb_matches_artifact_text
#print axioms OperatorKO7.free_recursor_tpdb_matches_artifact_text
#check @OperatorKO7.free_recursor_tpdb_rule_count
#print axioms OperatorKO7.free_recursor_tpdb_rule_count
