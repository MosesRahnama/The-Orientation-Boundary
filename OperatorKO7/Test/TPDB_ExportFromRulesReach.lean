import OperatorKO7.Meta.TPDB_ExportFromRules

/-! # TPDB_ExportFromRules reach and axiom check

Paired `#check @` and `#print axioms` for every public declaration of
`OperatorKO7/Meta/TPDB_ExportFromRules.lean`: the CWS rule patterns tied to `Step`, the texts
rendered from the Lean rules, their equality with the embedded copies of the archived files, and
the parse of those copies back to the rendered syntax trees.
-/

set_option autoImplicit false

#check @OperatorKO7.TPDBExportFromRules.KPat
#print axioms OperatorKO7.TPDBExportFromRules.KPat
#check @OperatorKO7.TPDBExportFromRules.KPat.var
#print axioms OperatorKO7.TPDBExportFromRules.KPat.var
#check @OperatorKO7.TPDBExportFromRules.KPat.void
#print axioms OperatorKO7.TPDBExportFromRules.KPat.void
#check @OperatorKO7.TPDBExportFromRules.KPat.delta
#print axioms OperatorKO7.TPDBExportFromRules.KPat.delta
#check @OperatorKO7.TPDBExportFromRules.KPat.integrate
#print axioms OperatorKO7.TPDBExportFromRules.KPat.integrate
#check @OperatorKO7.TPDBExportFromRules.KPat.merge
#print axioms OperatorKO7.TPDBExportFromRules.KPat.merge
#check @OperatorKO7.TPDBExportFromRules.KPat.app
#print axioms OperatorKO7.TPDBExportFromRules.KPat.app
#check @OperatorKO7.TPDBExportFromRules.KPat.recD
#print axioms OperatorKO7.TPDBExportFromRules.KPat.recD
#check @OperatorKO7.TPDBExportFromRules.KPat.eqW
#print axioms OperatorKO7.TPDBExportFromRules.KPat.eqW
#check @OperatorKO7.TPDBExportFromRules.KPat.inst
#print axioms OperatorKO7.TPDBExportFromRules.KPat.inst
#check @OperatorKO7.TPDBExportFromRules.ruleLhs
#print axioms OperatorKO7.TPDBExportFromRules.ruleLhs
#check @OperatorKO7.TPDBExportFromRules.ruleRhs
#print axioms OperatorKO7.TPDBExportFromRules.ruleRhs
#check @OperatorKO7.TPDBExportFromRules.val3
#print axioms OperatorKO7.TPDBExportFromRules.val3
#check @OperatorKO7.TPDBExportFromRules.ruleInstance_iff_pattern
#print axioms OperatorKO7.TPDBExportFromRules.ruleInstance_iff_pattern
#check @OperatorKO7.TPDBExportFromRules.step_iff_exists_pattern
#print axioms OperatorKO7.TPDBExportFromRules.step_iff_exists_pattern
#check @OperatorKO7.TPDBExportFromRules.ruleNames
#print axioms OperatorKO7.TPDBExportFromRules.ruleNames
#check @OperatorKO7.TPDBExportFromRules.mem_ruleNames
#print axioms OperatorKO7.TPDBExportFromRules.mem_ruleNames
#check @OperatorKO7.TPDBExportFromRules.ruleNames_nodup
#print axioms OperatorKO7.TPDBExportFromRules.ruleNames_nodup
#check @OperatorKO7.TPDBExportFromRules.kVarName
#print axioms OperatorKO7.TPDBExportFromRules.kVarName
#check @OperatorKO7.TPDBExportFromRules.KPat.toTpdb
#print axioms OperatorKO7.TPDBExportFromRules.KPat.toTpdb
#check @OperatorKO7.TPDBExportFromRules.KPat.vars
#print axioms OperatorKO7.TPDBExportFromRules.KPat.vars
#check @OperatorKO7.TPDBExportFromRules.firstOccurrences
#print axioms OperatorKO7.TPDBExportFromRules.firstOccurrences
#check @OperatorKO7.TPDBExportFromRules.cwsRenderedRules
#print axioms OperatorKO7.TPDBExportFromRules.cwsRenderedRules
#check @OperatorKO7.TPDBExportFromRules.cwsVarIndices
#print axioms OperatorKO7.TPDBExportFromRules.cwsVarIndices
#check @OperatorKO7.TPDBExportFromRules.cwsVarIndices_eq
#print axioms OperatorKO7.TPDBExportFromRules.cwsVarIndices_eq
#check @OperatorKO7.TPDBExportFromRules.renderVarLine
#print axioms OperatorKO7.TPDBExportFromRules.renderVarLine
#check @OperatorKO7.TPDBExportFromRules.ko7_full_step_tpdb_from_rules
#print axioms OperatorKO7.TPDBExportFromRules.ko7_full_step_tpdb_from_rules
#check @OperatorKO7.TPDBExportFromRules.cwsRenderedRules_eq_exporter_rules
#print axioms OperatorKO7.TPDBExportFromRules.cwsRenderedRules_eq_exporter_rules
#check @OperatorKO7.TPDBExportFromRules.ko7_full_step_tpdb_from_rules_eq_artifact
#print axioms OperatorKO7.TPDBExportFromRules.ko7_full_step_tpdb_from_rules_eq_artifact
#check @OperatorKO7.TPDBExportFromRules.ko7_full_step_tpdb_from_rules_eq_exporter
#print axioms OperatorKO7.TPDBExportFromRules.ko7_full_step_tpdb_from_rules_eq_exporter
#check @OperatorKO7.TPDBExportFromRules.freeSymName
#print axioms OperatorKO7.TPDBExportFromRules.freeSymName
#check @OperatorKO7.TPDBExportFromRules.freeVarName
#print axioms OperatorKO7.TPDBExportFromRules.freeVarName
#check @OperatorKO7.TPDBExportFromRules.renderFreeTerm
#print axioms OperatorKO7.TPDBExportFromRules.renderFreeTerm
#check @OperatorKO7.TPDBExportFromRules.renderFreeTerms
#print axioms OperatorKO7.TPDBExportFromRules.renderFreeTerms
#check @OperatorKO7.TPDBExportFromRules.freeTermVars
#print axioms OperatorKO7.TPDBExportFromRules.freeTermVars
#check @OperatorKO7.TPDBExportFromRules.freeTermsVars
#print axioms OperatorKO7.TPDBExportFromRules.freeTermsVars
#check @OperatorKO7.TPDBExportFromRules.freeRenderedRules
#print axioms OperatorKO7.TPDBExportFromRules.freeRenderedRules
#check @OperatorKO7.TPDBExportFromRules.freeVarIndices
#print axioms OperatorKO7.TPDBExportFromRules.freeVarIndices
#check @OperatorKO7.TPDBExportFromRules.freeVarIndices_eq
#print axioms OperatorKO7.TPDBExportFromRules.freeVarIndices_eq
#check @OperatorKO7.TPDBExportFromRules.free_recursor_tpdb_from_rules
#print axioms OperatorKO7.TPDBExportFromRules.free_recursor_tpdb_from_rules
#check @OperatorKO7.TPDBExportFromRules.freeRenderedRules_eq_exporter_rules
#print axioms OperatorKO7.TPDBExportFromRules.freeRenderedRules_eq_exporter_rules
#check @OperatorKO7.TPDBExportFromRules.free_recursor_tpdb_from_rules_eq_artifact
#print axioms OperatorKO7.TPDBExportFromRules.free_recursor_tpdb_from_rules_eq_artifact
#check @OperatorKO7.TPDBExportFromRules.free_recursor_tpdb_from_rules_eq_exporter
#print axioms OperatorKO7.TPDBExportFromRules.free_recursor_tpdb_from_rules_eq_exporter
#check @OperatorKO7.TPDBExportFromRules.tpdbTermDecEq
#print axioms OperatorKO7.TPDBExportFromRules.tpdbTermDecEq
#check @OperatorKO7.TPDBExportFromRules.tpdbTermListDecEq
#print axioms OperatorKO7.TPDBExportFromRules.tpdbTermListDecEq
#check @OperatorKO7.TPDBExportFromRules.tpdbTermDecidableEq
#print axioms OperatorKO7.TPDBExportFromRules.tpdbTermDecidableEq
#check @OperatorKO7.TPDBExportFromRules.tpdbRuleDecidableEq
#print axioms OperatorKO7.TPDBExportFromRules.tpdbRuleDecidableEq
#check @OperatorKO7.TPDBExportFromRules.TpdbToken
#print axioms OperatorKO7.TPDBExportFromRules.TpdbToken
#check @OperatorKO7.TPDBExportFromRules.TpdbToken.ident
#print axioms OperatorKO7.TPDBExportFromRules.TpdbToken.ident
#check @OperatorKO7.TPDBExportFromRules.TpdbToken.lpar
#print axioms OperatorKO7.TPDBExportFromRules.TpdbToken.lpar
#check @OperatorKO7.TPDBExportFromRules.TpdbToken.rpar
#print axioms OperatorKO7.TPDBExportFromRules.TpdbToken.rpar
#check @OperatorKO7.TPDBExportFromRules.TpdbToken.comma
#print axioms OperatorKO7.TPDBExportFromRules.TpdbToken.comma
#check @OperatorKO7.TPDBExportFromRules.TpdbToken.dash
#print axioms OperatorKO7.TPDBExportFromRules.TpdbToken.dash
#check @OperatorKO7.TPDBExportFromRules.TpdbToken.gt
#print axioms OperatorKO7.TPDBExportFromRules.TpdbToken.gt
#check @OperatorKO7.TPDBExportFromRules.isIdentChar
#print axioms OperatorKO7.TPDBExportFromRules.isIdentChar
#check @OperatorKO7.TPDBExportFromRules.flushIdent
#print axioms OperatorKO7.TPDBExportFromRules.flushIdent
#check @OperatorKO7.TPDBExportFromRules.tokenize
#print axioms OperatorKO7.TPDBExportFromRules.tokenize
#check @OperatorKO7.TPDBExportFromRules.parseTerm
#print axioms OperatorKO7.TPDBExportFromRules.parseTerm
#check @OperatorKO7.TPDBExportFromRules.parseArgs
#print axioms OperatorKO7.TPDBExportFromRules.parseArgs
#check @OperatorKO7.TPDBExportFromRules.parseVarNames
#print axioms OperatorKO7.TPDBExportFromRules.parseVarNames
#check @OperatorKO7.TPDBExportFromRules.parseRules
#print axioms OperatorKO7.TPDBExportFromRules.parseRules
#check @OperatorKO7.TPDBExportFromRules.parseTpdb
#print axioms OperatorKO7.TPDBExportFromRules.parseTpdb
#check @OperatorKO7.TPDBExportFromRules.parseTpdb_ko7_artifact
#print axioms OperatorKO7.TPDBExportFromRules.parseTpdb_ko7_artifact
#check @OperatorKO7.TPDBExportFromRules.parseTpdb_free_recursor_artifact
#print axioms OperatorKO7.TPDBExportFromRules.parseTpdb_free_recursor_artifact
