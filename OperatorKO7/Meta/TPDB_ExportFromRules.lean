import OperatorKO7.Meta.TPDB_Export
import OperatorKO7.Meta.DistinctionBoundary.RuleErasureCensus
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness

set_option autoImplicit false

/-!
# TPDB exports rendered from the Lean rule objects

The two TPDB texts of `Meta/TPDB_Export.lean` are string constants. This module renders both texts
from the Lean rule objects and proves them equal to the embedded copies of the archived files
`Artifacts/ttt2/KO7_full_step.trs` and `Artifacts/ttt2/free_recursor.trs`.

* CWS. Each `RuleName` of `Meta/DistinctionBoundary/RuleErasureCensus.lean` carries a left- and a
  right-hand side pattern over the seven trace constructors (`ruleLhs`, `ruleRhs`). The instances
  of the patterns of `r` are exactly the pairs `RuleInstance r` (`ruleInstance_iff_pattern`), so
  with `step_iff_exists_rule` the root relation `Step` is exactly the instances of the rendered
  rules (`step_iff_exists_pattern`). The rules are rendered in the order of `ruleNames`, which
  lists every rule name once (`mem_ruleNames`, `ruleNames_nodup`); the `VAR` line is computed from
  the variables of the patterns. The rendered text equals `ko7_full_step_tpdb_artifact_text` and
  the exporter text `ko7_full_step_tpdb` (`ko7_full_step_tpdb_from_rules_eq_artifact`,
  `ko7_full_step_tpdb_from_rules_eq_exporter`).
* Free recursor. The rules of `freeRecursorTRS` (`zeroRule`, `succRule`) are first-order terms;
  `renderFreeTerm` renders them with the symbol names `zero`, `succ`, `wrap`, `recur` and the
  variable names `b`, `s`, `n` for `0`, `1`, `2`. The rendered text equals
  `free_recursor_tpdb_artifact_text` (`free_recursor_tpdb_from_rules_eq_artifact`).
* Parse back. `parseTpdb` reads the restricted TPDB syntax of both files (a `VAR` block and a
  `RULES` block). The embedded artifact texts parse to the declared variables and to the rule
  syntax trees rendered from the Lean rules (`parseTpdb_ko7_artifact`,
  `parseTpdb_free_recursor_artifact`), so the correspondence holds at the level of syntax trees,
  with every declared variable read as a variable and every other identifier as a symbol.

Relation: `Step` of `Kernel.lean` (root, eight rules) for CWS; the rule list `freeRecursorTRS` for
the free recursor. The TPDB files list rules; the rewrite relation of each file is the contextual
closure of its rules under full rewriting (no `STRATEGY` line).
Trust: kernel-only. Lean reads no file: the archived files are compared with the embedded copies
outside the kernel (byte comparison in the closure record and `lean_exe verifyTpdbExport`).
-/

namespace OperatorKO7.TPDBExportFromRules

open OperatorKO7.Meta.DistinctionBoundary.RuleErasureCensus
open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

/-! ## CWS rules as patterns -/

/-- Rule patterns over the seven trace constructors and natural-number pattern variables.

Proves: nothing; a syntax type.
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the left- and right-hand sides of the eight kernel rules. -/
inductive KPat : Type
  | var (i : Nat)
  | void
  | delta (p : KPat)
  | integrate (p : KPat)
  | merge (p q : KPat)
  | app (p q : KPat)
  | recD (b s n : KPat)
  | eqW (p q : KPat)

/-- Instantiation of a pattern by a valuation of its variables.

Proves: nothing; a definition.
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every valuation `Nat → Trace`. -/
def KPat.inst (ρ : Nat → Trace) : KPat → Trace
  | .var i => ρ i
  | .void => .void
  | .delta p => .delta (p.inst ρ)
  | .integrate p => .integrate (p.inst ρ)
  | .merge p q => .merge (p.inst ρ) (q.inst ρ)
  | .app p q => .app (p.inst ρ) (q.inst ρ)
  | .recD b s n => .recΔ (b.inst ρ) (s.inst ρ) (n.inst ρ)
  | .eqW p q => .eqW (p.inst ρ) (q.inst ρ)

/-- The left-hand side pattern of each named kernel rule; the variables `0`, `1`, `2` stand for
`x`, `y`, `z`.

Proves: nothing; a definition (`ruleInstance_iff_pattern` ties it to `RuleInstance`).
Does not prove: anything by itself.
Relation: `Step` (root), through `ruleInstance_iff_pattern`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: the eight names of `RuleName`. -/
def ruleLhs : RuleName → KPat
  | .R_int_delta => .integrate (.delta (.var 0))
  | .R_merge_void_left => .merge .void (.var 0)
  | .R_merge_void_right => .merge (.var 0) .void
  | .R_merge_cancel => .merge (.var 0) (.var 0)
  | .R_rec_zero => .recD (.var 0) (.var 1) .void
  | .R_rec_succ => .recD (.var 0) (.var 1) (.delta (.var 2))
  | .R_eq_refl => .eqW (.var 0) (.var 0)
  | .R_eq_diff => .eqW (.var 0) (.var 1)

/-- The right-hand side pattern of each named kernel rule.

Proves: nothing; a definition (`ruleInstance_iff_pattern` ties it to `RuleInstance`).
Does not prove: anything by itself.
Relation: `Step` (root), through `ruleInstance_iff_pattern`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: the eight names of `RuleName`. -/
def ruleRhs : RuleName → KPat
  | .R_int_delta => .void
  | .R_merge_void_left => .var 0
  | .R_merge_void_right => .var 0
  | .R_merge_cancel => .var 0
  | .R_rec_zero => .var 0
  | .R_rec_succ => .app (.var 1) (.recD (.var 0) (.var 1) (.var 2))
  | .R_eq_refl => .void
  | .R_eq_diff => .integrate (.merge (.var 0) (.var 1))

/-- The valuation sending `0`, `1`, `2` to `x`, `y`, `z` and every other variable to `void`.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the three pattern variables of the kernel rules. -/
def val3 (x y z : Trace) : Nat → Trace := fun i => [x, y, z].getD i .void

/-- The instances of the patterns of a rule name are exactly the pairs of `RuleInstance`.

Proves: `RuleInstance r t u ↔ ∃ ρ, t = (ruleLhs r).inst ρ ∧ u = (ruleRhs r).inst ρ`.
Does not prove: anything about contextual rewriting.
Relation: `RuleInstance r` (one root rule of `Step`).
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: every rule name and every pair of traces. -/
theorem ruleInstance_iff_pattern (r : RuleName) (t u : Trace) :
    RuleInstance r t u ↔ ∃ ρ : Nat → Trace, t = (ruleLhs r).inst ρ ∧ u = (ruleRhs r).inst ρ := by
  cases r with
  | R_int_delta =>
      constructor
      · rintro ⟨x, ht, hu⟩
        exact ⟨val3 x .void .void, ht, hu⟩
      · rintro ⟨ρ, rfl, rfl⟩
        exact ⟨ρ 0, rfl, rfl⟩
  | R_merge_void_left =>
      constructor
      · rintro ⟨x, ht, hu⟩
        exact ⟨val3 x .void .void, ht, hu⟩
      · rintro ⟨ρ, rfl, rfl⟩
        exact ⟨ρ 0, rfl, rfl⟩
  | R_merge_void_right =>
      constructor
      · rintro ⟨x, ht, hu⟩
        exact ⟨val3 x .void .void, ht, hu⟩
      · rintro ⟨ρ, rfl, rfl⟩
        exact ⟨ρ 0, rfl, rfl⟩
  | R_merge_cancel =>
      constructor
      · rintro ⟨x, ht, hu⟩
        exact ⟨val3 x .void .void, ht, hu⟩
      · rintro ⟨ρ, rfl, rfl⟩
        exact ⟨ρ 0, rfl, rfl⟩
  | R_rec_zero =>
      constructor
      · rintro ⟨b, s, ht, hu⟩
        exact ⟨val3 b s .void, ht, hu⟩
      · rintro ⟨ρ, rfl, rfl⟩
        exact ⟨ρ 0, ρ 1, rfl, rfl⟩
  | R_rec_succ =>
      constructor
      · rintro ⟨b, s, n, ht, hu⟩
        exact ⟨val3 b s n, ht, hu⟩
      · rintro ⟨ρ, rfl, rfl⟩
        exact ⟨ρ 0, ρ 1, ρ 2, rfl, rfl⟩
  | R_eq_refl =>
      constructor
      · rintro ⟨a, ht, hu⟩
        exact ⟨val3 a .void .void, ht, hu⟩
      · rintro ⟨ρ, rfl, rfl⟩
        exact ⟨ρ 0, rfl, rfl⟩
  | R_eq_diff =>
      constructor
      · rintro ⟨a, b, ht, hu⟩
        exact ⟨val3 a b .void, ht, hu⟩
      · rintro ⟨ρ, rfl, rfl⟩
        exact ⟨ρ 0, ρ 1, rfl, rfl⟩

/-- The root relation `Step` is exactly the set of instances of the rule patterns.

Proves: `Step t u ↔ ∃ r ρ, t = (ruleLhs r).inst ρ ∧ u = (ruleRhs r).inst ρ`.
Does not prove: anything about the contextual closure.
Relation: `Step` (the full kernel relation, eight unconditional root rules).
Closure: root.
Strategy: full.
Trust: kernel-only; `step_iff_exists_rule` of `RuleErasureCensus`.
Scope: every pair of traces. -/
theorem step_iff_exists_pattern (t u : Trace) :
    OperatorKO7.Step t u ↔ ∃ r : RuleName, ∃ ρ : Nat → Trace,
      t = (ruleLhs r).inst ρ ∧ u = (ruleRhs r).inst ρ := by
  rw [step_iff_exists_rule]
  exact exists_congr fun r => ruleInstance_iff_pattern r t u

/-- The eight rule names in the order of the exported file.

Proves: nothing; a list (`mem_ruleNames`, `ruleNames_nodup`).
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the constructors of `RuleName`. -/
def ruleNames : List RuleName :=
  [.R_int_delta, .R_merge_void_left, .R_merge_void_right, .R_merge_cancel, .R_rec_zero,
    .R_rec_succ, .R_eq_refl, .R_eq_diff]

/-- Every rule name occurs in `ruleNames`.

Proves: `∀ r, r ∈ ruleNames`.
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the constructors of `RuleName`. -/
theorem mem_ruleNames (r : RuleName) : r ∈ ruleNames := by
  cases r <;> simp [ruleNames]

/-- No rule name occurs twice in `ruleNames`.

Proves: `ruleNames.Nodup`.
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the constructors of `RuleName`. -/
theorem ruleNames_nodup : ruleNames.Nodup := by
  simp [ruleNames]

/-! ## Rendering -/

/-- The TPDB name of the pattern variables `0`, `1`, `2`: `x`, `y`, `z`.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the kernel rule patterns, which use only `0`, `1`, `2`. -/
def kVarName (i : Nat) : String := ["x", "y", "z"].getD i "w"

/-- The TPDB syntax tree of a pattern, with the symbol names of the exported file.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: rule patterns. -/
def KPat.toTpdb : KPat → TpdbTerm
  | .var i => .var (kVarName i)
  | .void => .app "void" []
  | .delta p => .app "delta" [p.toTpdb]
  | .integrate p => .app "integrate" [p.toTpdb]
  | .merge p q => .app "merge" [p.toTpdb, q.toTpdb]
  | .app p q => .app "app" [p.toTpdb, q.toTpdb]
  | .recD b s n => .app "recD" [b.toTpdb, s.toTpdb, n.toTpdb]
  | .eqW p q => .app "eqW" [p.toTpdb, q.toTpdb]

/-- The variables of a pattern, one entry per occurrence, left to right.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: rule patterns. -/
def KPat.vars : KPat → List Nat
  | .var i => [i]
  | .void => []
  | .delta p => p.vars
  | .integrate p => p.vars
  | .merge p q => p.vars ++ q.vars
  | .app p q => p.vars ++ q.vars
  | .recD b s n => b.vars ++ s.vars ++ n.vars
  | .eqW p q => p.vars ++ q.vars

/-- Appends to `seen` the entries of the list not yet in it, keeping the first occurrence.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: lists of variable indices. -/
def firstOccurrences : List Nat → List Nat → List Nat
  | seen, [] => seen
  | seen, i :: is => if i ∈ seen then firstOccurrences seen is else firstOccurrences (seen ++ [i]) is

/-- The rules of CWS rendered from the patterns, in the order of `ruleNames`.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: `Step` (root), through `step_iff_exists_pattern`.
Closure: root.
Strategy: not applicable.
Trust: kernel-only.
Scope: the eight kernel rules. -/
def cwsRenderedRules : List TpdbRule :=
  ruleNames.map fun r => ⟨(ruleLhs r).toTpdb, (ruleRhs r).toTpdb⟩

/-- The variable indices of the CWS patterns in order of first occurrence.

Proves: nothing; a definition (`cwsVarIndices_eq`).
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the eight kernel rules. -/
def cwsVarIndices : List Nat :=
  firstOccurrences [] (ruleNames.flatMap fun r => (ruleLhs r).vars ++ (ruleRhs r).vars)

/-- The CWS patterns use exactly the variables `0`, `1`, `2`, first met in that order.

Proves: `cwsVarIndices = [0, 1, 2]`.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: the eight kernel rules. -/
theorem cwsVarIndices_eq : cwsVarIndices = [0, 1, 2] := by decide

/-- The `VAR` line of a TPDB file for a list of variable names.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: TPDB text. -/
def renderVarLine (names : List String) : String :=
  "(VAR " ++ " ".intercalate names ++ ")\n"

/-- The TPDB text of CWS rendered from the rule patterns: the `VAR` line computed from the pattern
variables and the rules in the order of `ruleNames`.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: `Step` (root), through `step_iff_exists_pattern`.
Closure: root; the TPDB file denotes the contextual closure of its rules.
Strategy: full (no `STRATEGY` line).
Trust: kernel-only.
Scope: the eight kernel rules. -/
def ko7_full_step_tpdb_from_rules : String :=
  renderVarLine (cwsVarIndices.map kVarName) ++ "(RULES\n" ++ renderRuleBlock cwsRenderedRules ++
    ")\n"

/-- The rule list rendered from the patterns is the rule list of the exporter.

Proves: `cwsRenderedRules = ko7FullStepTpdbRules`.
Does not prove: anything about the archived file (see `ko7_full_step_tpdb_from_rules_eq_artifact`).
Relation: not applicable (syntax trees).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; definitional unfolding.
Scope: the eight kernel rules. -/
theorem cwsRenderedRules_eq_exporter_rules : cwsRenderedRules = ko7FullStepTpdbRules := rfl

/-- The CWS text rendered from the rule patterns equals the embedded copy of the archived file
`Artifacts/ttt2/KO7_full_step.trs`.

Proves: `ko7_full_step_tpdb_from_rules = ko7_full_step_tpdb_artifact_text`.
Does not prove: equality with the file on disk inside the kernel (checked outside Lean).
Relation: `Step` (root), through `step_iff_exists_pattern`.
Closure: root.
Strategy: full.
Trust: kernel-only; evaluation by the kernel (`decide +kernel`).
Scope: the eight kernel rules. -/
theorem ko7_full_step_tpdb_from_rules_eq_artifact :
    ko7_full_step_tpdb_from_rules = ko7_full_step_tpdb_artifact_text := by decide +kernel

/-- The CWS text rendered from the rule patterns equals the text of the exporter.

Proves: `ko7_full_step_tpdb_from_rules = ko7_full_step_tpdb`.
Does not prove: anything about other files.
Relation: `Step` (root), through `step_iff_exists_pattern`.
Closure: root.
Strategy: full.
Trust: kernel-only; evaluation by the kernel (`decide +kernel`).
Scope: the eight kernel rules. -/
theorem ko7_full_step_tpdb_from_rules_eq_exporter :
    ko7_full_step_tpdb_from_rules = ko7_full_step_tpdb := by decide +kernel

/-! ## The free recursor -/

/-- The TPDB symbol names of the free recursor.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the four free symbols. -/
def freeSymName : FreeSym → String
  | .zero => "zero"
  | .succ => "succ"
  | .wrap => "wrap"
  | .recur => "recur"

/-- The TPDB names of the variables `0`, `1`, `2` of `freeRecursorTRS`: `b`, `s`, `n`.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the variables of `zeroRule` and `succRule`. -/
def freeVarName (i : Nat) : String := ["b", "s", "n"].getD i "v"

mutual
/-- The TPDB syntax tree of a first-order term over the free symbols.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: first-order terms over the free symbols. -/
def renderFreeTerm : Term FreeSym Nat → TpdbTerm
  | .var x => .var (freeVarName x)
  | .app f args => .app (freeSymName f) (renderFreeTerms args)
/-- The TPDB syntax trees of a list of first-order terms.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: argument lists over the free symbols. -/
def renderFreeTerms : List (Term FreeSym Nat) → List TpdbTerm
  | [] => []
  | t :: ts => renderFreeTerm t :: renderFreeTerms ts
end

mutual
/-- The variables of a first-order term, one entry per occurrence, left to right.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: first-order terms over the free symbols. -/
def freeTermVars : Term FreeSym Nat → List Nat
  | .var x => [x]
  | .app _ args => freeTermsVars args
/-- The variables of a list of first-order terms, one entry per occurrence, left to right.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: argument lists over the free symbols. -/
def freeTermsVars : List (Term FreeSym Nat) → List Nat
  | [] => []
  | t :: ts => freeTermVars t ++ freeTermsVars ts
end

/-- The rules of `freeRecursorTRS` rendered as TPDB rules, in list order.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: the rule list `freeRecursorTRS`.
Closure: not applicable (a rule list).
Strategy: not applicable.
Trust: kernel-only.
Scope: `zeroRule` and `succRule`. -/
def freeRenderedRules : List TpdbRule :=
  freeRecursorTRS.map fun rule => ⟨renderFreeTerm rule.lhs, renderFreeTerm rule.rhs⟩

/-- The variables of `freeRecursorTRS` in order of first occurrence.

Proves: nothing; a definition (`freeVarIndices_eq`).
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: `zeroRule` and `succRule`. -/
def freeVarIndices : List Nat :=
  firstOccurrences [] (freeRecursorTRS.flatMap fun rule => freeTermVars rule.lhs ++ freeTermVars rule.rhs)

/-- The rules of `freeRecursorTRS` use exactly the variables `0`, `1`, `2`, first met in that
order.

Proves: `freeVarIndices = [0, 1, 2]`.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; evaluation by `decide`.
Scope: `zeroRule` and `succRule`. -/
theorem freeVarIndices_eq : freeVarIndices = [0, 1, 2] := by decide

/-- The TPDB text of the free recursor rendered from `freeRecursorTRS`.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: the rule list `freeRecursorTRS`.
Closure: the TPDB file denotes the contextual closure of its rules.
Strategy: full (no `STRATEGY` line).
Trust: kernel-only.
Scope: `zeroRule` and `succRule`. -/
def free_recursor_tpdb_from_rules : String :=
  renderVarLine (freeVarIndices.map freeVarName) ++ "(RULES\n" ++
    renderRuleBlock freeRenderedRules ++ ")\n"

/-- The rule list rendered from `freeRecursorTRS` is the rule list of the exporter.

Proves: `freeRenderedRules = freeRecursorTpdbRules`.
Does not prove: anything about the archived file (see `free_recursor_tpdb_from_rules_eq_artifact`).
Relation: not applicable (syntax trees).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; definitional unfolding.
Scope: `zeroRule` and `succRule`. -/
theorem freeRenderedRules_eq_exporter_rules : freeRenderedRules = freeRecursorTpdbRules := rfl

/-- The free-recursor text rendered from `freeRecursorTRS` equals the embedded copy of the archived
file `Artifacts/ttt2/free_recursor.trs`.

Proves: `free_recursor_tpdb_from_rules = free_recursor_tpdb_artifact_text`.
Does not prove: equality with the file on disk inside the kernel (checked outside Lean).
Relation: the rule list `freeRecursorTRS`.
Closure: not applicable.
Strategy: full.
Trust: kernel-only; evaluation by `decide`.
Scope: `zeroRule` and `succRule`. -/
theorem free_recursor_tpdb_from_rules_eq_artifact :
    free_recursor_tpdb_from_rules = free_recursor_tpdb_artifact_text := by decide

/-- The free-recursor text rendered from `freeRecursorTRS` equals the text of the exporter.

Proves: `free_recursor_tpdb_from_rules = free_recursor_tpdb`.
Does not prove: anything about other files.
Relation: the rule list `freeRecursorTRS`.
Closure: not applicable.
Strategy: full.
Trust: kernel-only; evaluation by `decide`.
Scope: `zeroRule` and `succRule`. -/
theorem free_recursor_tpdb_from_rules_eq_exporter :
    free_recursor_tpdb_from_rules = free_recursor_tpdb := by decide

/-! ## Parsing the restricted TPDB syntax back -/

mutual
/-- Structural decidable equality on TPDB terms, threaded through the argument list with
`tpdbTermListDecEq` so the nested recursion is structural.

Proves: nothing; a decision procedure (the `Decidable` value carries the proof).
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: TPDB syntax trees. -/
def tpdbTermDecEq : (s t : TpdbTerm) → Decidable (s = t)
  | .var x, .var y => if h : x = y then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .var _, .app _ _ => .isFalse (by simp)
  | .app _ _, .var _ => .isFalse (by simp)
  | .app f xs, .app g ys =>
      if hfg : f = g then
        match tpdbTermListDecEq xs ys with
        | .isTrue h => .isTrue (by rw [hfg, h])
        | .isFalse h => .isFalse (by simp [hfg, h])
      else .isFalse (by simp [hfg])
/-- Structural decidable equality on lists of TPDB terms, the list companion of `tpdbTermDecEq`.

Proves: nothing; a decision procedure.
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: argument lists of TPDB syntax trees. -/
def tpdbTermListDecEq : (xs ys : List TpdbTerm) → Decidable (xs = ys)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
  | x :: xs, y :: ys =>
      match tpdbTermDecEq x y with
      | .isTrue hx =>
          match tpdbTermListDecEq xs ys with
          | .isTrue hxs => .isTrue (by rw [hx, hxs])
          | .isFalse hxs => .isFalse (by simp [hxs])
      | .isFalse hx => .isFalse (by simp [hx])
end

/-- Decidable equality of TPDB terms, from `tpdbTermDecEq`.

Proves: nothing; an instance.
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: TPDB syntax trees; used by the parse-back theorems. -/
instance tpdbTermDecidableEq : DecidableEq TpdbTerm := tpdbTermDecEq

/-- Decidable equality of TPDB rules, field by field.

Proves: nothing; an instance.
Does not prove: anything about rewriting.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: TPDB rules; used by the parse-back theorems. -/
instance tpdbRuleDecidableEq : DecidableEq TpdbRule := fun a b =>
  match a, b with
  | ⟨l₁, r₁⟩, ⟨l₂, r₂⟩ =>
      if h₁ : l₁ = l₂ then
        if h₂ : r₁ = r₂ then .isTrue (by rw [h₁, h₂])
        else .isFalse (by intro h; cases h; exact h₂ rfl)
      else .isFalse (by intro h; cases h; exact h₁ rfl)

/-- Tokens of the restricted TPDB syntax of the two files.

Proves: nothing; a syntax type.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: identifiers, parentheses, commas and the two characters of `->`. -/
inductive TpdbToken : Type
  | ident (s : String)
  | lpar
  | rpar
  | comma
  | dash
  | gt

/-- Identifier characters: letters, digits and `_`.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: TPDB identifiers of the two files. -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Emits the identifier accumulated in reverse order, if any, in front of the remaining tokens.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the tokenizer. -/
def flushIdent (acc : List Char) (rest : List TpdbToken) : List TpdbToken :=
  if acc.isEmpty then rest else .ident (String.mk acc.reverse) :: rest

/-- Splits characters into tokens; the second argument holds the current identifier in reverse.
Spaces and line breaks separate tokens; any other character outside the token set stops the
tokenizer with `none`.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the restricted TPDB syntax. -/
def tokenize : List Char → List Char → Option (List TpdbToken)
  | [], acc => some (flushIdent acc [])
  | c :: cs, acc =>
      if isIdentChar c then tokenize cs (c :: acc)
      else
        match tokenize cs [] with
        | none => none
        | some rest =>
            if c = ' ' ∨ c = '\n' then some (flushIdent acc rest)
            else if c = '(' then some (flushIdent acc (.lpar :: rest))
            else if c = ')' then some (flushIdent acc (.rpar :: rest))
            else if c = ',' then some (flushIdent acc (.comma :: rest))
            else if c = '-' then some (flushIdent acc (.dash :: rest))
            else if c = '>' then some (flushIdent acc (.gt :: rest))
            else none

mutual
/-- Parses one term: an identifier, followed by a parenthesized comma-separated argument list for
an application. An identifier without arguments is a variable when `vars` lists it and a constant
otherwise. `fuel` bounds the recursion depth.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the restricted TPDB syntax. -/
def parseTerm (vars : List String) : Nat → List TpdbToken → Option (TpdbTerm × List TpdbToken)
  | 0, _ => none
  | fuel + 1, .ident f :: .lpar :: rest =>
      match parseArgs vars fuel rest with
      | some (args, rest') => some (.app f args, rest')
      | none => none
  | _ + 1, .ident x :: rest => some (if x ∈ vars then .var x else .app x [], rest)
  | _ + 1, _ => none
/-- Parses a comma-separated argument list up to its closing parenthesis.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the restricted TPDB syntax. -/
def parseArgs (vars : List String) : Nat → List TpdbToken → Option (List TpdbTerm × List TpdbToken)
  | 0, _ => none
  | fuel + 1, toks =>
      match parseTerm vars fuel toks with
      | some (t, .comma :: rest) =>
          match parseArgs vars fuel rest with
          | some (ts, rest') => some (t :: ts, rest')
          | none => none
      | some (t, .rpar :: rest) => some ([t], rest)
      | _ => none
end

/-- Parses the identifiers of a `VAR` block up to its closing parenthesis.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the restricted TPDB syntax. -/
def parseVarNames : List TpdbToken → Option (List String × List TpdbToken)
  | .rpar :: rest => some ([], rest)
  | .ident x :: rest =>
      match parseVarNames rest with
      | some (xs, rest') => some (x :: xs, rest')
      | none => none
  | _ => none

/-- Parses the rules `l -> r` of a `RULES` block up to its closing parenthesis.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the restricted TPDB syntax. -/
def parseRules (vars : List String) : Nat → List TpdbToken → Option (List TpdbRule × List TpdbToken)
  | 0, _ => none
  | _ + 1, .rpar :: rest => some ([], rest)
  | fuel + 1, toks =>
      match parseTerm vars fuel toks with
      | some (l, .dash :: .gt :: rest) =>
          match parseTerm vars fuel rest with
          | some (r, rest') =>
              match parseRules vars fuel rest' with
              | some (rs, rest'') => some (⟨l, r⟩ :: rs, rest'')
              | none => none
          | none => none
      | _ => none

/-- Parses a file of the restricted TPDB syntax: `(VAR ...)` then `(RULES ...)` and nothing after,
with recursion depth bounded by the number of characters.

Proves: nothing; a definition.
Does not prove: anything by itself.
Relation: not applicable.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the restricted TPDB syntax of the two exported files. -/
def parseTpdb (text : String) : Option (List String × List TpdbRule) :=
  match tokenize text.data [] with
  | some (.lpar :: .ident "VAR" :: rest) =>
      match parseVarNames rest with
      | some (vars, .lpar :: .ident "RULES" :: rest') =>
          match parseRules vars text.length rest' with
          | some (rules, []) => some (vars, rules)
          | _ => none
      | _ => none
  | _ => none

/-- The embedded copy of `Artifacts/ttt2/KO7_full_step.trs` parses to the variables `x`, `y`, `z`
and to the syntax trees of the rules rendered from the CWS patterns.

Proves: `parseTpdb ko7_full_step_tpdb_artifact_text = some (cwsVarIndices.map kVarName,
cwsRenderedRules)`.
Does not prove: correctness of `parseTpdb` on other inputs.
Relation: `Step` (root), through `step_iff_exists_pattern`.
Closure: root.
Strategy: full.
Trust: kernel-only; evaluation by the kernel (`decide +kernel`) with `tpdbRuleDecidableEq`.
Scope: the embedded copy of the archived CWS file. -/
theorem parseTpdb_ko7_artifact :
    parseTpdb ko7_full_step_tpdb_artifact_text =
      some (cwsVarIndices.map kVarName, cwsRenderedRules) := by
  decide +kernel

/-- The embedded copy of `Artifacts/ttt2/free_recursor.trs` parses to the variables `b`, `s`, `n`
and to the syntax trees of the rules rendered from `freeRecursorTRS`.

Proves: `parseTpdb free_recursor_tpdb_artifact_text = some (freeVarIndices.map freeVarName,
freeRenderedRules)`.
Does not prove: correctness of `parseTpdb` on other inputs.
Relation: the rule list `freeRecursorTRS`.
Closure: not applicable.
Strategy: full.
Trust: kernel-only; evaluation by the kernel (`decide +kernel`) with `tpdbRuleDecidableEq`.
Scope: the embedded copy of the archived free-recursor file. -/
theorem parseTpdb_free_recursor_artifact :
    parseTpdb free_recursor_tpdb_artifact_text =
      some (freeVarIndices.map freeVarName, freeRenderedRules) := by
  decide +kernel

end OperatorKO7.TPDBExportFromRules
