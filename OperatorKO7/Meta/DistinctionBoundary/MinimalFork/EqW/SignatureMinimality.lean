import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.EqW.Syntax

/-!
# Declared grammar minimality

This file proves finite-role lower bounds. It does **not** put a `Fintype`
instance on the recursive term carrier `MiniEqWTerm`.

* role-collapsed comparator: equal verdict, different verdict, query = 3 roles;
* role-separated comparator: two input roles + two verdict roles + query = 5;
* two-verdict root architecture: two distinct declared rule identifiers = 2.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

universe u

/-- A finite role-collapsed comparator signature. -/
structure ComparatorSignature where
  Sym : Type u
  eqVerdict : Sym
  diffVerdict : Sym
  query : Sym
  eq_ne_diff : eqVerdict ≠ diffVerdict
  eq_ne_query : eqVerdict ≠ query
  diff_ne_query : diffVerdict ≠ query

/-- Roadmap-stable name for the role-collapsed comparator signature. -/
abbrev RoleCollapsedComparatorSignature := ComparatorSignature

/-- Three pairwise distinct designated roles force at least three symbols. -/
theorem comparatorSignature_card_ge_three
    (S : ComparatorSignature.{u}) [Fintype S.Sym] [DecidableEq S.Sym] :
    3 ≤ Fintype.card S.Sym := by
  have hcard : ({S.eqVerdict, S.diffVerdict, S.query} : Finset S.Sym).card = 3 := by
    simp [S.eq_ne_diff, S.eq_ne_query, S.diff_ne_query]
  calc
    3 = ({S.eqVerdict, S.diffVerdict, S.query} : Finset S.Sym).card := hcard.symm
    _ ≤ (Finset.univ : Finset S.Sym).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card S.Sym := Finset.card_univ

/-- Roadmap-stable role-collapsed lower bound. This is a declared-grammar
minimum, not a classification of arbitrary nonconfluent TRSs. -/
theorem roleCollapsed_symbols_ge_three
    (S : RoleCollapsedComparatorSignature.{u})
    [Fintype S.Sym] [DecidableEq S.Sym] :
    3 ≤ Fintype.card S.Sym :=
  comparatorSignature_card_ge_three S

/-- Exact three-role witness. -/
inductive ComparatorRole3 where
  | eqVerdict
  | diffVerdict
  | query
  deriving DecidableEq, Fintype, Repr

/-- Attainment witness for the role-collapsed lower bound. -/
def comparatorRole3Signature : ComparatorSignature where
  Sym := ComparatorRole3
  eqVerdict := .eqVerdict
  diffVerdict := .diffVerdict
  query := .query
  eq_ne_diff := by intro h; cases h
  eq_ne_query := by intro h; cases h
  diff_ne_query := by intro h; cases h

/-- The three-role witness has exactly three symbols. -/
theorem comparatorRole3_card_eq_three :
    Fintype.card ComparatorRole3 = 3 := by decide

/-- The role-collapsed lower bound is sharp. -/
theorem comparatorSignature_three_is_minimal :
    Fintype.card ComparatorRole3 = 3 ∧
      ∀ (S : ComparatorSignature) [Fintype S.Sym] [DecidableEq S.Sym],
        3 ≤ Fintype.card S.Sym :=
  ⟨comparatorRole3_card_eq_three, fun S => comparatorSignature_card_ge_three S⟩

/-- Role-separated comparator signature. The `roles_nodup` certificate is the
complete finite pairwise-distinctness assertion for all five named roles. -/
structure RoleSeparatedComparatorSignature where
  Sym : Type u
  base0 : Sym
  base1 : Sym
  eqVerdict : Sym
  diffVerdict : Sym
  query : Sym
  roles_nodup : [base0, base1, eqVerdict, diffVerdict, query].Nodup

/-- Five pairwise distinct designated roles force at least five symbols. -/
theorem roleSeparated_card_ge_five
    (S : RoleSeparatedComparatorSignature.{u})
    [Fintype S.Sym] [DecidableEq S.Sym] :
    5 ≤ Fintype.card S.Sym := by
  let roles : List S.Sym :=
    [S.base0, S.base1, S.eqVerdict, S.diffVerdict, S.query]
  have hnodup : roles.Nodup := S.roles_nodup
  have hlen : roles.length = 5 := rfl
  have hcard : roles.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  calc
    5 = roles.toFinset.card := hcard.symm
    _ ≤ (Finset.univ : Finset S.Sym).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card S.Sym := Finset.card_univ

/-- Exact five-role witness. -/
inductive ComparatorRole5 where
  | base0
  | base1
  | eqVerdict
  | diffVerdict
  | query
  deriving DecidableEq, Fintype, Repr

/-- Attainment witness for the separated-role lower bound. -/
def comparatorRole5Signature : RoleSeparatedComparatorSignature where
  Sym := ComparatorRole5
  base0 := .base0
  base1 := .base1
  eqVerdict := .eqVerdict
  diffVerdict := .diffVerdict
  query := .query
  roles_nodup := by decide

/-- The five-role witness has exactly five symbols. -/
theorem comparatorRole5_card_eq_five :
    Fintype.card ComparatorRole5 = 5 := by decide

/-- The five-role lower bound is sharp. -/
theorem roleSeparated_five_is_minimal :
    Fintype.card ComparatorRole5 = 5 ∧
      ∀ (S : RoleSeparatedComparatorSignature)
        [Fintype S.Sym] [DecidableEq S.Sym],
        5 ≤ Fintype.card S.Sym :=
  ⟨comparatorRole5_card_eq_five, fun S => roleSeparated_card_ge_five S⟩

/-- Two distinct verdict emissions from one source exhibit two distinct
one-step target values. This theorem is relational and does not identify the
number of syntactic rule declarations. -/
theorem two_verdict_emissions_require_two_targets
    {T : Type u} {R : T → T → Prop} {source equal different : T}
    (heq : R source equal) (hdiff : R source different)
    (hne : equal ≠ different) :
    ∃ l r, R source l ∧ R source r ∧ l ≠ r :=
  ⟨equal, different, heq, hdiff, hne⟩

/-- Abstract declared rule-ID surface for two distinct root verdict emissions. -/
structure TwoVerdictRuleSurface where
  RuleId : Type u
  reflexiveRule : RuleId
  differenceRule : RuleId
  rules_distinct : reflexiveRule ≠ differenceRule

/-- Two distinct declared rule IDs force at least two rule identities. This is
not a claim about arbitrary nonconfluent TRSs outside the declared architecture. -/
theorem twoVerdict_ruleId_card_ge_two
    (S : TwoVerdictRuleSurface.{u}) [Fintype S.RuleId] [DecidableEq S.RuleId] :
    2 ≤ Fintype.card S.RuleId := by
  have hcard : ({S.reflexiveRule, S.differenceRule} : Finset S.RuleId).card = 2 := by
    simp [S.rules_distinct]
  calc
    2 = ({S.reflexiveRule, S.differenceRule} : Finset S.RuleId).card := hcard.symm
    _ ≤ (Finset.univ : Finset S.RuleId).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card S.RuleId := Finset.card_univ

/-- Two-rule attainment witness. -/
inductive TwoRuleId where
  | reflexive
  | difference
  deriving DecidableEq, Fintype, Repr

/-- Exact two-rule-ID surface. -/
def twoRuleSurface : TwoVerdictRuleSurface where
  RuleId := TwoRuleId
  reflexiveRule := .reflexive
  differenceRule := .difference
  rules_distinct := by intro h; cases h

/-- The declared two-rule lower bound is attained. -/
theorem twoRuleId_card_eq_two : Fintype.card TwoRuleId = 2 := by decide

/-- One theorem bundling all three distinct minimality notions. -/
theorem declared_minimality_bundle :
    Fintype.card ComparatorRole3 = 3 ∧
    Fintype.card ComparatorRole5 = 5 ∧
    Fintype.card TwoRuleId = 2 :=
  ⟨comparatorRole3_card_eq_three,
    comparatorRole5_card_eq_five,
    twoRuleId_card_eq_two⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
