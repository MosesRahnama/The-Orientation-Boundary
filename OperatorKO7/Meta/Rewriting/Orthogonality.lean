import OperatorKO7.Meta.Rewriting.CriticalPairComplete

/-!
# Orthogonality criteria for first-order term rewriting systems

Roadmap source: the confluence-toolkit expansion atop the verified rewriting
foundation (`Term`, `Position`, `Subst`, `Unify`, `UnifyCorrect`, `Rewrite`,
`CriticalPair`, `CriticalPairLemma`, `CriticalPairComplete`). This module adds the
orthogonality vocabulary and derives local confluence and confluence from it
through the Critical Pair Lemma `critical_pair_lemma` (the Huet/Knuth-Bendix
biconditional) and the generic Newman lemma `confluent_of_cp_joinable_of_SN`.

## What this module delivers

The left-linearity predicate and the two orthogonality notions (priority 1):

- `Term.varOccs` / `Term.varOccsList` : the list of variable occurrences of a
  term, in left-to-right order, counting multiplicity. Its membership agrees with
  the variable set (`Term.mem_varOccs_iff`), so a duplicate-free occurrence list is
  exactly the absence of a repeated variable.
- `Term.linear` : a term whose variable-occurrence list has no duplicate.
- `leftLinear R` : every rule's left-hand side is linear, i.e. no variable repeats
  in any left-hand side.
- `orthogonal R := leftLinear R ∧ criticalPairs R = []` : left-linear with an empty
  critical-pair enumeration.
- `weaklyOrthogonal R := leftLinear R ∧ ∀ p ∈ criticalPairs R, p.1 = p.2` :
  left-linear with every critical pair trivial (both components equal).

Local confluence from orthogonality (priority 2):

- `orthogonal_imp_localConfluent` : an orthogonal system has a locally confluent
  renamed system. An empty critical-pair enumeration makes the joinability premise
  of `critical_pair_lemma` hold with no pair to check.
- `weaklyOrthogonal_imp_localConfluent` : a weakly orthogonal system has a locally
  confluent renamed system. Each critical pair has equal components, so it joins
  reflexively, again satisfying the premise of `critical_pair_lemma`.

Confluence from orthogonality with strong normalization (priority 3):

- `orthogonal_imp_confluent_of_SN` and `weaklyOrthogonal_imp_confluent_of_SN` :
  composing the local-confluence premise with strong normalization of the renamed
  system through the generic Newman lemma `confluent_of_cp_joinable_of_SN` yields
  confluence of `StepStar (renameTRS R)`.

Non-vacuity (priority 4):

- `emptyTRS_orthogonal` / `emptyTRS_weaklyOrthogonal` : the empty system satisfies
  both notions, its critical-pair enumeration being empty.
- `orthogonal_emptyTRS_localConfluent` / `weaklyOrthogonal_emptyTRS_localConfluent`
  : the local-confluence conclusion applied to that witness.
- `ruleFG_lhs_linear` : the concrete left-hand side `f(x)` is linear, the working
  part of left-linearity on a genuine one-variable application.

Trust: kernel-only; baseline-only under `#print axioms` (a subset of
`{propext, Classical.choice, Quot.sound}`). Any `Classical.choice`/`propext`
dependence is from `Finset`/`DecidableEq` plumbing inherited through the foundation
modules.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open scoped Subst
open Subst

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Variable occurrences and left-linearity

`Term.vars` returns the variable set as a `Finset`, which already discards
multiplicity, so a repeated variable is invisible to it. `Term.varOccs` records the
occurrences as a list in left-to-right order, keeping multiplicity; a rule's
left-hand side is linear exactly when this list has no duplicate. The membership
agreement `Term.mem_varOccs_iff` confirms the occurrence list ranges over precisely
the variables of the term. -/

namespace Term

mutual
/-- The list of variable occurrences of a term, in left-to-right order, counting
multiplicity. A variable contributes itself; an application concatenates the
occurrence lists of its arguments. Uses an auxiliary `varOccsList` so the nested
recursion through the argument list is structural. -/
def varOccs : Term sigma nu → List nu
  | .var x => [x]
  | .app _ args => varOccsList args
/-- The concatenated variable-occurrence lists over an argument list. -/
def varOccsList : List (Term sigma nu) → List nu
  | [] => []
  | a :: as => varOccs a ++ varOccsList as
end

@[simp] theorem varOccs_var (x : nu) :
    varOccs (Term.var (sigma := sigma) x) = [x] := rfl
@[simp] theorem varOccs_app (f : sigma) (args : List (Term sigma nu)) :
    varOccs (Term.app f args) = varOccsList args := rfl
@[simp] theorem varOccsList_nil :
    varOccsList ([] : List (Term sigma nu)) = [] := rfl
@[simp] theorem varOccsList_cons (a : Term sigma nu) (as : List (Term sigma nu)) :
    varOccsList (a :: as) = varOccs a ++ varOccsList as := rfl

/-- Membership in the occurrence list agrees with membership in the variable set:
a variable occurs in `varOccs t` exactly when it belongs to `vars t`. So a
duplicate-free `varOccs t` is precisely the absence of a repeated variable in `t`,
which is what left-linearity requires of a left-hand side. -/
theorem mem_varOccs_iff [DecidableEq nu] {x : nu} :
    ∀ (t : Term sigma nu), x ∈ varOccs t ↔ x ∈ Term.vars t := by
  intro t
  induction t using Term.rec' with
  | hvar y => simp
  | happ f args ih =>
      simp only [varOccs_app, Term.vars_app]
      induction args with
      | nil => simp
      | cons a as ihl =>
          simp only [varOccsList_cons, List.mem_append, Term.varsList_cons,
            Finset.mem_union]
          rw [ih a (by simp)]
          rw [ihl (fun c hc => ih c (by simp [hc]))]

/-- A term is linear when its variable-occurrence list has no duplicate: no variable
occurs in it more than once. -/
def linear (t : Term sigma nu) : Prop := (Term.varOccs t).Nodup

end Term

/-- A term rewriting system is left-linear when every rule's left-hand side is
linear, i.e. no variable occurs more than once in any left-hand side. The
variable-overlap join of the Critical Pair Lemma already covers non-left-linear
systems, so this predicate isolates exactly the systems whose only obstructions to
local confluence are the genuine critical overlaps. -/
def leftLinear (R : TRS sigma nu) : Prop :=
  ∀ rule ∈ R, Term.linear rule.lhs

/-! ## The two orthogonality notions

Orthogonality is left-linearity together with the absence of critical overlaps.
The strong form asks for an empty critical-pair enumeration; the weak form allows
critical pairs as long as every one is trivial (its two components coincide), which
joins reflexively. -/

/-- A term rewriting system is orthogonal when it is left-linear and its
critical-pair enumeration is empty: it is left-linear and has no critical overlaps.
-/
def orthogonal [DecidableEq sigma] [DecidableEq nu] (R : TRS sigma nu) : Prop :=
  leftLinear R ∧ criticalPairs R = []

/-- A term rewriting system is weakly orthogonal when it is left-linear and every
critical pair is trivial: its two components coincide. Trivial critical pairs join
reflexively, so weak orthogonality already forces local confluence of the renamed
system. -/
def weaklyOrthogonal [DecidableEq sigma] [DecidableEq nu] (R : TRS sigma nu) : Prop :=
  leftLinear R ∧ ∀ p ∈ criticalPairs R, p.1 = p.2

/-! ## Priority 2: local confluence from orthogonality

Both orthogonality notions discharge the joinability premise of the Critical Pair
Lemma `critical_pair_lemma`, so each yields local confluence of the renamed system.
The strong form discharges it because there is no critical pair to join; the weak
form because every critical pair joins reflexively. -/

/-- An orthogonal system has a locally confluent renamed system. The critical-pair
enumeration is empty, so the joinability premise of the Critical Pair Lemma holds
with no pair to check, and `critical_pair_lemma` returns local confluence. -/
theorem orthogonal_imp_localConfluent [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (h : orthogonal R) : localConfluent (renameTRS R) := by
  refine (critical_pair_lemma R).2 ?_
  intro p hp
  rw [h.2] at hp
  exact absurd hp List.not_mem_nil

/-- A weakly orthogonal system has a locally confluent renamed system. Every
critical pair has equal components, so each joins reflexively, discharging the
joinability premise of the Critical Pair Lemma, and `critical_pair_lemma` returns
local confluence. -/
theorem weaklyOrthogonal_imp_localConfluent [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (h : weaklyOrthogonal R) : localConfluent (renameTRS R) := by
  refine (critical_pair_lemma R).2 ?_
  intro p hp
  have hpeq : p.1 = p.2 := h.2 p hp
  rw [hpeq]
  exact joinable.refl (renameTRS R) p.2

/-! ## Priority 3: confluence from orthogonality under strong normalization

Composing the local-confluence premise with strong normalization of the renamed
system through the generic Newman lemma `confluent_of_cp_joinable_of_SN` upgrades
either orthogonality notion to confluence of `StepStar (renameTRS R)`. The
strong-normalization hypothesis is supplied; for a concrete system it is discharged
by a termination measure. -/

/-- Confluence of an orthogonal system under strong normalization: if `R` is
orthogonal and the one-step relation `Step (renameTRS R)` is strongly normalizing
(its reverse is well-founded), then `StepStar (renameTRS R)` is confluent. The empty
critical-pair enumeration discharges critical-pair joinability, and the generic
Newman lemma `confluent_of_cp_joinable_of_SN` upgrades local confluence to
confluence. -/
theorem orthogonal_imp_confluent_of_SN [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (h : orthogonal R)
    (hSN : WellFounded (fun x y : Term sigma (RenVar nu) => Step (renameTRS R) y x)) :
    ∀ a b c, StepStar (renameTRS R) a b → StepStar (renameTRS R) a c →
      ∃ d, StepStar (renameTRS R) b d ∧ StepStar (renameTRS R) c d := by
  refine confluent_of_cp_joinable_of_SN hSN ?_
  intro p hp
  rw [h.2] at hp
  exact absurd hp List.not_mem_nil

/-- Confluence of a weakly orthogonal system under strong normalization: if `R` is
weakly orthogonal and the one-step relation `Step (renameTRS R)` is strongly
normalizing (its reverse is well-founded), then `StepStar (renameTRS R)` is
confluent. Every critical pair is trivial, joining reflexively, and the generic
Newman lemma `confluent_of_cp_joinable_of_SN` upgrades local confluence to
confluence. -/
theorem weaklyOrthogonal_imp_confluent_of_SN [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (h : weaklyOrthogonal R)
    (hSN : WellFounded (fun x y : Term sigma (RenVar nu) => Step (renameTRS R) y x)) :
    ∀ a b c, StepStar (renameTRS R) a b → StepStar (renameTRS R) a c →
      ∃ d, StepStar (renameTRS R) b d ∧ StepStar (renameTRS R) c d := by
  refine confluent_of_cp_joinable_of_SN hSN ?_
  intro p hp
  have hpeq : p.1 = p.2 := h.2 p hp
  rw [hpeq]
  exact joinable.refl (renameTRS R) p.2

/-! ## Priority 4: non-vacuity

The empty system satisfies both orthogonality notions: its critical-pair
enumeration is empty, so the empty-list condition holds by `rfl` and the
universal condition holds with no pair to check. Each notion carries its
local-confluence conclusion. A concrete left-hand side `f(x)` is exhibited as linear
to show left-linearity bites on a genuine one-variable application. -/

/-- The empty term rewriting system is orthogonal: it is left-linear with no rule to
check, and its critical-pair enumeration is empty. -/
theorem emptyTRS_orthogonal [DecidableEq sigma] [DecidableEq nu] :
    orthogonal ([] : TRS sigma nu) :=
  ⟨fun _ hrule => absurd hrule List.not_mem_nil, rfl⟩

/-- The empty term rewriting system is weakly orthogonal: it is left-linear, and its
empty critical-pair enumeration has no pair whose components could differ. -/
theorem emptyTRS_weaklyOrthogonal [DecidableEq sigma] [DecidableEq nu] :
    weaklyOrthogonal ([] : TRS sigma nu) :=
  ⟨fun _ hrule => absurd hrule List.not_mem_nil,
    fun _ hp => absurd hp List.not_mem_nil⟩

/-- The orthogonality local-confluence conclusion applied to the empty system: its
renamed system is locally confluent. -/
theorem orthogonal_emptyTRS_localConfluent [DecidableEq sigma] [DecidableEq nu] :
    localConfluent (renameTRS ([] : TRS sigma nu)) :=
  orthogonal_imp_localConfluent emptyTRS_orthogonal

/-- The weak-orthogonality local-confluence conclusion applied to the empty system:
its renamed system is locally confluent. -/
theorem weaklyOrthogonal_emptyTRS_localConfluent [DecidableEq sigma] [DecidableEq nu] :
    localConfluent (renameTRS ([] : TRS sigma nu)) :=
  weaklyOrthogonal_imp_localConfluent emptyTRS_weaklyOrthogonal

/-- The rule `f(x) -> g(x)`, with `f` the symbol `0`, `g` the symbol `1`, and `x`
the variable `0`. Its left-hand side is an application carrying a single,
non-repeated variable. -/
def ruleFG : Rule Nat Nat where
  lhs := .app 0 [.var 0]
  rhs := .app 1 [.var 0]
  lhs_isApp := rfl

/-- The concrete left-hand side `f(x)` is linear: its variable-occurrence list `[x]`
has no duplicate. This exercises `Term.linear` and `leftLinear`'s per-rule condition
on a genuine one-variable application, the working content of left-linearity. -/
theorem ruleFG_lhs_linear : Term.linear ruleFG.lhs := by
  show (Term.varOccs ruleFG.lhs).Nodup
  decide

end OperatorKO7.Meta.Rewriting

/-! ## Verification: headline types and axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @Term.varOccs
open OperatorKO7.Meta.Rewriting in
#check @Term.mem_varOccs_iff
open OperatorKO7.Meta.Rewriting in
#check @Term.linear
open OperatorKO7.Meta.Rewriting in
#check @leftLinear
open OperatorKO7.Meta.Rewriting in
#check @orthogonal
open OperatorKO7.Meta.Rewriting in
#check @weaklyOrthogonal
open OperatorKO7.Meta.Rewriting in
#check @orthogonal_imp_localConfluent
open OperatorKO7.Meta.Rewriting in
#check @weaklyOrthogonal_imp_localConfluent
open OperatorKO7.Meta.Rewriting in
#check @orthogonal_imp_confluent_of_SN
open OperatorKO7.Meta.Rewriting in
#check @weaklyOrthogonal_imp_confluent_of_SN
open OperatorKO7.Meta.Rewriting in
#check @emptyTRS_orthogonal
open OperatorKO7.Meta.Rewriting in
#check @emptyTRS_weaklyOrthogonal
open OperatorKO7.Meta.Rewriting in
#check @ruleFG_lhs_linear

#print axioms OperatorKO7.Meta.Rewriting.Term.varOccs
#print axioms OperatorKO7.Meta.Rewriting.Term.mem_varOccs_iff
#print axioms OperatorKO7.Meta.Rewriting.orthogonal_imp_localConfluent
#print axioms OperatorKO7.Meta.Rewriting.weaklyOrthogonal_imp_localConfluent
#print axioms OperatorKO7.Meta.Rewriting.orthogonal_imp_confluent_of_SN
#print axioms OperatorKO7.Meta.Rewriting.weaklyOrthogonal_imp_confluent_of_SN
#print axioms OperatorKO7.Meta.Rewriting.emptyTRS_orthogonal
#print axioms OperatorKO7.Meta.Rewriting.emptyTRS_weaklyOrthogonal
#print axioms OperatorKO7.Meta.Rewriting.orthogonal_emptyTRS_localConfluent
#print axioms OperatorKO7.Meta.Rewriting.weaklyOrthogonal_emptyTRS_localConfluent
#print axioms OperatorKO7.Meta.Rewriting.ruleFG_lhs_linear
