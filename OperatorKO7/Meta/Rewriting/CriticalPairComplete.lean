import OperatorKO7.Meta.Rewriting.CriticalPairLemma

/-!
# The Critical Pair Lemma: completeness of the overlap enumeration and the Huet biconditional

Roadmap source: `ROADMAP-01-generic-critical-pair-lemma.md`, section 3 (the
critical-overlap case: a peak at a critical position is a context-and-substitution
instance of a critical pair, closed by critical-pair joinability). This module
closes the backward direction of the Critical Pair Lemma on top of the verified
foundation (`Term`, `Position`, `Subst`, `Unify`, `UnifyCorrect`, `Rewrite`,
`CriticalPair`, `CriticalPairLemma`).

## What this module delivers

Completeness of the critical-pair enumeration (priority 1):

- `criticalPairs_complete` : the inverse of `criticalPairs_sound`. When two rules
  `r1, r2` of `R` overlap at a non-variable position `p` of `r1`'s renamed
  left-hand side under a common instance (a substitution `nu` equalizing the
  overlapped subterm with `r2`'s renamed left-hand side), there is an emitted
  critical pair `(c1, c2) ∈ criticalPairs R` and a substitution `rho` so the
  overlap's two reducts are `rho • c1` and `rho • c2`. The engine is
  `unify_mostGeneral`: the overlap's unifier factors through `unify`'s most general
  unifier, so the concrete overlap is a `rho`-instance of the emitted pair.

The root-overlap backward direction and biconditional (priority 3/4, root case):

- `joinable_of_cp_joinable_rootPeak` : a root-overlap peak (two root contractions
  from one source) is joinable, given critical-pair joinability. The source is a
  common instance of two rule left-hand sides, so the peak is a `rho`-instance of an
  emitted critical pair; `criticalPairs_complete` names the pair, `joinable_subst`
  carries its joinability to the instance.

The general redex trichotomy (priority 2) and full backward direction (priority 3):

- `Step.rootStep_or_arg` : a one-step rewrite is either a root contraction or sits
  strictly inside one argument, the structural split powering the peak analysis.
- `cp_joinable_imp_localConfluent` : if every critical pair of `R` is joinable in
  `renameTRS R`, then `renameTRS R` is locally confluent. Parallel peaks join by
  `joinable_of_parallel_peak`, variable-overlap peaks by
  `joinable_of_variable_overlap`, critical peaks by `criticalPairs_complete`,
  `joinable_subst`, and `joinable_at_pos`.

The full biconditional and the confluence corollary (priority 4):

- `critical_pair_lemma` : `localConfluent (renameTRS R) ↔
  ∀ q ∈ criticalPairs R, joinable (renameTRS R) q.1 q.2`, the Huet/Knuth-Bendix
  characterization, assembled from the forward direction
  (`localConfluent_imp_cp_joinable`) and the backward direction
  (`cp_joinable_imp_localConfluent`).
- `confluent_of_cp_joinable_of_SN` : critical-pair joinability plus strong
  normalization of `renameTRS R` gives confluence of `StepStar (renameTRS R)`,
  composing the biconditional with the generic Newman lemma
  `confluent_of_wf_of_localConfluent`.

Trust: kernel-only; baseline-only under `#print axioms` (a subset of
`{propext, Classical.choice, Quot.sound}`). Any `Classical.choice`/`propext`
dependence is from `Finset`/`DecidableEq` plumbing inherited through the
foundation modules.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open scoped Subst
open Subst

universe u v

variable {sigma : Type u} {nu : Type v}

/-- The left-summand renaming injection, with its codomain pinned to the shared
critical-pair carrier `RenVar nu`. Rule 1 of an overlap is renamed through this. -/
abbrev renL (nu : Type v) : nu → RenVar nu := Sum.inl

/-- The right-summand renaming injection, with its codomain pinned to the shared
critical-pair carrier `RenVar nu`. Rule 2 of an overlap is renamed through this. -/
abbrev renR (nu : Type v) : nu → RenVar nu := Sum.inr

/-! ## Priority 1: completeness of the critical-pair enumeration

The inverse of `criticalPairs_sound`. A genuine overlap of two rules at a
non-variable position under a common instance is captured by the emitted critical
pair, up to a residual substitution. `unify_mostGeneral` is the engine: the
overlap's own unifier factors through `unify`'s most general unifier, so the
overlap is a substitution instance of the emitted pair. -/

/-- Completeness of `overlapAt`: if the subterm of `r1.lhs` at a non-variable
position `p` and `r2.lhs` have a common instance under some substitution `ν`
(`ν • sub = ν • r2.lhs`), then `overlapAt r1 r2 p` emits a pair `(c1, c2)`, and `ν`
factors through the emitted unifier by some `ρ` so the concrete overlap reducts are
`ρ`-instances: `ν • r1.rhs = ρ • c1` and `ν • replaceAt r1.lhs p r2.rhs = ρ • c2`.
The most general unifier `μ` returned by `unify` exists by `unify_complete`, and
`unify_mostGeneral` supplies `ρ`. -/
theorem overlapAt_complete [DecidableEq sigma] [DecidableEq nu]
    (r1 r2 : Rule sigma (RenVar nu)) (p : Pos) {sub : Term sigma (RenVar nu)}
    (hsub : Term.subtermAt r1.lhs p = some sub) {ν : Subst sigma (RenVar nu)}
    (hcommon : ν • sub = ν • r2.lhs) :
    ∃ c1 c2 : Term sigma (RenVar nu), overlapAt r1 r2 p = some (c1, c2) ∧
      ∃ ρ : Subst sigma (RenVar nu),
        ν • r1.rhs = ρ • c1 ∧ ν • Term.replaceAt r1.lhs p r2.rhs = ρ • c2 := by
  -- the overlap unifies, so `unify` succeeds with some most general unifier `μ`
  obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (unify_complete ⟨ν, hcommon⟩)
  -- the emitted critical pair at `p`
  refine ⟨μ • r1.rhs, μ • Term.replaceAt r1.lhs p r2.rhs, ?_, ?_⟩
  · -- `overlapAt` peels to exactly this pair through its two `Option` layers
    rw [overlapAt, hsub, Option.bind_some, hμ, Option.map_some]
  · -- `ν` factors through `μ`: `∀ x, ν x = (ρ.comp μ) x`
    obtain ⟨ρ, hρ⟩ := unify_mostGeneral hμ ν hcommon
    refine ⟨ρ, ?_, ?_⟩
    · -- `ν • r1.rhs = (ρ.comp μ) • r1.rhs = ρ • (μ • r1.rhs)`
      rw [apply_congr_of_pointwise hρ r1.rhs, apply_comp]
    · rw [apply_congr_of_pointwise hρ (Term.replaceAt r1.lhs p r2.rhs), apply_comp]

/-- A pair emitted by `overlapAt (renameRule Sum.inl r1) (renameRule Sum.inr r2) p`
at a non-variable position `p` is a member of `criticalPairs R` whenever
`r1, r2 ∈ R`. It is reached through `List.mem_filterMap` into `overlapPairs` and
then the ordered double `flatMap` of `criticalPairs`. -/
theorem mem_criticalPairs_of_overlapAt [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {r1 r2 : Rule sigma nu} (hr1 : r1 ∈ R) (hr2 : r2 ∈ R)
    {p : Pos} (hp : p ∈ nonVarPositions (renameRule (renL nu) r1).lhs)
    {c1 c2 : Term sigma (RenVar nu)}
    (hpair : overlapAt (renameRule (renL nu) r1) (renameRule (renR nu) r2) p
      = some (c1, c2)) :
    (c1, c2) ∈ criticalPairs R := by
  rw [criticalPairs, List.mem_flatMap]
  refine ⟨r1, hr1, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨r2, hr2, ?_⟩
  rw [overlapPairs, List.mem_filterMap]
  exact ⟨p, hp, hpair⟩

/-- Completeness of the critical-pair enumeration: the inverse of
`criticalPairs_sound`. Suppose two rules `r1, r2 ∈ R` (renamed apart into the
left and right variable summands) overlap at a non-variable position `p` of
`r1`'s renamed left-hand side under a common instance: the subterm there is `sub`
and a substitution `ν` over `RenVar nu` equalizes `ν • sub = ν • r2.lhs`. Then an
emitted critical pair `(c1, c2) ∈ criticalPairs R` and a substitution `ρ` witness
that the overlap's two reducts are `ρ`-instances of the pair, `ν • r1.rhs = ρ • c1`
and `ν • replaceAt r1.lhs p r2.rhs = ρ • c2`. The most general unifier of the
overlap factors `ν`, so the concrete overlap is a substitution instance of the
emitted pair. -/
theorem criticalPairs_complete [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {r1 r2 : Rule sigma nu} (hr1 : r1 ∈ R) (hr2 : r2 ∈ R)
    {p : Pos} (hp : p ∈ nonVarPositions (renameRule (renL nu) r1).lhs)
    {sub : Term sigma (RenVar nu)}
    (hsub : Term.subtermAt (renameRule (renL nu) r1).lhs p = some sub)
    {ν : Subst sigma (RenVar nu)} (hcommon : ν • sub = ν • (renameRule (renR nu) r2).lhs) :
    ∃ c1 c2 : Term sigma (RenVar nu), (c1, c2) ∈ criticalPairs R ∧
      ∃ ρ : Subst sigma (RenVar nu),
        ν • (renameRule (renL nu) r1).rhs = ρ • c1 ∧
        ν • Term.replaceAt (renameRule (renL nu) r1).lhs p (renameRule (renR nu) r2).rhs
          = ρ • c2 := by
  obtain ⟨c1, c2, hpair, ρ, hc1, hc2⟩ :=
    overlapAt_complete (renameRule (renL nu) r1) (renameRule (renR nu) r2) p hsub hcommon
  exact ⟨c1, c2, mem_criticalPairs_of_overlapAt hr1 hr2 hp hpair, ρ, hc1, hc2⟩

/-! ## Priority 3/4 (FLOOR): the root-overlap backward direction

A root-overlap peak is two root contractions from one source. After the rules are
renamed apart, the shared source is a common instance of their left-hand sides, so
the peak is a substitution instance of an emitted critical pair at the root
position. `criticalPairs_complete` names the pair, and `joinable_subst` carries its
joinability across to the instance. The bridge from a renamed-rule instance to a
recombined-substitution instance is `apply_rename`. -/

/-- Two renaming-then-substitution composites that agree variable-by-variable
produce the same term: if `σ (g x) = σ' (g' x)` for every original variable `x`,
then `σ • (rename g t) = σ' • (rename g' t)`. By structural induction on `t` over
the argument-list eliminator. This recombines the two renamed copies of a rule in a
peak into a single common instance over the shared carrier, the bridge into
`criticalPairs_complete`. -/
theorem apply_rename_congr {nu' : Type v} (σ σ' : Subst sigma nu') (g g' : nu → nu')
    (hpt : ∀ x, σ (g x) = σ' (g' x)) :
    ∀ (t : Term sigma nu), apply σ (Term.rename g t) = apply σ' (Term.rename g' t) := by
  intro t
  induction t using Term.rec' with
  | hvar x => exact hpt x
  | happ f args ih =>
      rw [Term.rename_app, Term.rename_app, apply_app, apply_app,
        Term.renameList_eq_map, Term.renameList_eq_map, applyList_eq_map,
        applyList_eq_map, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left ih

/-- Membership in `renameTRS R` is membership of an original rule renamed into one
of the two summands: `rule ∈ renameTRS R` exactly when `rule = renameRule Sum.inl r`
or `rule = renameRule Sum.inr r` for some `r ∈ R`. Reads off the `++` and the two
`List.map`s of `renameTRS`. -/
theorem mem_renameTRS_iff [DecidableEq nu] {R : TRS sigma nu}
    {rule : Rule sigma (RenVar nu)} :
    rule ∈ renameTRS R ↔
      (∃ r ∈ R, rule = renameRule (renL nu) r) ∨ (∃ r ∈ R, rule = renameRule (renR nu) r) := by
  rw [renameTRS, List.mem_append]
  constructor
  · rintro (h | h)
    · rw [List.mem_map] at h; obtain ⟨r, hr, rfl⟩ := h; exact Or.inl ⟨r, hr, rfl⟩
    · rw [List.mem_map] at h; obtain ⟨r, hr, rfl⟩ := h; exact Or.inr ⟨r, hr, rfl⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact Or.inl (List.mem_map_of_mem hr)
    · exact Or.inr (List.mem_map_of_mem hr)

/-- The root position is a non-variable position of any rule's renamed left-hand
side: a rule's left-hand side is an application, and renaming preserves that, so
the root `[]` is enumerated by `nonVarPositions`. -/
theorem nil_mem_nonVarPositions_renameRule {nu' : Type v} (g : nu → nu')
    (r : Rule sigma nu) : ([] : Pos) ∈ nonVarPositions (renameRule g r).lhs := by
  have happ : (renameRule g r).lhs.isApp = true := (renameRule g r).lhs_isApp
  cases hlhs : (renameRule g r).lhs with
  | var x => rw [hlhs] at happ; simp at happ
  | app f args => simp [nonVarPositions_app]

/-- A root-overlap peak of two original rules joins under critical-pair
joinability. Two rules `r1, r2 ∈ R`, renamed apart through `g1` and `g2` into the
shared carrier and contracted at the root by substitutions `σ1, σ2` to a common
source `σ1 • (rename g1 r1.lhs) = σ2 • (rename g2 r2.lhs)`, have joinable reducts
`σ1 • (rename g1 r1.rhs)` and `σ2 • (rename g2 r2.rhs)` in `renameTRS R`. The
combined substitution `ν = Sum.elim (σ1 ∘ g1) (σ2 ∘ g2)` makes the apart copies
`renameRule Sum.inl r1` and `renameRule Sum.inr r2` a common instance at the root
position, so `criticalPairs_complete` exhibits the peak as a `ρ`-instance of an
emitted critical pair; `joinable_subst` carries the pair's joinability across. The
two summand injections `g1, g2` may each be `Sum.inl` or `Sum.inr`, so this covers
every root overlap of `renameTRS R`. -/
theorem joinable_rootOverlap_of_cp_joinable [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (hcp : ∀ q ∈ criticalPairs R, joinable (renameTRS R) q.1 q.2)
    {r1 r2 : Rule sigma nu} (hr1 : r1 ∈ R) (hr2 : r2 ∈ R)
    (g1 g2 : nu → RenVar nu) {σ1 σ2 : Subst sigma (RenVar nu)}
    (hs : σ1 • Term.rename g1 r1.lhs = σ2 • Term.rename g2 r2.lhs) :
    joinable (renameTRS R) (σ1 • Term.rename g1 r1.rhs) (σ2 • Term.rename g2 r2.rhs) := by
  -- the combined substitution feeding both apart copies their original assignment
  set ν : Subst sigma (RenVar nu) :=
    Sum.elim (fun x => σ1 (g1 x)) (fun y => σ2 (g2 y)) with hν
  -- on the inl-image `ν` reproduces `σ1 ∘ g1`; on the inr-image, `σ2 ∘ g2`
  have hνl : ∀ x, ν (Sum.inl x) = σ1 (g1 x) := fun x => rfl
  have hνr : ∀ y, ν (Sum.inr y) = σ2 (g2 y) := fun y => rfl
  -- the source as an instance of the inl-renamed copy of `r1`
  have hsrc1 : ν • Term.rename (renL nu) r1.lhs = σ1 • Term.rename g1 r1.lhs :=
    apply_rename_congr ν σ1 (renL nu) g1 (fun x => hνl x) r1.lhs
  -- the source as an instance of the inr-renamed copy of `r2`
  have hsrc2 : ν • Term.rename (renR nu) r2.lhs = σ2 • Term.rename g2 r2.lhs :=
    apply_rename_congr ν σ2 (renR nu) g2 (fun y => hνr y) r2.lhs
  -- the right reducts recombine the same way
  have hrhs1 : ν • Term.rename (renL nu) r1.rhs = σ1 • Term.rename g1 r1.rhs :=
    apply_rename_congr ν σ1 (renL nu) g1 (fun x => hνl x) r1.rhs
  have hrhs2 : ν • Term.rename (renR nu) r2.rhs = σ2 • Term.rename g2 r2.rhs :=
    apply_rename_congr ν σ2 (renR nu) g2 (fun y => hνr y) r2.rhs
  -- the overlap at the root position: subterm there is the whole inl-renamed lhs
  have hsub : Term.subtermAt (renameRule (renL nu) r1).lhs [] = some (renameRule (renL nu) r1).lhs :=
    Term.subtermAt_nil _
  -- common-instance hypothesis for completeness, at the root position
  have hcommon : ν • (renameRule (renL nu) r1).lhs = ν • (renameRule (renR nu) r2).lhs := by
    rw [renameRule_lhs, renameRule_lhs, hsrc1, hsrc2]; exact hs
  -- completeness names the emitted pair and the residual substitution
  obtain ⟨c1, c2, hmem, ρ, hc1, hc2⟩ :=
    criticalPairs_complete hr1 hr2 (nil_mem_nonVarPositions_renameRule (renL nu) r1) hsub hcommon
  -- the emitted pair is joinable; transport that joinability by `ρ`
  have hjoin : joinable (renameTRS R) (ρ • c1) (ρ • c2) :=
    joinable_subst (renameTRS R) ρ (hcp (c1, c2) hmem)
  -- rewrite the two reducts of the peak as `ρ • c1` and `ρ • c2`
  -- `(renameRule (renL nu) r1).rhs = Term.rename (renL nu) r1.rhs` definitionally
  rw [renameRule_rhs] at hc1
  rw [Term.replaceAt_nil, renameRule_rhs] at hc2
  have hleft : σ1 • Term.rename g1 r1.rhs = ρ • c1 := hrhs1 ▸ hc1
  have hright : σ2 • Term.rename g2 r2.rhs = ρ • c2 := hrhs2 ▸ hc2
  rw [hleft, hright]; exact hjoin

/-! ## Priority 2: the redex-position trichotomy

Two one-step rewrites from one source contract redexes at two positions. The
analysis turns on those positions. The structural engine is `Step.exists_pos_rootStep`
(every step is a root contraction at some position) together with the position
classification `subtermAt_apply_cases`: a position read inside a substitution
instance `σ • t` either lands on a non-variable position of `t` (a function
position, the critical-overlap case) or descends through a variable of `t` into the
substituted term (the variable-overlap case). -/

/-- Position classification inside a substitution instance. A position `q` that
reads a subterm of `σ • t` either lands on a (function) position of `t` whose
subterm is an application, or it factors as a variable position of `t` followed by a
position inside the term that variable is mapped to. The first alternative is the
critical-overlap shape; the second is the variable-overlap shape. By structural
induction on `t` and case analysis on `q`. -/
theorem subtermAt_apply_cases (σ : Subst sigma nu) :
    ∀ (t : Term sigma nu) (q : Pos) (redex : Term sigma nu),
      Term.subtermAt (σ • t) q = some redex →
      (∃ sub, Term.subtermAt t q = some sub ∧ sub.isApp = true ∧ redex = σ • sub) ∨
      (∃ pv x pr, q = pv ++ pr ∧ Term.subtermAt t pv = some (Term.var x) ∧
        Term.subtermAt (σ x) pr = some redex) := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro q redex hq
      -- `σ • var x = σ x`; the read happens entirely inside the variable image
      refine Or.inr ⟨[], x, q, by simp, by simp, ?_⟩
      rwa [apply_var] at hq
  | happ f args ih =>
      intro q redex hq
      cases q with
      | nil =>
          -- root read: the whole substituted application
          refine Or.inl ⟨Term.app f args, by simp, by simp, ?_⟩
          rw [Term.subtermAt_nil, Option.some.injEq] at hq
          exact hq.symm
      | cons i q' =>
          rw [apply_app, Term.subtermAt_app_cons, applyList_eq_map] at hq
          cases hgi : args[i]? with
          | none => rw [List.getElem?_map, hgi] at hq; simp at hq
          | some ai =>
              have hmap : (args.map (apply σ))[i]? = some (σ • ai) := by
                rw [List.getElem?_map, hgi]; rfl
              rw [hmap] at hq
              have hmem : ai ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, ha⟩ := hgi; exact ha ▸ List.getElem_mem _
              rcases ih ai hmem q' redex hq with ⟨sub, hsub, happ, hred⟩ | ⟨pv, x, pr, hq', hpv, hpr⟩
              · -- function position inside the `i`-th argument
                refine Or.inl ⟨sub, ?_, happ, hred⟩
                rw [Term.subtermAt_app_cons, hgi]; exact hsub
              · -- variable position inside the `i`-th argument
                refine Or.inr ⟨i :: pv, x, pr, by rw [hq', List.cons_append], ?_, hpr⟩
                rw [Term.subtermAt_app_cons, hgi]; exact hpv

/-- Completeness of `nonVarPositions` (the converse of `nonVarPositions_sound`):
a position whose subterm is an application is enumerated by `nonVarPositions`. By
structural induction on `t` and case analysis on the position. This certifies that
a function-position overlap discovered by `subtermAt_apply_cases` is genuinely one
of the positions the critical-pair construction ranges over. -/
theorem mem_nonVarPositions_of_subtermAt :
    ∀ (t : Term sigma nu) (q : Pos) (s : Term sigma nu),
      Term.subtermAt t q = some s → s.isApp = true → q ∈ nonVarPositions t := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro q s hq hsapp
      cases q with
      | nil =>
          rw [Term.subtermAt_nil, Option.some.injEq] at hq
          rw [← hq] at hsapp; simp at hsapp
      | cons i q => simp only [Term.subtermAt_var_cons, reduceCtorEq] at hq
  | happ f args ih =>
      intro q s hq hsapp
      cases q with
      | nil => simp [nonVarPositions_app]
      | cons i q' =>
          rw [Term.subtermAt_app_cons] at hq
          cases hgi : args[i]? with
          | none => rw [hgi] at hq; simp at hq
          | some ai =>
              rw [hgi] at hq
              have hmem : ai ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, ha⟩ := hgi; exact ha ▸ List.getElem_mem _
              have hi : i < args.length := by
                rw [List.getElem?_eq_some_iff] at hgi; exact hgi.1
              have hinner : q' ∈ nonVarPositions ai := ih ai hmem q' s hq hsapp
              -- the inner non-variable position lifts with the index `i` prepended
              rw [nonVarPositions_app, List.mem_cons]
              refine Or.inr ?_
              -- `nonVarPositionsList args 0` contains `i :: q'`
              have hkey : ∀ (l : List (Term sigma nu)) (base : Nat) (j : Nat) (a : Term sigma nu),
                  l[j]? = some a → q' ∈ nonVarPositions a → (base + j) :: q' ∈ nonVarPositionsList l base := by
                intro l
                induction l with
                | nil => intro base j a hj _; simp at hj
                | cons c cs ihl =>
                    intro base j a hj hqa
                    cases j with
                    | zero =>
                        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
                        subst hj
                        rw [nonVarPositionsList, List.mem_append]
                        refine Or.inl ?_
                        rw [List.mem_map]
                        exact ⟨q', hqa, by simp⟩
                    | succ j =>
                        simp only [List.getElem?_cons_succ] at hj
                        rw [nonVarPositionsList, List.mem_append]
                        refine Or.inr ?_
                        have := ihl (base + 1) j a hj hqa
                        have heq : base + 1 + j = base + (j + 1) := by omega
                        rwa [heq] at this
              have := hkey args 0 i ai hgi hinner
              simpa using this

/-! ## Position-append algebra for the nested peak

Two facts to descend a concatenated position: reading along `p ++ q` reads at `p`
then continues at `q`; and replacing along `p ++ q` replaces within the subterm at
`p`. Both descend the position path by structural recursion on the term. They turn
a nested peak (one redex below the other) into a peak inside the shared subterm. -/

/-- Reading along a concatenated position reads at the prefix then continues at the
suffix: `subtermAt t (p ++ q) = (subtermAt t p).bind (subtermAt · q)`. By structural
induction on `t` and the prefix path. -/
theorem Term.subtermAt_append :
    ∀ (t : Term sigma nu) (p q : Pos),
      Term.subtermAt t (p ++ q) = (Term.subtermAt t p).bind (fun a => Term.subtermAt a q) := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro p q
      cases p with
      | nil => simp
      | cons i p => simp
  | happ f args ih =>
      intro p q
      cases p with
      | nil => simp
      | cons i p =>
          rw [List.cons_append, Term.subtermAt_app_cons, Term.subtermAt_app_cons]
          cases hgi : args[i]? with
          | none => simp
          | some a =>
              have hmem : a ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, ha⟩ := hgi; exact ha ▸ List.getElem_mem _
              simp only []
              exact ih a hmem p q

/-- Replacing along a concatenated position replaces within the subterm at the
prefix: if `subtermAt t p = some a`, then
`replaceAt t (p ++ q) s = replaceAt t p (replaceAt a q s)`. By structural induction
on `t` and the prefix path. -/
theorem Term.replaceAt_append :
    ∀ (t : Term sigma nu) (p q : Pos) (a s : Term sigma nu),
      Term.subtermAt t p = some a →
        Term.replaceAt t (p ++ q) s = Term.replaceAt t p (Term.replaceAt a q s) := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro p q a s hsub
      cases p with
      | nil => rw [Term.subtermAt_nil, Option.some.injEq] at hsub; subst hsub; simp
      | cons i p => simp only [Term.subtermAt_var_cons, reduceCtorEq] at hsub
  | happ f args ih =>
      intro p q a s hsub
      cases p with
      | nil => rw [Term.subtermAt_nil, Option.some.injEq] at hsub; subst hsub; simp
      | cons i p =>
          rw [Term.subtermAt_app_cons] at hsub
          cases hgi : args[i]? with
          | none => rw [hgi] at hsub; simp at hsub
          | some c =>
              rw [hgi] at hsub
              have hmem : c ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, hc⟩ := hgi; exact hc ▸ List.getElem_mem _
              -- `hsub : subtermAt c p = some a`
              rw [List.cons_append, Term.replaceAt_app_cons, Term.replaceAt_app_cons]
              congr 1
              -- list level: replacing at index `i` along `p ++ q` vs nested replace
              rw [replaceAtList_split s (p ++ q) args i c hgi,
                replaceAtList_split (Term.replaceAt a q s) p args i c hgi]
              rw [ih c hmem p q a s hsub]

/-- Trichotomy of positions: any two positions are parallel, or one is a prefix of
the other. By induction on both lists; equal heads recurse, distinct heads are
parallel, and the empty position is a prefix of everything. -/
theorem Term.Pos.trichotomy :
    ∀ (p q : Pos), Term.Pos.parallel p q ∨ Term.Pos.IsPrefix p q ∨ Term.Pos.IsPrefix q p := by
  intro p
  induction p with
  | nil => intro q; exact Or.inr (Or.inl ⟨q, by simp⟩)
  | cons i p ih =>
      intro q
      cases q with
      | nil => exact Or.inr (Or.inr ⟨i :: p, by simp⟩)
      | cons j q =>
          by_cases hij : i = j
          · subst hij
            rcases ih q with hpar | hpre | hpre
            · -- parallel tails give parallel `i :: ·`
              refine Or.inl ⟨?_, ?_⟩
              · rintro ⟨r, hr⟩
                rw [List.cons_append, List.cons.injEq] at hr
                exact hpar.1 ⟨r, hr.2⟩
              · rintro ⟨r, hr⟩
                rw [List.cons_append, List.cons.injEq] at hr
                exact hpar.2 ⟨r, hr.2⟩
            · obtain ⟨r, hr⟩ := hpre
              exact Or.inr (Or.inl ⟨r, by rw [hr, List.cons_append]⟩)
            · obtain ⟨r, hr⟩ := hpre
              exact Or.inr (Or.inr ⟨r, by rw [hr, List.cons_append]⟩)
          · -- distinct heads are parallel
            refine Or.inl ⟨?_, ?_⟩
            · rintro ⟨r, hr⟩
              rw [List.cons_append, List.cons.injEq] at hr
              exact hij hr.1.symm
            · rintro ⟨r, hr⟩
              rw [List.cons_append, List.cons.injEq] at hr
              exact hij hr.1

/-! ## Renaming commutes with reading positions

Renaming only relabels variables, leaving the term structure intact, so a position
reads the renamed image of whatever it read before. This certifies that a
function-position overlap discovered inside a renamed-rule instance is a
non-variable position of the canonical `Sum.inl`-renamed copy, the form
`criticalPairs_complete` ranges over. -/

/-- Reading a position commutes with renaming: `subtermAt (rename g t) p` is the
renamed image of `subtermAt t p`. By structural induction on `t` and the position
path. -/
theorem Term.subtermAt_rename {nu' : Type v} (g : nu → nu') :
    ∀ (t : Term sigma nu) (p : Pos),
      Term.subtermAt (Term.rename g t) p = (Term.subtermAt t p).map (Term.rename g) := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro p
      cases p with
      | nil => simp
      | cons i p => simp
  | happ f args ih =>
      intro p
      cases p with
      | nil => simp
      | cons i p =>
          rw [Term.rename_app, Term.subtermAt_app_cons, Term.subtermAt_app_cons,
            Term.renameList_eq_map]
          cases hgi : args[i]? with
          | none => rw [List.getElem?_map, hgi]; simp
          | some a =>
              have hmem : a ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, ha⟩ := hgi; exact ha ▸ List.getElem_mem _
              rw [List.getElem?_map, hgi]
              simpa using ih a hmem p

/-! ## Priority 3b, continued: the variable-overlap reconciliation

The variable-overlap case's actual peak contracts one occurrence of a variable's
substitution image, whereas `joinable_of_variable_overlap` replays the contraction
at every occurrence. The bridge below reduces the one-occurrence-rewritten term to
the all-occurrences-rewritten term: the single position is already advanced, the
remaining occurrences advance by the pointwise reduction. The argument-list driver
advances the designated argument (already partly reduced) and the rest pointwise. -/

/-- Argument-list replay with one designated, already-advanced argument: if the
`i`-th argument's already-replaced form `r` reduces to its `τ`-image `apply τ ai`,
and every other argument reduces from its `σ`-image to its `τ`-image, then the
application built from the substituted prefix and the replaced `i`-th slot reduces
to the application of `τ`-images. By induction on the argument list and the index. -/
theorem stepStar_replaceAtList_pointwise (R : TRS sigma nu) {σ τ : Subst sigma nu}
    (hpt : ∀ z, StepStar R (σ z) (τ z)) (f : sigma) :
    ∀ (args : List (Term sigma nu)) (i : Nat) (r : Term sigma nu),
      (∀ ai ∈ args[i]?, StepStar R r (apply τ ai)) →
      ∀ done : List (Term sigma nu),
        StepStar R (Term.app f (done ++ Term.replaceAtList (applyList σ args) i [] r))
          (Term.app f (done ++ applyList τ args)) := by
  intro args
  induction args with
  | nil => intro i r _ done; simpa using StepStar.refl R _
  | cons a as ih =>
      intro i r hr done
      cases i with
      | zero =>
          -- the designated argument sits at the head; the tail replays pointwise
          simp only [applyList_eq_map, List.map_cons, Term.replaceAtList_cons_zero,
            Term.replaceAt_nil]
          have hhead : StepStar R r (apply τ a) := hr a (by simp)
          -- advance the head from `r` to `τ a`
          have h1 : StepStar R
              (Term.app f (done ++ r :: as.map (apply σ)))
              (Term.app f (done ++ apply τ a :: as.map (apply σ))) :=
            StepStar.arg_congr R f done (as.map (apply σ)) hhead
          -- advance the tail from `σ`-images to `τ`-images
          have h2 : StepStar R
              (Term.app f ((done ++ [apply τ a]) ++ as.map (apply σ)))
              (Term.app f ((done ++ [apply τ a]) ++ as.map (apply τ))) := by
            have := stepStar_app_argwise R f (apply σ) (apply τ) as
              (fun b _ => stepStar_of_pointwise_stepStar R hpt b) (done ++ [apply τ a])
            exact this
          have he1 : done ++ apply τ a :: as.map (apply σ)
              = (done ++ [apply τ a]) ++ as.map (apply σ) := by simp
          have he2 : (done ++ [apply τ a]) ++ as.map (apply τ)
              = done ++ apply τ a :: as.map (apply τ) := by simp
          rw [he1] at h1
          rw [he2] at h2
          exact h1.trans h2
      | succ i =>
          -- the head replays pointwise; recurse on the tail with the head appended
          simp only [applyList_cons, Term.replaceAtList_cons_succ]
          have hhead : StepStar R (apply σ a) (apply τ a) :=
            stepStar_of_pointwise_stepStar R hpt a
          have h1 : StepStar R
              (Term.app f (done ++ apply σ a :: Term.replaceAtList (applyList σ as) i [] r))
              (Term.app f ((done ++ [apply τ a]) ++ Term.replaceAtList (applyList σ as) i [] r)) := by
            have := StepStar.arg_congr R f done
              (Term.replaceAtList (applyList σ as) i [] r) hhead
            have he : done ++ apply τ a :: Term.replaceAtList (applyList σ as) i [] r
                = (done ++ [apply τ a]) ++ Term.replaceAtList (applyList σ as) i [] r := by simp
            rw [he] at this; exact this
          have h2 := ih i r (by simpa using hr) (done ++ [apply τ a])
          have he2 : (done ++ [apply τ a]) ++ applyList τ as
              = done ++ apply τ a :: applyList τ as := by simp
          rw [he2] at h2
          exact h1.trans h2

/-- The variable-overlap reconciliation: the one-occurrence-rewritten term reduces
to the all-occurrences-rewritten term. With `subtermAt u pv = some (var x)`, the
term `σ • u` with its occurrence at `pv` replaced by `τ x` reduces to `τ • u`, given
`∀ z, StepStar R (σ z) (τ z)`. By structural induction on `u` and the variable path:
at the variable both sides equal `τ x`; inside an application the designated
argument is reconciled by the induction hypothesis and the rest replay pointwise
through `stepStar_replaceAtList_pointwise`. -/
theorem stepStar_replaceAt_pointwise (R : TRS sigma nu) {σ τ : Subst sigma nu}
    (hpt : ∀ z, StepStar R (σ z) (τ z)) (x : nu) :
    ∀ (u : Term sigma nu) (pv : Pos), Term.subtermAt u pv = some (Term.var x) →
      StepStar R (Term.replaceAt (σ • u) pv (τ x)) (τ • u) := by
  intro u
  induction u using Term.rec' with
  | hvar y =>
      intro pv hpv
      cases pv with
      | nil =>
          rw [Term.subtermAt_nil, Option.some.injEq] at hpv
          -- `var y = var x` forces `y = x`
          have hyx : y = x := by injection hpv
          subst hyx
          rw [apply_var, Term.replaceAt_nil, apply_var]
          exact StepStar.refl R _
      | cons i pv => simp only [Term.subtermAt_var_cons, reduceCtorEq] at hpv
  | happ f args ih =>
      intro pv hpv
      cases pv with
      | nil =>
          rw [Term.subtermAt_nil, Option.some.injEq] at hpv
          -- an application is never a variable
          exact absurd hpv.symm (by simp)
      | cons i pv =>
          rw [Term.subtermAt_app_cons] at hpv
          cases hgi : args[i]? with
          | none => rw [hgi] at hpv; simp at hpv
          | some a =>
              rw [hgi] at hpv
              have hmem : a ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, ha⟩ := hgi; exact ha ▸ List.getElem_mem _
              -- the designated argument is reconciled by the induction hypothesis
              have hrec : StepStar R (Term.replaceAt (σ • a) pv (τ x)) (τ • a) :=
                ih a hmem pv hpv
              -- assemble through the argument-list replay with empty prefix
              rw [apply_app, apply_app, Term.replaceAt_app_cons]
              -- `replaceAt (σ•app f args) (i::pv) (τ x)` exposes the list replacement
              have hkey := stepStar_replaceAtList_pointwise R hpt f args i
                (Term.replaceAt (σ • a) pv (τ x)) ?_ []
              · -- relate the empty-prefix list replacement to the descended replacement
                have hsplit : Term.replaceAtList (applyList σ args) i [] (Term.replaceAt (σ • a) pv (τ x))
                    = Term.replaceAtList (applyList σ args) i pv (τ x) := by
                  -- both replace the `i`-th argument; `replaceAt (σ•a) pv (τ x)` is the
                  -- descended replacement, `replaceAt (σ•a) [] (...)` the empty one
                  rw [replaceAtList_split (Term.replaceAt (σ • a) pv (τ x)) [] (applyList σ args) i
                        (σ • a) (by rw [applyList_eq_map, List.getElem?_map, hgi]; rfl),
                      replaceAtList_split (τ x) pv (applyList σ args) i (σ • a)
                        (by rw [applyList_eq_map, List.getElem?_map, hgi]; rfl)]
                  rw [Term.replaceAt_nil]
                simpa [hsplit] using hkey
              · -- the designated-argument hypothesis for the list replay
                intro ai hai
                rw [hgi, Option.mem_def, Option.some.injEq] at hai
                rw [← hai]; exact hrec

/-! ## Priority 3: the nested-overlap case and the full backward direction

A nested peak contracts the inner redex strictly inside the outer redex `σ1 • r1.lhs`.
The position classification `subtermAt_apply_cases` splits it: the inner redex either
sits at a non-variable position of `r1.lhs` (the critical overlap, closed by
`criticalPairs_complete` and `joinable_subst`) or descends through a variable of
`r1.lhs` (the variable overlap, closed by `joinable_of_variable_overlap` after the
one-occurrence/all-occurrences reconciliation `stepStar_replaceAt_pointwise`). The
trichotomy `Term.Pos.trichotomy` then reduces every peak to this nested case or the
disjoint case `joinable_of_parallel_peak`. -/

/-- The nested-overlap case: a peak whose outer redex is a root contraction of a
rule `r1 ∈ renameTRS R` of the whole term `w = σ1 • r1.lhs`, and whose inner redex
is a root contraction at a position `q` strictly inside `w`, is joinable in
`renameTRS R`, given critical-pair joinability. The classification of `q` inside the
substitution instance `σ1 • r1.lhs` splits the proof: a function position is a
critical overlap closed by completeness; a variable position is a variable overlap
closed by the multi-occurrence replay. -/
theorem joinable_nested_of_cp_joinable [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (hcp : ∀ p ∈ criticalPairs R, joinable (renameTRS R) p.1 p.2)
    {r1 : Rule sigma (RenVar nu)} (hr1 : r1 ∈ renameTRS R) {σ1 : Subst sigma (RenVar nu)}
    {q : Pos} {a2 b2 : Term sigma (RenVar nu)}
    (hsub : Term.subtermAt (σ1 • r1.lhs) q = some a2)
    (hroot2 : rootStep (renameTRS R) a2 b2) :
    joinable (renameTRS R) (σ1 • r1.rhs) (Term.replaceAt (σ1 • r1.lhs) q b2) := by
  obtain ⟨rule2, hrule2, σ2, ha2, hb2⟩ := hroot2
  rcases subtermAt_apply_cases σ1 r1.lhs q a2 hsub with
    ⟨sub, hsubr, happ, hred⟩ | ⟨pv, x, pr, hq, hpv, hpr⟩
  · -- critical overlap: the inner redex sits at a function position of `r1.lhs`
    -- `r1 = renameRule g1 r01` and `rule2 = renameRule g2 r02` for original rules
    rw [mem_renameTRS_iff] at hr1 hrule2
    -- the common instance equation at this position: `σ1 • sub = a2 = σ2 • rule2.lhs`
    have hcommon0 : σ1 • sub = σ2 • rule2.lhs := by rw [← hred, ha2]
    -- reduce to original rules through the recombined substitution
    obtain ⟨r01, hr01, hr1eq⟩ : ∃ r ∈ R, r1 = renameRule (renL nu) r ∨ r1 = renameRule (renR nu) r := by
      rcases hr1 with ⟨r, hr, h⟩ | ⟨r, hr, h⟩
      exacts [⟨r, hr, Or.inl h⟩, ⟨r, hr, Or.inr h⟩]
    obtain ⟨r02, hr02, hr2eq⟩ : ∃ r ∈ R, rule2 = renameRule (renL nu) r ∨ rule2 = renameRule (renR nu) r := by
      rcases hrule2 with ⟨r, hr, h⟩ | ⟨r, hr, h⟩
      exacts [⟨r, hr, Or.inl h⟩, ⟨r, hr, Or.inr h⟩]
    -- the two rule injections, read off the membership decomposition
    obtain ⟨g1, hg1⟩ : ∃ g : nu → RenVar nu, r1 = renameRule g r01 := by
      rcases hr1eq with h | h; exacts [⟨renL nu, h⟩, ⟨renR nu, h⟩]
    obtain ⟨g2, hg2⟩ : ∃ g : nu → RenVar nu, rule2 = renameRule g r02 := by
      rcases hr2eq with h | h; exacts [⟨renL nu, h⟩, ⟨renR nu, h⟩]
    -- the original lhs subterm and its renamed lift along `g1`
    have hsub0 : ∃ sub0, Term.subtermAt r01.lhs q = some sub0 ∧ sub = Term.rename g1 sub0 := by
      have := Term.subtermAt_rename g1 r01.lhs q
      rw [hg1, renameRule_lhs] at hsubr
      rw [hsubr] at this
      cases hs0 : Term.subtermAt r01.lhs q with
      | none => rw [hs0] at this; simp at this
      | some sub0 => rw [hs0] at this; exact ⟨sub0, rfl, by simpa using this⟩
    obtain ⟨sub0, hsub0eq, hsubsub0⟩ := hsub0
    -- the combined substitution feeding both apart copies their assignment
    set ν : Subst sigma (RenVar nu) :=
      Sum.elim (fun y => σ1 (g1 y)) (fun y => σ2 (g2 y)) with hν
    have hνl : ∀ y, ν (Sum.inl y) = σ1 (g1 y) := fun _ => rfl
    have hνr : ∀ y, ν (Sum.inr y) = σ2 (g2 y) := fun _ => rfl
    -- the subterm of the inl-renamed `r01.lhs` at `q`, and that it is an application
    have hsubren : Term.subtermAt (renameRule (renL nu) r01).lhs q = some (Term.rename (renL nu) sub0) := by
      rw [renameRule_lhs, Term.subtermAt_rename, hsub0eq]; rfl
    have happ' : (Term.rename (renL nu) sub0).isApp = true := by
      rw [Term.isApp_rename]
      have : sub.isApp = true := happ
      rw [hsubsub0, Term.isApp_rename] at this; exact this
    have hpmem : q ∈ nonVarPositions (renameRule (renL nu) r01).lhs :=
      mem_nonVarPositions_of_subtermAt _ q _ hsubren happ'
    -- the common-instance hypothesis over the shared carrier at position `q`
    have hcommon : ν • Term.rename (renL nu) sub0 = ν • (renameRule (renR nu) r02).lhs := by
      have hL : ν • Term.rename (renL nu) sub0 = σ1 • Term.rename g1 sub0 :=
        apply_rename_congr ν σ1 (renL nu) g1 (fun y => hνl y) sub0
      have hR : ν • (renameRule (renR nu) r02).lhs = σ2 • Term.rename g2 r02.lhs := by
        rw [renameRule_lhs]; exact apply_rename_congr ν σ2 (renR nu) g2 (fun y => hνr y) r02.lhs
      rw [hL, hR, ← hsubsub0, hcommon0, hg2, renameRule_lhs]
    -- completeness names the emitted pair and the residual substitution
    obtain ⟨c1, c2, hmem, ρ, hc1, hc2⟩ :=
      criticalPairs_complete hr01 hr02 hpmem hsubren hcommon
    have hjoin : joinable (renameTRS R) (ρ • c1) (ρ • c2) :=
      joinable_subst (renameTRS R) ρ (hcp (c1, c2) hmem)
    -- rewrite the peak's two reducts as `ρ • c1` and `ρ • c2`
    have hleft : σ1 • r1.rhs = ρ • c1 := by
      rw [renameRule_rhs] at hc1
      rw [hg1, renameRule_rhs]
      rw [← hc1]; exact (apply_rename_congr ν σ1 (renL nu) g1 (fun y => hνl y) r01.rhs).symm
    have hright : Term.replaceAt (σ1 • r1.lhs) q b2 = ρ • c2 := by
      -- `ν • replaceAt (rename renL r01.lhs) q (rename renR r02.rhs) = ρ • c2`
      rw [renameRule_lhs] at hc2
      -- push `ν` inside the replacement using `replaceAt_apply`
      rw [← replaceAt_apply ν (renameRule (renR nu) r02).rhs (Term.rename (renL nu) r01.lhs) q
            (Term.rename (renL nu) sub0) (by rw [Term.subtermAt_rename, hsub0eq]; rfl)] at hc2
      -- the two pieces of the replacement match the peak
      have hwhole : ν • Term.rename (renL nu) r01.lhs = σ1 • r1.lhs := by
        rw [hg1, renameRule_lhs]
        exact apply_rename_congr ν σ1 (renL nu) g1 (fun y => hνl y) r01.lhs
      have hfill : ν • (renameRule (renR nu) r02).rhs = b2 := by
        rw [renameRule_rhs, hb2, hg2, renameRule_rhs]
        exact apply_rename_congr ν σ2 (renR nu) g2 (fun y => hνr y) r02.rhs
      rw [hwhole, hfill] at hc2
      exact hc2
    rw [hleft, hright]; exact hjoin
  · -- variable overlap: the inner redex descends through a variable `x` of `r1.lhs`
    -- the substitution `τ` advancing the contracted occurrence of `σ1 x`
    classical
    -- the contracting step at position `pr` inside `σ1 x`, reconstructed
    have hstepin : Step (renameTRS R) a2 b2 := Step.root ⟨rule2, hrule2, σ2, ha2, hb2⟩
    set τ : Subst sigma (RenVar nu) :=
      fun z => if z = x then Term.replaceAt (σ1 z) pr b2 else σ1 z with hτ
    have hτx : τ x = Term.replaceAt (σ1 x) pr b2 := by rw [hτ]; simp
    -- every variable image reduces from `σ1` to `τ`
    have hpt : ∀ z, StepStar (renameTRS R) (σ1 z) (τ z) := by
      intro z
      by_cases hz : z = x
      · rw [hz, hτx]
        -- one step inside `σ1 x` at position `pr`, contracting `a2 → b2`
        exact StepStar.single (Step.at_pos (renameTRS R) (σ1 x) pr a2 b2 hpr hstepin)
      · rw [hτ]; simp only [if_neg hz]; exact StepStar.refl _ _
    -- the variable-overlap join: common reduct `τ • r1.rhs`
    obtain ⟨w, hbw, hlw⟩ := joinable_of_variable_overlap (renameTRS R) hr1 hpt
    -- the actual second reduct reduces to `τ • r1.lhs`, hence to the common reduct
    have ht2 : Term.replaceAt (σ1 • r1.lhs) q b2 = Term.replaceAt (σ1 • r1.lhs) pv (τ x) := by
      -- `replaceAt _ (pv ++ pr) b2 = replaceAt _ pv (replaceAt (σ1 x) pr b2) = replaceAt _ pv (τ x)`
      have hsubpv : Term.subtermAt (σ1 • r1.lhs) pv = some (σ1 x) := by
        have := subtermAt_apply σ1 r1.lhs pv (Term.var x) hpv
        rwa [apply_var] at this
      rw [hq, Term.replaceAt_append (σ1 • r1.lhs) pv pr (σ1 x) b2 hsubpv, hτx]
    have hredto : StepStar (renameTRS R) (Term.replaceAt (σ1 • r1.lhs) q b2) (τ • r1.lhs) := by
      rw [ht2]; exact stepStar_replaceAt_pointwise (renameTRS R) hpt x r1.lhs pv hpv
    -- assemble: `σ1•r1.rhs ↠ w` and `replaceAt … ↠ τ•r1.lhs ↠ w`
    exact ⟨w, hbw, hredto.trans hlw⟩

/-- A one-step rewrite is either a root contraction, or it descends strictly into
one argument: `Step R s t` either is `rootStep R s t`, or `s = app f (pre ++ a :: post)`,
`t = app f (pre ++ b :: post)` with `Step R a b`. The structural split of the `Step`
constructor, the entry point for separating root from contextual peaks. -/
theorem Step.rootStep_or_arg (R : TRS sigma nu) {s t : Term sigma nu} (h : Step R s t) :
    rootStep R s t ∨
      ∃ (f : sigma) (pre post : List (Term sigma nu)) (a b : Term sigma nu),
        s = .app f (pre ++ a :: post) ∧ t = .app f (pre ++ b :: post) ∧ Step R a b := by
  cases h with
  | root hroot => exact Or.inl hroot
  | @arg f pre post a b hstep => exact Or.inr ⟨f, pre, post, a, b, rfl, rfl, hstep⟩

/-! ## Priority 3/4: the full backward direction and the Critical Pair Lemma

Every one-step peak of `renameTRS R` reduces, by `Step.exists_pos_rootStep` and the
position trichotomy `Term.Pos.trichotomy`, to the disjoint case
(`joinable_of_parallel_peak`) or the nested case (`joinable_nested_of_cp_joinable`).
This gives the backward direction; pairing it with the forward direction
`localConfluent_imp_cp_joinable` yields the biconditional, and composing with the
generic Newman lemma `confluent_of_wf_of_localConfluent` yields confluence under
strong normalization. -/

/-- The full backward direction of the Critical Pair Lemma: if every critical pair
of `R` is joinable in `renameTRS R`, then `renameTRS R` is locally confluent. Each
peak's two redexes sit at positions `p1, p2`. When the positions are parallel the
contractions commute (`joinable_of_parallel_peak`); when one position is a prefix of
the other the inner contraction happens inside the outer redex
(`joinable_nested_of_cp_joinable`), which the position classification splits into a
critical overlap closed by `criticalPairs_complete` and a variable overlap closed by
`joinable_of_variable_overlap`. This covers every peak of `renameTRS R`, including
those between two left-summand or two right-summand copies of a rule. -/
theorem cp_joinable_imp_localConfluent [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (hcp : ∀ p ∈ criticalPairs R, joinable (renameTRS R) p.1 p.2) :
    localConfluent (renameTRS R) := by
  intro s t1 t2 hstep1 hstep2
  obtain ⟨p1, a1, b1, hsub1, hroot1, ht1⟩ := Step.exists_pos_rootStep (renameTRS R) hstep1
  obtain ⟨p2, a2, b2, hsub2, hroot2, ht2⟩ := Step.exists_pos_rootStep (renameTRS R) hstep2
  subst ht1; subst ht2
  rcases Term.Pos.trichotomy p1 p2 with hpar | hpre | hpre
  · -- disjoint case: the two contractions commute
    exact joinable_of_parallel_peak (renameTRS R) s p1 p2 hsub1 hsub2 hpar
      (Step.root hroot1) (Step.root hroot2)
  · -- `p1` is a prefix of `p2`: the second redex is nested inside the first
    obtain ⟨p2', rfl⟩ := hpre
    obtain ⟨rule1, hrule1, σ1, ha1, hb1⟩ := hroot1
    -- the inner redex read inside the outer redex `a1 = σ1 • rule1.lhs`
    have hsubin : Term.subtermAt (σ1 • rule1.lhs) p2' = some a2 := by
      have happ := Term.subtermAt_append s p1 p2'
      rw [hsub1, Option.bind_some] at happ
      rw [← ha1]; rw [happ] at hsub2; exact hsub2
    -- the nested-overlap join inside `a1`
    have hjoin : joinable (renameTRS R) (σ1 • rule1.rhs)
        (Term.replaceAt (σ1 • rule1.lhs) p2' b2) :=
      joinable_nested_of_cp_joinable hcp hrule1 hsubin hroot2
    -- lift the join from the subterm at `p1` to the whole term `s`
    have hvalid : Term.ValidPos s p1 := Term.validPos_of_subtermAt hsub1
    have hlift := joinable_at_pos (renameTRS R) s p1 hvalid hjoin
    -- identify the two lifted reducts with `t1` and `t2`
    have hrep : Term.replaceAt s (p1 ++ p2') b2 = Term.replaceAt s p1 (Term.replaceAt a1 p2' b2) :=
      Term.replaceAt_append s p1 p2' a1 b2 hsub1
    rw [hb1, hrep, ha1]
    exact hlift
  · -- `p2` is a prefix of `p1`: symmetric to the previous case
    obtain ⟨p1', rfl⟩ := hpre
    obtain ⟨rule2, hrule2, σ2, ha2, hb2⟩ := hroot2
    have hsubin : Term.subtermAt (σ2 • rule2.lhs) p1' = some a1 := by
      have happ := Term.subtermAt_append s p2 p1'
      rw [hsub2, Option.bind_some] at happ
      rw [← ha2]; rw [happ] at hsub1; exact hsub1
    have hjoin : joinable (renameTRS R) (σ2 • rule2.rhs)
        (Term.replaceAt (σ2 • rule2.lhs) p1' b1) :=
      joinable_nested_of_cp_joinable hcp hrule2 hsubin hroot1
    have hvalid : Term.ValidPos s p2 := Term.validPos_of_subtermAt hsub2
    have hlift := joinable_at_pos (renameTRS R) s p2 hvalid hjoin
    refine joinable.symm ?_
    -- read the subterm at `p2` as `σ2 • rule2.lhs` and split the nested replacement
    have hsub2' : Term.subtermAt s p2 = some (σ2 • rule2.lhs) := by rw [← ha2]; exact hsub2
    have hrep : Term.replaceAt s (p2 ++ p1') b1
        = Term.replaceAt s p2 (Term.replaceAt (σ2 • rule2.lhs) p1' b1) :=
      Term.replaceAt_append s p2 p1' (σ2 • rule2.lhs) b1 hsub2'
    rw [hb2, hrep]
    exact hlift

/-- The Critical Pair Lemma (Knuth-Bendix/Huet), full biconditional: `renameTRS R`
is locally confluent if and only if every critical pair of `R` is joinable in
`renameTRS R`. The forward direction is `localConfluent_imp_cp_joinable` (each
critical pair is a peak, joined by local confluence); the backward direction is
`cp_joinable_imp_localConfluent` (every peak reduces, by the position trichotomy, to
a parallel, variable, or critical overlap, each joinable). -/
theorem critical_pair_lemma [DecidableEq sigma] [DecidableEq nu] (R : TRS sigma nu) :
    localConfluent (renameTRS R) ↔
      ∀ q ∈ criticalPairs R, joinable (renameTRS R) q.1 q.2 :=
  ⟨fun hlc => localConfluent_imp_cp_joinable hlc, fun hcp => cp_joinable_imp_localConfluent hcp⟩

/-- Confluence from joinable critical pairs and strong normalization: if every
critical pair of `R` is joinable in `renameTRS R` and the one-step relation
`Step (renameTRS R)` is strongly normalizing (its reverse is well-founded), then
`StepStar (renameTRS R)` is confluent. The Critical Pair Lemma supplies local
confluence; the generic Newman lemma `confluent_of_wf_of_localConfluent` upgrades it
to confluence under strong normalization. This is the standard route to a decision
procedure for confluence of a terminating system. -/
theorem confluent_of_cp_joinable_of_SN [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu}
    (hSN : WellFounded (fun x y : Term sigma (RenVar nu) => Step (renameTRS R) y x))
    (hcp : ∀ q ∈ criticalPairs R, joinable (renameTRS R) q.1 q.2) :
    ∀ a b c, StepStar (renameTRS R) a b → StepStar (renameTRS R) a c →
      ∃ d, StepStar (renameTRS R) b d ∧ StepStar (renameTRS R) c d := by
  have hlc : localConfluent (renameTRS R) := (critical_pair_lemma R).2 hcp
  have hlc' : AbsLocalConfluent (Step (renameTRS R)) :=
    fun a b c hab hac => hlc a b c hab hac
  exact confluent_of_wf_of_localConfluent (Step (renameTRS R)) hSN hlc'

end OperatorKO7.Meta.Rewriting

/-! ## Verification: headline types and axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @overlapAt_complete
open OperatorKO7.Meta.Rewriting in
#check @criticalPairs_complete
open OperatorKO7.Meta.Rewriting in
#check @subtermAt_apply_cases
open OperatorKO7.Meta.Rewriting in
#check @mem_nonVarPositions_of_subtermAt
open OperatorKO7.Meta.Rewriting in
#check @joinable_rootOverlap_of_cp_joinable
open OperatorKO7.Meta.Rewriting in
#check @stepStar_replaceAt_pointwise
open OperatorKO7.Meta.Rewriting in
#check @joinable_nested_of_cp_joinable
open OperatorKO7.Meta.Rewriting in
#check @Step.rootStep_or_arg
open OperatorKO7.Meta.Rewriting in
#check @cp_joinable_imp_localConfluent
open OperatorKO7.Meta.Rewriting in
#check @critical_pair_lemma
open OperatorKO7.Meta.Rewriting in
#check @confluent_of_cp_joinable_of_SN

#print axioms OperatorKO7.Meta.Rewriting.overlapAt_complete
#print axioms OperatorKO7.Meta.Rewriting.mem_criticalPairs_of_overlapAt
#print axioms OperatorKO7.Meta.Rewriting.criticalPairs_complete
#print axioms OperatorKO7.Meta.Rewriting.apply_rename_congr
#print axioms OperatorKO7.Meta.Rewriting.mem_renameTRS_iff
#print axioms OperatorKO7.Meta.Rewriting.joinable_rootOverlap_of_cp_joinable
#print axioms OperatorKO7.Meta.Rewriting.subtermAt_apply_cases
#print axioms OperatorKO7.Meta.Rewriting.mem_nonVarPositions_of_subtermAt
#print axioms OperatorKO7.Meta.Rewriting.Term.subtermAt_append
#print axioms OperatorKO7.Meta.Rewriting.Term.replaceAt_append
#print axioms OperatorKO7.Meta.Rewriting.Term.Pos.trichotomy
#print axioms OperatorKO7.Meta.Rewriting.Term.subtermAt_rename
#print axioms OperatorKO7.Meta.Rewriting.stepStar_replaceAtList_pointwise
#print axioms OperatorKO7.Meta.Rewriting.stepStar_replaceAt_pointwise
#print axioms OperatorKO7.Meta.Rewriting.joinable_nested_of_cp_joinable
#print axioms OperatorKO7.Meta.Rewriting.Step.rootStep_or_arg
#print axioms OperatorKO7.Meta.Rewriting.cp_joinable_imp_localConfluent
#print axioms OperatorKO7.Meta.Rewriting.critical_pair_lemma
#print axioms OperatorKO7.Meta.Rewriting.confluent_of_cp_joinable_of_SN
