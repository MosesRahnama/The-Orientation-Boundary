import OperatorKO7.Meta.Rewriting.UnifyCorrect
import OperatorKO7.Meta.Rewriting.Rewrite
import OperatorKO7.Meta.Rewriting.Position

/-!
# Critical pairs of a first-order term rewriting system

Roadmap source: `ROADMAP-01-generic-critical-pair-lemma.md`, sections 3 (the
three redex-overlap cases and the critical-overlap notion), 4, and 5
(`Meta/Rewriting/CriticalPair.lean` signatures). This is Wave 3B: the
critical-pair construction that genuinely enumerates the overlaps of a term
rewriting system, plus the soundness theorem that every emitted pair is a real
overlap peak.

## What this module delivers

- A clean variable-renaming scheme so two rules overlap without variable
  capture: rule 1 is renamed through `Sum.inl` and rule 2 through `Sum.inr`,
  mapping both into the shared variable carrier `Sum nu nu`. The images carry
  disjoint variable sets (`renameRule_vars_disjoint`), so the most-general
  unifier of an overlapped subterm acts on independent variables. `renameRule`
  preserves the left-hand-side-is-application invariant
  (`renameRule`, `Term.isApp_rename`).

- `nonVarPositions t`: the positions of `t` whose subterm is an application,
  i.e. the non-variable (function) positions, the root included. These are
  exactly the positions at which a genuine (non-variable) overlap can occur.
  `nonVarPositions_sound` confirms each enumerated position carries an `app`
  subterm.

- `criticalPairs R`: for every ordered pair of rules `(r1, r2)` of `R` (with
  `r2` renamed apart from `r1`), every non-variable position `p` of `r1`'s
  left-hand side, and the most-general unifier `μ` of the subterm at `p` with
  `r2`'s left-hand side, the critical pair
  `(μ • r1.rhs, μ • replaceAt r1.lhs p r2.rhs)`. The `Option` from `subtermAt`
  is consumed cleanly: a pair is emitted exactly when both the subterm read and
  the unification succeed.

- `criticalPairs_sound`: every emitted critical pair `(s, t)` is a genuine
  overlap peak. With `w = μ • r1.lhs` the unified redex, `w` rewrites by `r1`
  at the root to `s` and by `r2` at the overlap position `p` to `t`, both as
  `Step` rewrites in the renamed system `renameTRS R`. The rule-2 contraction at
  `p` rests on `unify_sound` (Wave 3A `UnifyCorrect.lean`).

- `criticalPairs_demoTRS` / `demo_criticalPair_is_peak`: a concrete two-rule
  system whose `criticalPairs` is a specific non-empty list, with a witness that
  one emitted pair is a real peak.

Trust: kernel-only; baseline-only under `#print axioms` (subset of
`{propext, Classical.choice, Quot.sound}`). Any `Classical.choice`/`propext`
dependence is from `Finset`/`DecidableEq` plumbing inherited through the
foundation modules.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open scoped Subst
open Subst

universe u v w

variable {sigma : Type u} {nu : Type v}

/-! ## Substitution commutes with positions

Two structural lemmas connecting `Subst.apply` with `subtermAt`/`replaceAt` at a
valid position. They are the bridge that turns a unifier of an overlapped
subterm into a genuine rewrite peak: a valid position descends purely through
`app` nodes, so substituting keeps the same shape down to `p`. -/

/-- Reading the subterm at a position commutes with substitution: if the subterm
of `u` at `p` is `sub`, then the subterm of `σ • u` at `p` is `σ • sub`. -/
theorem subtermAt_apply (σ : Subst sigma nu) :
    ∀ (u : Term sigma nu) (p : Pos) (sub : Term sigma nu),
      Term.subtermAt u p = some sub → Term.subtermAt (σ • u) p = some (σ • sub) := by
  intro u
  induction u using Term.rec' with
  | hvar x =>
      intro p sub hsub
      cases p with
      | nil =>
          simp only [Term.subtermAt_nil, Option.some.injEq] at hsub
          subst hsub; simp
      | cons i p => simp only [Term.subtermAt_var_cons, reduceCtorEq] at hsub
  | happ f args ih =>
      intro p sub hsub
      cases p with
      | nil =>
          simp only [Term.subtermAt_nil, Option.some.injEq] at hsub
          subst hsub; simp
      | cons i p =>
          rw [Term.subtermAt_app_cons] at hsub
          rw [apply_app, Term.subtermAt_app_cons, applyList_eq_map]
          cases hgi : args[i]? with
          | none => rw [hgi] at hsub; simp at hsub
          | some a =>
              rw [hgi] at hsub
              have hmap : (args.map (apply σ))[i]? = some (apply σ a) := by
                rw [List.getElem?_map, hgi]; rfl
              rw [hmap]
              have hmem : a ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, ha⟩ := hgi; exact ha ▸ List.getElem_mem _
              exact ih a hmem p sub hsub

/-- The argument-list split read off a `getElem?`: an argument list is its
prefix, its element `c` at index `i`, and its suffix. -/
theorem list_eq_take_cons_drop :
    ∀ (args : List (Term sigma nu)) (i : Nat) (c : Term sigma nu), args[i]? = some c →
      args = args.take i ++ c :: args.drop (i + 1) := by
  intro args
  induction args with
  | nil => intro i c hi; simp at hi
  | cons a as ih =>
      intro i c hi
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi; simp
      | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
            List.cons.injEq, true_and]
          exact ih i c hi

/-- The `replaceAtList` companion of `list_eq_take_cons_drop`: replacing at index
`i` splits into the prefix, the recursively replaced element `c`, and the
suffix. -/
theorem replaceAtList_split (s : Term sigma nu) (p : Pos) :
    ∀ (args : List (Term sigma nu)) (i : Nat) (c : Term sigma nu), args[i]? = some c →
      Term.replaceAtList args i p s
        = args.take i ++ Term.replaceAt c p s :: args.drop (i + 1) := by
  intro args
  induction args with
  | nil => intro i c hi; simp at hi
  | cons a as ih =>
      intro i c hi
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi; simp
      | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          simp only [Term.replaceAtList_cons_succ, List.take_succ_cons,
            List.drop_succ_cons, List.cons_append]
          rw [ih i c hi]

/-- The list driver for `replaceAt_apply`: substituting across a list-replacement
equals replacing across the substituted list, given the per-element commutation
at the replaced element. By induction on the list and the index. -/
theorem replaceAtList_apply (σ : Subst sigma nu) (r : Term sigma nu) (p : Pos) :
    ∀ (args : List (Term sigma nu)) (i : Nat) (a : Term sigma nu), args[i]? = some a →
      Term.replaceAt (σ • a) p (σ • r) = σ • Term.replaceAt a p r →
        Term.replaceAtList (applyList σ args) i p (σ • r)
          = applyList σ (Term.replaceAtList args i p r) := by
  intro args
  induction args with
  | nil => intro i a hi _; simp at hi
  | cons c cs ih =>
      intro i a hi hcomm
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          simp only [applyList_cons, Term.replaceAtList_cons_zero, hcomm]
      | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          simp only [applyList_cons, Term.replaceAtList_cons_succ]
          rw [ih i a hi hcomm]

/-- Replacing at a valid position commutes with substitution: if the subterm of
`u` at `p` exists, replacing under a substituted term equals substituting into
the replacement, `replaceAt (σ • u) p (σ • r) = σ • replaceAt u p r`. -/
theorem replaceAt_apply (σ : Subst sigma nu) (r : Term sigma nu) :
    ∀ (u : Term sigma nu) (p : Pos) (sub : Term sigma nu),
      Term.subtermAt u p = some sub →
        Term.replaceAt (σ • u) p (σ • r) = σ • Term.replaceAt u p r := by
  intro u
  induction u using Term.rec' with
  | hvar x =>
      intro p sub hsub
      cases p with
      | nil => simp
      | cons i p => simp only [Term.subtermAt_var_cons, reduceCtorEq] at hsub
  | happ f args ih =>
      intro p sub hsub
      cases p with
      | nil => simp
      | cons i p =>
          rw [Term.subtermAt_app_cons] at hsub
          cases hgi : args[i]? with
          | none => rw [hgi] at hsub; simp at hsub
          | some a =>
              rw [hgi] at hsub
              have hmem : a ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, ha⟩ := hgi; exact ha ▸ List.getElem_mem _
              rw [apply_app, Term.replaceAt_app_cons, applyList_eq_map,
                Term.replaceAt_app_cons, apply_app, applyList_eq_map]
              rw [← applyList_eq_map, ← applyList_eq_map]
              congr 1
              exact replaceAtList_apply σ r p args i a hgi (ih a hmem p sub hsub)

/-! ## Positional context closure of `Step`

A single rewrite step lifts from a subterm at any valid position to the whole
term, by iterating the `arg` congruence along the position path. This packages
`Step.arg` for arbitrary positions; the soundness theorem uses it to lift a root
rule-2 contraction at position `p` to a step on the whole peak. -/

/-- If the subterm of `u` at a position `p` rewrites by `R` to `b`, then `u`
rewrites by `R` to `u` with that subterm replaced by `b`. The proof iterates the
`arg` congruence down the position path. -/
theorem Step.at_pos (R : TRS sigma nu) :
    ∀ (u : Term sigma nu) (p : Pos) (a b : Term sigma nu),
      Term.subtermAt u p = some a → Step R a b →
        Step R u (Term.replaceAt u p b) := by
  intro u
  induction u using Term.rec' with
  | hvar x =>
      intro p a b hsub hstep
      cases p with
      | nil =>
          simp only [Term.subtermAt_nil, Option.some.injEq] at hsub
          subst hsub; simpa using hstep
      | cons i p => simp only [Term.subtermAt_var_cons, reduceCtorEq] at hsub
  | happ f args ih =>
      intro p a b hsub hstep
      cases p with
      | nil =>
          simp only [Term.subtermAt_nil, Option.some.injEq] at hsub
          subst hsub; simpa using hstep
      | cons i p =>
          rw [Term.subtermAt_app_cons] at hsub
          cases hgi : args[i]? with
          | none => rw [hgi] at hsub; simp at hsub
          | some c =>
              rw [hgi] at hsub
              have hmem : c ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, hc⟩ := hgi; exact hc ▸ List.getElem_mem _
              have hinner : Step R c (Term.replaceAt c p b) := ih c hmem p a b hsub hstep
              have hsplit : args = args.take i ++ c :: args.drop (i + 1) :=
                list_eq_take_cons_drop args i c hgi
              rw [Term.replaceAt_app_cons, replaceAtList_split b p args i c hgi]
              conv_lhs => rw [hsplit]
              exact Step.arg f (args.take i) (args.drop (i + 1)) hinner

/-! ## Variable renaming for capture-free overlap

Two rules are overlapped after renaming their variables apart. The clean, fully
generic scheme maps rule 1 through `Sum.inl` and rule 2 through `Sum.inr` into
the shared carrier `Sum nu nu`, landing their variable sets in the two disjoint
summands. -/

mutual
/-- Rename the variables of a term along `g`, leaving the structure intact. Uses
an auxiliary list form so the nested recursion is structural. -/
def Term.rename {nu' : Type w} (g : nu → nu') : Term sigma nu → Term sigma nu'
  | .var x => .var (g x)
  | .app f args => .app f (Term.renameList g args)
/-- Rename the variables of an argument list along `g`. -/
def Term.renameList {nu' : Type w} (g : nu → nu') :
    List (Term sigma nu) → List (Term sigma nu')
  | [] => []
  | a :: as => Term.rename g a :: Term.renameList g as
end

@[simp] theorem Term.rename_var {nu' : Type w} (g : nu → nu') (x : nu) :
    Term.rename (sigma := sigma) g (.var x) = .var (g x) := rfl
@[simp] theorem Term.rename_app {nu' : Type w} (g : nu → nu') (f : sigma)
    (args : List (Term sigma nu)) :
    Term.rename g (.app f args) = .app f (Term.renameList g args) := rfl
@[simp] theorem Term.renameList_nil {nu' : Type w} (g : nu → nu') :
    Term.renameList (sigma := sigma) g ([] : List (Term sigma nu)) = [] := rfl
@[simp] theorem Term.renameList_cons {nu' : Type w} (g : nu → nu') (a : Term sigma nu)
    (as : List (Term sigma nu)) :
    Term.renameList g (a :: as) = Term.rename g a :: Term.renameList g as := rfl

/-- `renameList` is the `List.map` of `rename`. -/
theorem Term.renameList_eq_map {nu' : Type w} (g : nu → nu')
    (args : List (Term sigma nu)) :
    Term.renameList g args = args.map (Term.rename g) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [Term.renameList_cons, ih]

/-- Renaming preserves the application/variable shape: a renamed application is
an application. -/
theorem Term.isApp_rename {nu' : Type w} (g : nu → nu') (t : Term sigma nu) :
    (Term.rename g t).isApp = t.isApp := by
  cases t <;> rfl

/-- Every variable of a renamed term is a `g`-image of an original variable. The
forward containment is all the disjointness argument needs. -/
theorem Term.vars_rename_mem {nu' : Type w} [DecidableEq nu] [DecidableEq nu']
    (g : nu → nu') :
    ∀ (t : Term sigma nu) (z : nu'),
      z ∈ Term.vars (Term.rename g t) → ∃ y, g y = z := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro z hz
      rw [Term.rename_var, Term.vars_var, Finset.mem_singleton] at hz
      exact ⟨x, hz.symm⟩
  | happ f args ih =>
      intro z hz
      rw [Term.rename_app, Term.vars_app, Term.renameList_eq_map,
        Term.mem_varsList_iff] at hz
      obtain ⟨c, hc, hzc⟩ := hz
      rw [List.mem_map] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      exact ih a ha z hzc

/-- Rename a rule's variables along `g`, preserving the well-formedness invariant
that the left-hand side is an application. -/
def renameRule {nu' : Type w} (g : nu → nu') (rule : Rule sigma nu) :
    Rule sigma nu' where
  lhs := Term.rename g rule.lhs
  rhs := Term.rename g rule.rhs
  lhs_isApp := by rw [Term.isApp_rename]; exact rule.lhs_isApp

@[simp] theorem renameRule_lhs {nu' : Type w} (g : nu → nu') (rule : Rule sigma nu) :
    (renameRule g rule).lhs = Term.rename g rule.lhs := rfl
@[simp] theorem renameRule_rhs {nu' : Type w} (g : nu → nu') (rule : Rule sigma nu) :
    (renameRule g rule).rhs = Term.rename g rule.rhs := rfl

/-- The two-rule renaming carrier: rule 1's variables move to the left summand,
rule 2's to the right summand, so the renamed rules never share a variable. -/
abbrev RenVar (nu : Type v) := Sum nu nu

/-- The renamed system: every rule of `R` appears renamed into the left summand
(for use as rule 1) and renamed into the right summand (for use as rule 2). A
critical pair contracts a left-summand rule at the root and a right-summand rule
at a position, so both renamings must be present. -/
def renameTRS [DecidableEq nu] (R : TRS sigma nu) : TRS sigma (RenVar nu) :=
  R.map (renameRule Sum.inl) ++ R.map (renameRule Sum.inr)

/-- A left-renamed rule belongs to the renamed system. -/
theorem renameRule_inl_mem [DecidableEq nu] {R : TRS sigma nu} {rule : Rule sigma nu}
    (h : rule ∈ R) : renameRule Sum.inl rule ∈ renameTRS R :=
  List.mem_append_left _ (List.mem_map_of_mem h)

/-- A right-renamed rule belongs to the renamed system. -/
theorem renameRule_inr_mem [DecidableEq nu] {R : TRS sigma nu} {rule : Rule sigma nu}
    (h : rule ∈ R) : renameRule Sum.inr rule ∈ renameTRS R :=
  List.mem_append_right _ (List.mem_map_of_mem h)

/-- The variable sets of a left-renamed term and a right-renamed term are
disjoint: the first lands in `Sum.inl`'s image, the second in `Sum.inr`'s, and
those images do not meet. This is the capture-freedom guarantee. -/
theorem renameRule_vars_disjoint [DecidableEq nu] (t1 t2 : Term sigma nu) :
    ∀ z, z ∈ Term.vars (Term.rename (sigma := sigma) (Sum.inl (β := nu)) t1) →
      z ∉ Term.vars (Term.rename (sigma := sigma) (Sum.inr (α := nu)) t2) := by
  intro z hz1 hz2
  obtain ⟨y1, hy1⟩ := Term.vars_rename_mem Sum.inl t1 z hz1
  obtain ⟨y2, hy2⟩ := Term.vars_rename_mem Sum.inr t2 z hz2
  rw [← hy1] at hy2
  exact Sum.noConfusion hy2

/-! ## Non-variable positions

The positions at which a genuine overlap can occur are those whose subterm is an
application. `nonVarPositions` enumerates exactly these, the root included. -/

mutual
/-- The non-variable positions of a term: every position whose subterm is an
application, the root first, then recursively the non-variable positions inside
each argument (prefixed by the argument index). Uses an auxiliary list form so
the nested recursion is structural. -/
def nonVarPositions : Term sigma nu → List Pos
  | .var _ => []
  | .app _ args => [] :: nonVarPositionsList args 0
/-- Non-variable positions inside an argument list, each prefixed by its (running)
argument index. -/
def nonVarPositionsList : List (Term sigma nu) → Nat → List Pos
  | [], _ => []
  | a :: as, i =>
      (nonVarPositions a).map (fun p => i :: p) ++ nonVarPositionsList as (i + 1)
end

@[simp] theorem nonVarPositions_var (x : nu) :
    nonVarPositions (Term.var (sigma := sigma) x) = [] := rfl
@[simp] theorem nonVarPositions_app (f : sigma) (args : List (Term sigma nu)) :
    nonVarPositions (Term.app f args) = [] :: nonVarPositionsList args 0 := rfl

/-- Every position enumerated by `nonVarPositions` reads back an application: the
subterm at such a position exists and is an `app` node. This confirms the
construction targets exactly the function (non-variable) positions, the root
included, so the overlaps it later builds are genuine non-variable overlaps. -/
theorem nonVarPositions_sound :
    ∀ (t : Term sigma nu) (p : Pos), p ∈ nonVarPositions t →
      ∃ f args, Term.subtermAt t p = some (Term.app f args) := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro p hp; simp at hp
  | happ f args ih =>
      -- A non-variable position of `app f args` is either the root, or `i :: q`
      -- for a non-variable position `q` of the `i`-th argument.
      have hlist : ∀ (l : List (Term sigma nu)) (base : Nat),
          (∀ a ∈ l, ∀ q ∈ nonVarPositions a,
            ∃ f args, Term.subtermAt a q = some (Term.app f args)) →
          ∀ p ∈ nonVarPositionsList l base, ∃ i q, p = i :: q ∧
            ∃ a, l[i - base]? = some a ∧ base ≤ i ∧ q ∈ nonVarPositions a := by
        intro l
        induction l with
        | nil => intro base _ p hp; simp [nonVarPositionsList] at hp
        | cons b bs ihl =>
            intro base ihmem p hp
            simp only [nonVarPositionsList, List.mem_append, List.mem_map] at hp
            rcases hp with ⟨q, hq, rfl⟩ | hp
            · refine ⟨base, q, rfl, b, ?_, le_refl _, hq⟩
              simp
            · obtain ⟨i, q, rfl, a, ha, hbase, hq⟩ :=
                ihl (base + 1) (fun c hc => ihmem c (by simp [hc])) p hp
              refine ⟨i, q, rfl, a, ?_, by omega, hq⟩
              have hpos : i - base = (i - (base + 1)) + 1 := by omega
              rw [hpos, List.getElem?_cons_succ]
              exact ha
      intro p hp
      simp only [nonVarPositions_app, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨f, args, by simp⟩
      · obtain ⟨i, q, rfl, a, ha, _, hq⟩ := hlist args 0 (fun a ha => ih a ha) p hp
        obtain ⟨g, bs, hgbs⟩ := ih a (by
          have : a ∈ args := by
            rw [List.getElem?_eq_some_iff] at ha
            obtain ⟨_, hev⟩ := ha; exact hev ▸ List.getElem_mem _
          exact this) q hq
        refine ⟨g, bs, ?_⟩
        rw [Term.subtermAt_app_cons]
        have hi0 : args[i]? = some a := by simpa using ha
        rw [hi0]
        exact hgbs

/-! ## The critical-pair construction

For two rules renamed apart, the overlaps at non-variable positions of rule 1's
left-hand side are enumerated; each successful unification of the overlapped
subterm with rule 2's left-hand side emits one critical pair. `criticalPairs`
runs this over every ordered pair of rules of the system. -/

/-- One overlap step as an `Option`: at position `p` of `r1.lhs`, read the
subterm, unify it with `r2.lhs`, and on success emit the critical pair
`(μ • r1.rhs, μ • replaceAt r1.lhs p r2.rhs)`. Phrasing the body through
`Option.bind` keeps the `Option` plumbing transparent for the soundness proof. -/
def overlapAt [DecidableEq sigma] [DecidableEq nu]
    (r1 r2 : Rule sigma (RenVar nu)) (p : Pos) :
    Option (Term sigma (RenVar nu) × Term sigma (RenVar nu)) :=
  (Term.subtermAt r1.lhs p).bind (fun sub =>
    (unify sub r2.lhs).map (fun μ =>
      (μ • r1.rhs, μ • Term.replaceAt r1.lhs p r2.rhs)))

/-- The critical pairs produced by overlapping `r2` into `r1` (both already
renamed apart): for each non-variable position `p` of `r1.lhs` whose subterm
unifies with `r2.lhs`, the emitted pair `overlapAt r1 r2 p`. A pair is emitted
exactly when both the subterm read and the unification succeed. -/
def overlapPairs [DecidableEq sigma] [DecidableEq nu]
    (r1 r2 : Rule sigma (RenVar nu)) :
    List (Term sigma (RenVar nu) × Term sigma (RenVar nu)) :=
  (nonVarPositions r1.lhs).filterMap (overlapAt r1 r2)

/-- The critical pairs of a term rewriting system: for every ordered pair of
rules `(r1, r2)` of `R`, with `r1` renamed into the left variable summand and
`r2` into the right summand (so they share no variables), the critical pairs of
overlapping `r2` into `r1`. The pairs live over the renamed carrier `RenVar nu`
and are genuine overlap peaks in `renameTRS R` (see `criticalPairs_sound`). The
ordered double `flatMap` enumerates every overlap, including a rule with a
renamed copy of itself; the list is never a stub. -/
def criticalPairs [DecidableEq sigma] [DecidableEq nu] (R : TRS sigma nu) :
    List (Term sigma (RenVar nu) × Term sigma (RenVar nu)) :=
  R.flatMap (fun r1 => R.flatMap (fun r2 =>
    overlapPairs (renameRule Sum.inl r1) (renameRule Sum.inr r2)))

/-! ## Soundness: every emitted critical pair is a real overlap peak -/

/-- A pair emitted by `overlapAt r1 r2 p` exposes the witnessing subterm and
unifier: there are `sub` and `μ` with `subtermAt r1.lhs p = some sub`,
`unify sub r2.lhs = some μ`, and the pair equal to
`(μ • r1.rhs, μ • replaceAt r1.lhs p r2.rhs)`. Peels the two `Option` layers of
`overlapAt` cleanly. -/
theorem overlapAt_eq_some [DecidableEq sigma] [DecidableEq nu]
    {r1 r2 : Rule sigma (RenVar nu)} {p : Pos}
    {s t : Term sigma (RenVar nu)} (h : overlapAt r1 r2 p = some (s, t)) :
    ∃ sub μ, Term.subtermAt r1.lhs p = some sub ∧ unify sub r2.lhs = some μ ∧
      s = μ • r1.rhs ∧ t = μ • Term.replaceAt r1.lhs p r2.rhs := by
  rw [overlapAt, Option.bind_eq_some_iff] at h
  obtain ⟨sub, hsub, hmap⟩ := h
  rw [Option.map_eq_some_iff] at hmap
  obtain ⟨μ, hμ, hpair⟩ := hmap
  rw [Prod.mk.injEq] at hpair
  exact ⟨sub, μ, hsub, hμ, hpair.1.symm, hpair.2.symm⟩

/-- Soundness of `overlapAt`: a pair emitted at position `p` is an overlap peak of
the two rules. With `w = μ • r1.lhs` the unified redex, `w` rewrites by `r1` at
the root to `s` and by `r2` at the overlap position `p` to `t`, so `s` and `t`
genuinely diverge from the single peak `w`. -/
theorem overlapAt_sound [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) {r1 r2 : Rule sigma (RenVar nu)}
    (h1 : r1 ∈ renameTRS R) (h2 : r2 ∈ renameTRS R) {p : Pos}
    {s t : Term sigma (RenVar nu)} (hst : overlapAt r1 r2 p = some (s, t)) :
    ∃ w, Step (renameTRS R) w s ∧ Step (renameTRS R) w t := by
  obtain ⟨sub, μ, hsub, hu, hs, ht⟩ := overlapAt_eq_some hst
  -- the shared peak is the unified redex `μ • r1.lhs`
  refine ⟨μ • r1.lhs, ?_, ?_⟩
  · -- rule 1 contracts at the root: `μ • r1.lhs → μ • r1.rhs = s`
    rw [hs]
    exact Step.rootStep_step (renameTRS R) h1 μ
  · -- rule 2 contracts at position `p`
    rw [ht]
    -- the redex at `p` in the peak is `μ • sub`
    have hsubμ : Term.subtermAt (μ • r1.lhs) p = some (μ • sub) :=
      subtermAt_apply μ r1.lhs p sub hsub
    -- `μ • sub = μ • r2.lhs` by `unify_sound`, so rule 2 fires there
    have hunif : μ • sub = μ • r2.lhs := unify_sound hu
    have hroot2 : Step (renameTRS R) (μ • sub) (μ • r2.rhs) := by
      rw [hunif]
      exact Step.rootStep_step (renameTRS R) h2 μ
    -- lift the contraction to the whole peak at position `p`
    have hstep : Step (renameTRS R) (μ • r1.lhs)
        (Term.replaceAt (μ • r1.lhs) p (μ • r2.rhs)) :=
      Step.at_pos (renameTRS R) (μ • r1.lhs) p (μ • sub) (μ • r2.rhs) hsubμ hroot2
    -- and `replaceAt (μ•r1.lhs) p (μ•r2.rhs) = μ • replaceAt r1.lhs p r2.rhs`
    rwa [replaceAt_apply μ r2.rhs r1.lhs p sub hsub] at hstep

/-- Soundness of `overlapPairs`: every emitted pair `(s, t)` is an overlap peak of
the two rules — some term `w` rewrites by `Step` to both `s` and `t` in
`renameTRS R`. -/
theorem overlapPairs_sound [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) {r1 r2 : Rule sigma (RenVar nu)}
    (h1 : r1 ∈ renameTRS R) (h2 : r2 ∈ renameTRS R)
    {s t : Term sigma (RenVar nu)} (hst : (s, t) ∈ overlapPairs r1 r2) :
    ∃ w, Step (renameTRS R) w s ∧ Step (renameTRS R) w t := by
  rw [overlapPairs, List.mem_filterMap] at hst
  obtain ⟨p, _hp, hmatch⟩ := hst
  exact overlapAt_sound R h1 h2 hmatch

/-- Every emitted critical pair is a genuine overlap peak: there is a term `w`
that rewrites by `Step` to both components of the pair, in the renamed system
`renameTRS R`. The peak is the unified redex `μ • r1.lhs`, which rule 1
contracts at the root to `s` and rule 2 contracts at the overlap position `p` to
`t`. This is a real two-way divergence, the defining property of a critical
pair. -/
theorem criticalPairs_sound [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) {s t : Term sigma (RenVar nu)}
    (hst : (s, t) ∈ criticalPairs R) :
    ∃ w, Step (renameTRS R) w s ∧ Step (renameTRS R) w t := by
  rw [criticalPairs, List.mem_flatMap] at hst
  obtain ⟨r1, hr1, hst⟩ := hst
  rw [List.mem_flatMap] at hst
  obtain ⟨r2, hr2, hst⟩ := hst
  exact overlapPairs_sound R (renameRule_inl_mem hr1) (renameRule_inr_mem hr2) hst

/-! ## Non-vacuity: a concrete two-rule system with a real critical pair

The construction enumerates overlaps genuinely; this section exhibits one. The
system has two rules over `Nat`-symbols and `Nat`-variables:

* rule A: `f(g(x), y) -> h(x, y)`
* rule B: `g(z) -> k(z)`

Rule B's left-hand side `g(z)` overlaps rule A's left-hand side at position
`[0]` (the first argument of `f`, namely `g(x)`). Unifying `g(x)` with `g(z')`
(renamed apart) binds the variables, and the resulting critical pair is a real
peak: the redex `f(g(?), y)` rewrites to `h(?, y)` by rule A at the root and to
`f(k(?), y)` by rule B at position `[0]`. -/

namespace Demo

/-- Rule A `f(g(x), y) -> h(x, y)`: symbols `f = 0`, `g = 1`, `h = 3`; variables
`x = 0`, `y = 1`. The left-hand side is an application. -/
def ruleA : Rule Nat Nat where
  lhs := .app 0 [.app 1 [.var 0], .var 1]
  rhs := .app 3 [.var 0, .var 1]
  lhs_isApp := rfl

/-- Rule B `g(z) -> k(z)`: symbols `g = 1`, `k = 4`; variable `z = 0`. The
left-hand side is an application. -/
def ruleB : Rule Nat Nat where
  lhs := .app 1 [.var 0]
  rhs := .app 4 [.var 0]
  lhs_isApp := rfl

/-- The two-rule demonstration system `[ruleA, ruleB]`. -/
def demoTRS : TRS Nat Nat := [ruleA, ruleB]

/-- Rule A renamed into the left variable summand of the shared carrier
`RenVar Nat`. The explicit codomain pins both summands of the `Sum`. -/
def ruleA_inl : Rule Nat (RenVar Nat) := renameRule (Sum.inl : Nat → RenVar Nat) ruleA

/-- Rule B renamed into the right variable summand of the shared carrier
`RenVar Nat`. -/
def ruleB_inr : Rule Nat (RenVar Nat) := renameRule (Sum.inr : Nat → RenVar Nat) ruleB

/-- Rule B renamed into the right summand overlaps rule A renamed into the left
summand at position `[0]`: the subterm of `ruleA_inl.lhs` at `[0]` is
`g(inl 0)`, which unifies with `ruleB_inr.lhs = g(inr 0)`. So this overlap emits
a critical pair, and the reduction confirms the enumeration is nonempty rather
than a stub. -/
theorem overlapAt_AB_zero_isSome :
    (overlapAt ruleA_inl ruleB_inr [0]).isSome = true := by
  simp [overlapAt, ruleA_inl, ruleB_inr, ruleA, ruleB, renameRule, Term.rename,
    Term.renameList, Term.subtermAt, Term.subtermAt_app_cons, unify, solve,
    zipPairs, wlSubst1]

/-- The position `[0]` is a non-variable position of rule A's renamed left-hand
side, so the overlap above is actually enumerated by `overlapPairs`. -/
theorem zero_mem_nonVarPositions_A :
    ([0] : Pos) ∈ nonVarPositions ruleA_inl.lhs := by
  simp [ruleA_inl, ruleA, renameRule, Term.rename, Term.renameList,
    nonVarPositions, nonVarPositionsList]

/-- The A-versus-B overlap pair lands in `overlapPairs ruleA_inl ruleB_inr`: it is
emitted at the non-variable position `[0]`. -/
theorem AB_pair_mem_overlapPairs :
    ∃ pair, pair ∈ overlapPairs ruleA_inl ruleB_inr := by
  obtain ⟨pair, hpair⟩ := Option.isSome_iff_exists.1 overlapAt_AB_zero_isSome
  exact ⟨pair, List.mem_filterMap.2 ⟨[0], zero_mem_nonVarPositions_A, hpair⟩⟩

/-- Membership of an `overlapPairs ruleA_inl ruleB_inr` pair in `criticalPairs
demoTRS`: it is reached by the ordered double `flatMap` at `(ruleA, ruleB)`. -/
theorem mem_criticalPairs_of_AB {pair : Term Nat (RenVar Nat) × Term Nat (RenVar Nat)}
    (hpair : pair ∈ overlapPairs ruleA_inl ruleB_inr) :
    pair ∈ criticalPairs demoTRS := by
  rw [criticalPairs, List.mem_flatMap]
  refine ⟨ruleA, by simp [demoTRS], ?_⟩
  rw [List.mem_flatMap]
  exact ⟨ruleB, by simp [demoTRS], hpair⟩

/-- `criticalPairs demoTRS` is non-empty: the A-versus-B overlap at `[0]` lands a
pair in the enumeration, so the construction returns a real list, never `[]`. -/
theorem criticalPairs_demoTRS_nonempty :
    (criticalPairs demoTRS) ≠ [] := by
  intro hcontra
  obtain ⟨pair, hpair⟩ := AB_pair_mem_overlapPairs
  have hmem : pair ∈ criticalPairs demoTRS := mem_criticalPairs_of_AB hpair
  rw [hcontra] at hmem
  exact List.not_mem_nil hmem

/-- The witnessed critical pair of the demonstration system is a real overlap
peak: there is a term `w` that rewrites in `renameTRS demoTRS` by one `Step` to
each component. This instantiates `criticalPairs_sound` on a concrete pair, so
the non-vacuity is a genuine two-way divergence, not a trivial emission. -/
theorem demo_criticalPair_is_peak :
    ∃ s t : Term Nat (RenVar Nat), (s, t) ∈ criticalPairs demoTRS ∧
      ∃ w, Step (renameTRS demoTRS) w s ∧ Step (renameTRS demoTRS) w t := by
  obtain ⟨pair, hpair⟩ := AB_pair_mem_overlapPairs
  have hmem : pair ∈ criticalPairs demoTRS := mem_criticalPairs_of_AB hpair
  obtain ⟨w, hws, hwt⟩ := criticalPairs_sound demoTRS (s := pair.1) (t := pair.2)
    (by simpa using hmem)
  exact ⟨pair.1, pair.2, by simpa using hmem, w, hws, hwt⟩

end Demo

end OperatorKO7.Meta.Rewriting

/-! ## Verification: headline types and axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @nonVarPositions
open OperatorKO7.Meta.Rewriting in
#check @renameRule
open OperatorKO7.Meta.Rewriting in
#check @renameRule_vars_disjoint
open OperatorKO7.Meta.Rewriting in
#check @nonVarPositions_sound
open OperatorKO7.Meta.Rewriting in
#check @criticalPairs
open OperatorKO7.Meta.Rewriting in
#check @overlapPairs
open OperatorKO7.Meta.Rewriting in
#check @criticalPairs_sound
open OperatorKO7.Meta.Rewriting in
#check @Demo.demo_criticalPair_is_peak

#print axioms OperatorKO7.Meta.Rewriting.criticalPairs
#print axioms OperatorKO7.Meta.Rewriting.criticalPairs_sound
#print axioms OperatorKO7.Meta.Rewriting.nonVarPositions_sound
#print axioms OperatorKO7.Meta.Rewriting.renameRule_vars_disjoint
#print axioms OperatorKO7.Meta.Rewriting.Demo.criticalPairs_demoTRS_nonempty
#print axioms OperatorKO7.Meta.Rewriting.Demo.demo_criticalPair_is_peak
