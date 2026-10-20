import OperatorKO7.Meta.Rewriting.CriticalPair
import Mathlib.Order.WellFounded

/-!
# The Critical Pair Lemma: support, the forward direction, the always-join cases, and Newman

Roadmap source: `ROADMAP-01-generic-critical-pair-lemma.md`, sections 3 (the
three redex-overlap cases), 4, 5, and the dispatch wave 4. This module assembles
the classical Knuth-Bendix/Huet critical-pair material on top of the verified
rewriting foundation (`Term`, `Position`, `Subst`, `Unify`, `UnifyCorrect`,
`Rewrite`, `CriticalPair`).

## What this module delivers

Support algebra (priority 1):

- `step_subst` : a one-step rewrite is preserved by substitution,
  `Step R s t → Step R (σ • s) (σ • t)`, since `rootStep` is closed under further
  substitution through `apply_comp`. This is the engine of the variable-overlap
  case: an inner step replays at every occurrence of a duplicated variable.
- `stepStar_subst`, `joinable_subst` : the closure and joinability inherit the
  same substitution stability.
- `joinable_at_pos` : joinability of two subterms at a common valid position lifts
  to joinability of the whole terms, the positional context closure of `joinable`.

Forward direction (priority 2):

- `localConfluent_imp_cp_joinable` : if `renameTRS R` is locally confluent then
  every critical pair of `R` is joinable in `renameTRS R`. Each critical pair is a
  genuine peak by `criticalPairs_sound`, and local confluence joins every peak.

The always-join overlap cases (priority 3), each a substantive peak-joining lemma:

- `joinable_of_parallel_peak` : a peak whose two contractions sit at parallel
  positions is joinable; the contractions commute by `replaceAt_parallel_comm`,
  and the common reduct performs both. This is the disjoint case, which always
  closes.
- `joinable_of_variable_overlap` : a peak where one step happens inside a
  substitution instance (an inner step on the term filling a variable position)
  is joinable; the inner step is replayed under the surrounding root contraction
  through `step_subst`. This is the variable-overlap case, which always closes,
  and it accounts for non-left-linear rules because the replay holds at every
  occurrence of the substituted variable.

Generic Newman (priority 5):

- `confluent_of_wf_of_localConfluent` : an abstract relation that is strongly
  normalizing (its reverse is well-founded) and locally confluent is confluent.
  The proof is the standard `Acc`-recursion diamond, written over an arbitrary
  relation so it is reusable.
- `stepStar_confluent_of_SN_of_localConfluent` : its specialization to the
  rewrite relation, joining `localConfluent` and a supplied strong-normalization
  hypothesis into confluence of `StepStar`.

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

/-! ## Priority 1: substitution stability of the rewrite relation

`rootStep` is closed under further substitution: a root contraction
`s = τ • lhs → τ • rhs = t` becomes `σ • s = (comp σ τ) • lhs → (comp σ τ) • rhs = σ • t`
by `apply_comp`. The context closure inherits this through the `arg` constructor,
giving the substitution stability of `Step`, its closure, and joinability. -/

/-- A root contraction is preserved by substitution: applying `σ` to both sides of
a `rootStep` is again a `rootStep`, with the matching substitution composed with
`σ`. The algebraic core is `apply_comp`: `σ • (τ • l) = (comp σ τ) • l`. -/
theorem rootStep_subst (R : TRS sigma nu) (σ : Subst sigma nu) {s t : Term sigma nu}
    (h : rootStep R s t) : rootStep R (σ • s) (σ • t) := by
  obtain ⟨rule, hrule, τ, hs, ht⟩ := h
  refine ⟨rule, hrule, σ.comp τ, ?_, ?_⟩
  · rw [hs, apply_comp]
  · rw [ht, apply_comp]

/-- A one-step rewrite is preserved by substitution: if `s` rewrites to `t` then
`σ • s` rewrites to `σ • t`. The `root` case is `rootStep_subst`; the `arg` case
pushes the substitution through the application via `applyList_eq_map`, exposing
the same one-position context on the substituted arguments. This is the engine of
the variable-overlap join: an inner rewrite replays under any surrounding
substitution, at every occurrence of the variable it acts under. -/
theorem step_subst (R : TRS sigma nu) (σ : Subst sigma nu) :
    ∀ {s t : Term sigma nu}, Step R s t → Step R (σ • s) (σ • t) := by
  intro s t h
  induction h with
  | @root s t hroot => exact Step.root (rootStep_subst R σ hroot)
  | @arg f pre post a b _hstep ih =>
      -- push `σ` through the application: the rewriting argument stays in place
      rw [apply_app, apply_app, applyList_eq_map, applyList_eq_map,
        List.map_append, List.map_append, List.map_cons]
      exact Step.arg f (pre.map (apply σ)) (post.map (apply σ)) ih

/-- The reflexive-transitive closure is preserved by substitution: a rewrite
sequence `s ↠ t` lifts to `σ • s ↠ σ • t`. By `ReflTransGen.lift` along
`apply σ`, each step transported by `step_subst`. -/
theorem stepStar_subst (R : TRS sigma nu) (σ : Subst sigma nu) {s t : Term sigma nu}
    (h : StepStar R s t) : StepStar R (σ • s) (σ • t) :=
  Relation.ReflTransGen.lift (apply σ) (fun _ _ hstep => step_subst R σ hstep) h

/-- Joinability is preserved by substitution: if `s` and `t` are joinable then so
are `σ • s` and `σ • t`. The common reduct is the substituted common reduct. This
is exactly the closure under substitution that the critical-overlap case needs:
once a critical pair is joinable, every substitution instance of it is joinable. -/
theorem joinable_subst (R : TRS sigma nu) (σ : Subst sigma nu) {s t : Term sigma nu}
    (h : joinable R s t) : joinable R (σ • s) (σ • t) :=
  let ⟨u, hsu, htu⟩ := h
  ⟨σ • u, stepStar_subst R σ hsu, stepStar_subst R σ htu⟩

/-! ## Priority 1, continued: position inversion of a single step

The exact converse of `Step.at_pos`: every one-step rewrite is a root contraction
performed at some position. This exposes the redex position and rule instance of an
arbitrary step, the entry point for any position-based peak analysis. -/

/-- Replacing in `pre ++ c :: post` at the index `pre.length` (the slot holding
`c`) recursively replaces `c` and leaves the prefix and suffix intact. By induction
on the prefix `pre`. -/
theorem Term.replaceAtList_append_length (pre post : List (Term sigma nu))
    (c : Term sigma nu) (p : Pos) (b : Term sigma nu) :
    Term.replaceAtList (pre ++ c :: post) pre.length p b
      = pre ++ Term.replaceAt c p b :: post := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      simp only [List.cons_append, List.length_cons, Term.replaceAtList_cons_succ, ih]

/-- Position inversion of `Step`: every one-step rewrite `Step R s t` is a root
contraction at some position `p`. There are a position `p`, a redex `a`, and a
contractum `b` with `subtermAt s p = some a`, `rootStep R a b`, and
`t = replaceAt s p b`. The `root` constructor gives the root position `[]`; the
`arg` constructor prepends its argument index to the inner position. -/
theorem Step.exists_pos_rootStep (R : TRS sigma nu) {s t : Term sigma nu}
    (h : Step R s t) :
    ∃ (p : Pos) (a b : Term sigma nu),
      Term.subtermAt s p = some a ∧ rootStep R a b ∧ t = Term.replaceAt s p b := by
  induction h with
  | @root s t hroot =>
      exact ⟨[], s, t, by simp, hroot, by simp⟩
  | @arg f pre post c d _hstep ih =>
      obtain ⟨p, a, b, hsub, hroot, ht⟩ := ih
      refine ⟨pre.length :: p, a, b, ?_, hroot, ?_⟩
      · -- reading at index `pre.length` lands on `c`, then descends along `p`
        rw [Term.subtermAt_app_cons]
        have hidx : (pre ++ c :: post)[pre.length]? = some c := by
          rw [List.getElem?_append_right (by omega)]; simp
        rw [hidx]; exact hsub
      · -- replacing at `pre.length :: p` rebuilds the application with `c` updated
        rw [ht, Term.replaceAt_app_cons, Term.replaceAtList_append_length]

/-! ## Priority 1, continued: positional context closure of joinability

`StepStar.arg_congr` lifts a rewrite sequence through one argument position; the
positional form below lifts it through an arbitrary valid position by iterating
the `arg` congruence down the position path (the closure analogue of
`Step.at_pos`). Joinability then climbs out of any subterm.

Three structural position facts power this and are proved here directly over the
`Term.rec'` eliminator: reading a position back means a replacement there with the
same subterm is a no-op (`replaceAt_eq_self_of_subtermAt`), a readable position is
valid (`validPos_of_subtermAt`), and two replacements at one position collapse to
the last (`replaceAt_replaceAt_same`). -/

/-- A readable position is valid: if `subtermAt u p` returns a subterm then `p` is
a `ValidPos` of `u`. Immediate from the definition of `ValidPos`. -/
theorem Term.validPos_of_subtermAt {u : Term sigma nu} {p : Pos} {a : Term sigma nu}
    (h : Term.subtermAt u p = some a) : Term.ValidPos u p := by
  rw [Term.ValidPos, h]; rfl

/-- Replacing the subterm at a position with the subterm already there is a no-op:
if `subtermAt u p = some a` then `replaceAt u p a = u`. By induction on `u` and
the position path. -/
theorem Term.replaceAt_eq_self_of_subtermAt :
    ∀ (u : Term sigma nu) (p : Pos) (a : Term sigma nu),
      Term.subtermAt u p = some a → Term.replaceAt u p a = u := by
  intro u
  induction u using Term.rec' with
  | hvar x =>
      intro p a hsub
      cases p with
      | nil =>
          simp only [Term.subtermAt_nil, Option.some.injEq] at hsub
          rw [hsub, Term.replaceAt_nil]
      | cons i p => simp only [Term.subtermAt_var_cons, reduceCtorEq] at hsub
  | happ f args ih =>
      intro p a hsub
      cases p with
      | nil =>
          simp only [Term.subtermAt_nil, Option.some.injEq] at hsub
          rw [hsub, Term.replaceAt_nil]
      | cons i p =>
          rw [Term.subtermAt_app_cons] at hsub
          cases hgi : args[i]? with
          | none => rw [hgi] at hsub; simp at hsub
          | some c =>
              rw [hgi] at hsub
              have hmem : c ∈ args := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, hc⟩ := hgi; exact hc ▸ List.getElem_mem _
              have hinner : Term.replaceAt c p a = c := ih c hmem p a hsub
              have hi : i < args.length := by
                rw [List.getElem?_eq_some_iff] at hgi; exact hgi.1
              rw [Term.replaceAt_app_cons]
              -- the list-replacement at index `i` rebuilds `args`
              have hsplit : Term.replaceAtList args i p a = args := by
                have hself := Term.getElem?_replaceAtList_self args i p a hi
                have hci : args[i] = c := by
                  rw [List.getElem?_eq_some_iff] at hgi
                  obtain ⟨_, hc⟩ := hgi; exact hc
                -- compare element-by-element with `args`
                apply List.ext_getElem
                · rw [Term.length_replaceAtList]
                · intro n h1 h2
                  by_cases hn : n = i
                  · subst hn
                    have := Term.getElem?_replaceAtList_self args n p a h2
                    rw [List.getElem?_eq_getElem h1] at this
                    rw [Option.some.injEq] at this
                    rw [this, hci, hinner]
                  · have := Term.getElem?_replaceAtList_ne args i n p a (fun h => hn h.symm)
                    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
                    rw [Option.some.injEq] at this
                    exact this
              rw [hsplit]

/-- Replacing twice at the same position collapses to the last replacement:
`replaceAt (replaceAt u p a) p b = replaceAt u p b`, for any position. By
induction on `u` and the position path; off-path the term is unchanged by both. -/
theorem Term.replaceAt_replaceAt_same :
    ∀ (u : Term sigma nu) (p : Pos) (a b : Term sigma nu),
      Term.replaceAt (Term.replaceAt u p a) p b = Term.replaceAt u p b := by
  intro u
  induction u using Term.rec' with
  | hvar x =>
      intro p a b
      cases p with
      | nil => simp
      | cons i p => simp
  | happ f args ih =>
      intro p a b
      cases p with
      | nil => simp
      | cons i p =>
          rw [Term.replaceAt_app_cons, Term.replaceAt_app_cons, Term.replaceAt_app_cons]
          congr 1
          -- list level: replacing twice at index `i`, tail `p`, collapses
          clear f
          induction args generalizing i with
          | nil => simp
          | cons c cs ihl =>
              cases i with
              | zero =>
                  simp only [Term.replaceAtList_cons_zero]
                  rw [ih c (by simp) p a b]
              | succ i =>
                  simp only [Term.replaceAtList_cons_succ]
                  rw [ihl (fun d hd => ih d (by simp [hd])) i]

/-- A rewrite sequence on the subterm at a valid position lifts to a rewrite
sequence on the whole term: if the subterm of `u` at `p` is `a` and `a ↠ b`, then
`u ↠ replaceAt u p b`. Each step is lifted by `Step.at_pos`, then chained, by
induction on the closure. -/
theorem StepStar.at_pos (R : TRS sigma nu) (u : Term sigma nu) (p : Pos)
    {a b : Term sigma nu} (hsub : Term.subtermAt u p = some a) (h : StepStar R a b) :
    StepStar R u (Term.replaceAt u p b) := by
  induction h with
  | refl =>
      -- zero steps: `replaceAt u p a = u` because reading at `p` returned `a`
      rw [Term.replaceAt_eq_self_of_subtermAt u p a hsub]
      exact StepStar.refl R u
  | @tail c d _hac hcd ih =>
      -- `u ↠ replaceAt u p c` (ih) then one step `replaceAt u p c → replaceAt u p d`
      refine ih.tail ?_
      have hsubc : Term.subtermAt (Term.replaceAt u p c) p = some c :=
        Term.subtermAt_replaceAt_same u p c (Term.validPos_of_subtermAt hsub)
      have hstep := Step.at_pos R (Term.replaceAt u p c) p c d hsubc hcd
      rwa [Term.replaceAt_replaceAt_same u p c d] at hstep

/-- Joinability lifts through an arbitrary valid position: if the subterms of `u`
and `v` at the same valid position `p` are joinable and `u`, `v` agree off `p`
(both obtained from a shared frame by `replaceAt` at `p`), then the framed terms
are joinable. Stated in the form used downstream: two replacements at `p` of a
common frame `w` are joinable whenever the inserted terms are. -/
theorem joinable_at_pos (R : TRS sigma nu) (w : Term sigma nu) (p : Pos)
    (hvalid : Term.ValidPos w p) {a b : Term sigma nu} (h : joinable R a b) :
    joinable R (Term.replaceAt w p a) (Term.replaceAt w p b) := by
  obtain ⟨c, hac, hbc⟩ := h
  refine ⟨Term.replaceAt w p c, ?_, ?_⟩
  · have hsa : Term.subtermAt (Term.replaceAt w p a) p = some a :=
      Term.subtermAt_replaceAt_same w p a hvalid
    have := StepStar.at_pos R (Term.replaceAt w p a) p hsa hac
    rwa [Term.replaceAt_replaceAt_same w p a c] at this
  · have hsb : Term.subtermAt (Term.replaceAt w p b) p = some b :=
      Term.subtermAt_replaceAt_same w p b hvalid
    have := StepStar.at_pos R (Term.replaceAt w p b) p hsb hbc
    rwa [Term.replaceAt_replaceAt_same w p b c] at this

/-! ## Priority 3a: the disjoint (parallel) overlap case

A peak whose two contractions sit at parallel positions joins. The contractions
commute (`replaceAt_parallel_comm`), and reading a position is undisturbed by a
replacement at a parallel position (`subtermAt_replaceAt_parallel`, proved here),
so each side can still perform the other contraction, meeting at the doubly
replaced term. This case always closes, with no critical-pair hypothesis. -/

/-- A replacement at one position does not change the subterm read at a parallel
position: `p ∥ q → subtermAt (replaceAt w p s) q = subtermAt w q`. By induction on
`w` and the parallel-position structure, mirroring `replaceAt_parallel_comm`. -/
theorem Term.subtermAt_replaceAt_parallel :
    ∀ (w : Term sigma nu) (p q : Pos) (s : Term sigma nu), Pos.parallel p q →
      Term.subtermAt (Term.replaceAt w p s) q = Term.subtermAt w q := by
  intro w
  induction w using Term.rec' with
  | hvar x =>
      intro p q s hpq
      obtain ⟨i, j, p', q', hp, hq, _⟩ := parallel_cons_cases hpq
      subst hp; subst hq; simp
  | happ f args ih =>
      intro p q s hpq
      obtain ⟨i, j, p', q', hp, hq, hcase⟩ := parallel_cons_cases hpq
      subst hp; subst hq
      rw [Term.replaceAt_app_cons, Term.subtermAt_app_cons, Term.subtermAt_app_cons]
      rcases hcase with hij | ⟨hij, hpar⟩
      · -- distinct argument indices: the read index `j` is untouched by replacing at `i`
        rw [Term.getElem?_replaceAtList_ne args i j p' s hij]
      · -- same index, parallel tails: descend and use the inner-argument hypothesis
        subst hij
        by_cases hi : i < args.length
        · -- in range: both reads return the (recursively replaced) element
          have hself := Term.getElem?_replaceAtList_self args i p' s hi
          have hget : args[i]? = some args[i] := List.getElem?_eq_getElem hi
          rw [hself, hget]
          have hmem : args[i] ∈ args := List.getElem_mem hi
          exact ih args[i] hmem p' q' s hpar
        · -- out of range: both reads are `none`
          have hnone : args[i]? = none := List.getElem?_eq_none (by omega)
          have hnone' : (Term.replaceAtList args i p' s)[i]? = none :=
            List.getElem?_eq_none (by rw [Term.length_replaceAtList]; omega)
          rw [hnone, hnone']

/-- The disjoint overlap case: a peak whose two contractions happen at parallel
positions is joinable. Given a frame `w` with a redex at `p` stepping to `b₁` and a
redex at `q` stepping to `b₂`, where `p ∥ q`, the two results `replaceAt w p b₁`
and `replaceAt w q b₂` join at the doubly replaced term. Each side performs the
contraction the other already did: the relevant subterm survives at its parallel
position, and `replaceAt_parallel_comm` identifies the two meeting points. -/
theorem joinable_of_parallel_peak (R : TRS sigma nu) (w : Term sigma nu) (p q : Pos)
    {a₁ b₁ a₂ b₂ : Term sigma nu}
    (hp : Term.subtermAt w p = some a₁) (hq : Term.subtermAt w q = some a₂)
    (hpar : Term.Pos.parallel p q) (hstep₁ : Step R a₁ b₁) (hstep₂ : Step R a₂ b₂) :
    joinable R (Term.replaceAt w p b₁) (Term.replaceAt w q b₂) := by
  refine ⟨Term.replaceAt (Term.replaceAt w p b₁) q b₂, ?_, ?_⟩
  · -- left side already at the common reduct, in one step at `q`
    have hsubq : Term.subtermAt (Term.replaceAt w p b₁) q = some a₂ := by
      rw [Term.subtermAt_replaceAt_parallel w p q b₁ hpar]; exact hq
    exact StepStar.single (Step.at_pos R (Term.replaceAt w p b₁) q a₂ b₂ hsubq hstep₂)
  · -- right side: contract at `p` (subterm survives), then commute to the common reduct
    have hsubp : Term.subtermAt (Term.replaceAt w q b₂) p = some a₁ := by
      rw [Term.subtermAt_replaceAt_parallel w q p b₂ (Term.Pos.parallel_comm hpar)]; exact hp
    have hstep := Step.at_pos R (Term.replaceAt w q b₂) p a₁ b₁ hsubp hstep₁
    have hcomm : Term.replaceAt (Term.replaceAt w q b₂) p b₁
        = Term.replaceAt (Term.replaceAt w p b₁) q b₂ :=
      Term.replaceAt_parallel_comm w q p b₂ b₁ (Term.Pos.parallel_comm hpar)
    rw [hcomm] at hstep
    exact StepStar.single hstep

/-! ## Priority 3b: the variable-overlap case

A peak where one redex sits inside a substitution instance, strictly below a
variable position of the other redex, is joinable. The mechanism is the
multi-occurrence replay `stepStar_of_pointwise_stepStar`: when two substitutions
are connected variable-by-variable by reduction sequences, every term reduces from
the first instance to the second, replaying the inner reduction at every occurrence
of every variable. Non-left-linear rules are covered: a variable occurring several
times has the inner reduction replayed at each occurrence. -/

/-- Pointwise reduction lifts through an argument list within a fixed head: if every
argument reduces from its `g`-image to its `h`-image, then the application reduces
argument-wise. The accumulator `done` carries the already-rewritten prefix; each
step rewrites one further argument through its one-position context via
`StepStar.arg_congr`. -/
theorem stepStar_app_argwise (R : TRS sigma nu) (f : sigma)
    (g h : Term sigma nu → Term sigma nu) :
    ∀ (rest : List (Term sigma nu)), (∀ a ∈ rest, StepStar R (g a) (h a)) →
      ∀ done : List (Term sigma nu),
        StepStar R (Term.app f (done ++ rest.map g)) (Term.app f (done ++ rest.map h)) := by
  intro rest
  induction rest with
  | nil => intro _ done; simpa using StepStar.refl R _
  | cons a rest ih =>
      intro hrest done
      -- rewrite the head argument `g a ↠ h a` in place at index `done.length`
      have hhead : StepStar R
          (Term.app f (done ++ (g a) :: rest.map g))
          (Term.app f (done ++ (h a) :: rest.map g)) :=
        StepStar.arg_congr R f done (rest.map g) (hrest a (by simp))
      -- recurse on the tail with the head appended to the done-prefix
      have htail : StepStar R
          (Term.app f ((done ++ [h a]) ++ rest.map g))
          (Term.app f ((done ++ [h a]) ++ rest.map h)) :=
        ih (fun b hb => hrest b (by simp [hb])) (done ++ [h a])
      -- reassociate the lists so the two sequences compose
      have he1 : done ++ (g a) :: rest.map g = done ++ List.map g (a :: rest) := by simp
      have he2 : done ++ (h a) :: rest.map g = (done ++ [h a]) ++ rest.map g := by simp
      have he3 : (done ++ [h a]) ++ rest.map h = done ++ List.map h (a :: rest) := by simp
      rw [he1] at hhead
      rw [he2] at hhead
      rw [he3] at htail
      exact hhead.trans htail

/-- Multi-occurrence replay: if two substitutions `σ` and `τ` are connected
variable-by-variable by reduction sequences (`∀ z, σ z ↠ τ z`), then every term
reduces from its `σ`-instance to its `τ`-instance, `σ • u ↠ τ • u`. By induction on
`u`: a variable is the hypothesis at that variable; an application replays each
argument through `stepStar_app_argwise`. This is the engine of the variable-overlap
join, and it accounts for non-left-linearity because the reduction is replayed at
every occurrence of every variable. -/
theorem stepStar_of_pointwise_stepStar (R : TRS sigma nu) {σ τ : Subst sigma nu}
    (hpt : ∀ z, StepStar R (σ z) (τ z)) :
    ∀ (u : Term sigma nu), StepStar R (σ • u) (τ • u) := by
  intro u
  induction u using Term.rec' with
  | hvar x => simpa using hpt x
  | happ f args ih =>
      rw [apply_app, apply_app, applyList_eq_map, applyList_eq_map]
      have := stepStar_app_argwise R f (apply σ) (apply τ) args
        (fun a ha => ih a ha) []
      simpa using this

/-- The variable-overlap case: a peak `σ • rhs ← σ • lhs → τ • lhs` joins, where `τ`
arises from `σ` by reducing inside the terms filling its variables
(`∀ z, σ z ↠ τ z`). The two sides meet at `τ • rhs`: the left side `σ • rhs` replays
the inner reductions to `τ • rhs` through `stepStar_of_pointwise_stepStar`, and the
right side `τ • lhs` contracts at the root by the same rule to `τ • rhs`. This always
closes; the replay handles a variable that occurs any number of times in `rhs`,
which is exactly where non-left-linearity is delicate. -/
theorem joinable_of_variable_overlap (R : TRS sigma nu) {rule : Rule sigma nu}
    (hrule : rule ∈ R) {σ τ : Subst sigma nu} (hpt : ∀ z, StepStar R (σ z) (τ z)) :
    joinable R (σ • rule.rhs) (τ • rule.lhs) := by
  refine ⟨τ • rule.rhs, ?_, ?_⟩
  · -- left side: replay the inner reductions across `rhs`
    exact stepStar_of_pointwise_stepStar R hpt rule.rhs
  · -- right side: one root contraction of the rule under `τ`
    exact StepStar.single (Step.rootStep_step R hrule τ)

/-! ## Priority 2: the forward direction

Every critical pair of `R` is a genuine peak in the renamed system `renameTRS R`
(`criticalPairs_sound`). If `renameTRS R` is locally confluent, local confluence
joins that peak, so the critical pair is joinable. This is the easy half of the
Critical Pair Lemma, and it holds with no further hypotheses. -/

/-- Forward direction of the Critical Pair Lemma: if the renamed system
`renameTRS R` is locally confluent, then every critical pair of `R` is joinable in
`renameTRS R`. Each critical pair `(s, t)` is a peak `s ← w → t` by
`criticalPairs_sound`, and local confluence joins every peak. -/
theorem localConfluent_imp_cp_joinable [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (hlc : localConfluent (renameTRS R)) :
    ∀ p ∈ criticalPairs R, joinable (renameTRS R) p.1 p.2 := by
  intro p hp
  obtain ⟨w, hws, hwt⟩ := criticalPairs_sound R (s := p.1) (t := p.2) (by
    rw [Prod.mk.eta]; exact hp)
  exact hlc w p.1 p.2 hws hwt

/-! ## Priority 5: a generic Newman lemma and its rewriting specialization

Newman's lemma in the abstract: a relation that is strongly normalizing (its
reverse is well-founded, equivalently every element is accessible under the
reverse relation) and locally confluent is confluent. The proof is the standard
`Acc`-recursion diamond, written over an arbitrary relation `r` so it is reusable,
then specialized to the rewrite relation. -/

section Newman

variable {α : Type u} (r : α → α → Prop)

/-- Local confluence of an abstract relation: every one-step peak joins through the
reflexive-transitive closure. -/
def AbsLocalConfluent : Prop :=
  ∀ a b c, r a b → r a c → ∃ d, Relation.ReflTransGen r b d ∧ Relation.ReflTransGen r c d

/-- Confluence of an abstract relation: every pair of coinitial reduction sequences
joins. -/
def AbsConfluent : Prop :=
  ∀ a b c, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c →
    ∃ d, Relation.ReflTransGen r b d ∧ Relation.ReflTransGen r c d

/-- The `Acc`-recursion engine of Newman's lemma: at an element `a` accessible
under the reverse relation `fun x y => r y x`, any two reduction sequences out of
`a` join. The recursion descends along the first steps of both sequences and uses
local confluence at `a` to bridge. This is the generic form of the proven
`join_star_star_at` pattern. -/
theorem absJoin_of_acc (hlc : AbsLocalConfluent r) :
    ∀ a, Acc (fun x y => r y x) a →
      ∀ {b c}, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c →
        ∃ d, Relation.ReflTransGen r b d ∧ Relation.ReflTransGen r c d := by
  intro a ha
  induction ha with
  | intro a _hacc ih =>
    intro b c hab hac
    rcases Relation.ReflTransGen.cases_head hab with rfl | ⟨b1, hab1, hb1b⟩
    · exact ⟨c, hac, Relation.ReflTransGen.refl⟩
    · rcases Relation.ReflTransGen.cases_head hac with rfl | ⟨c1, hac1, hc1c⟩
      · exact ⟨b, Relation.ReflTransGen.refl, Relation.ReflTransGen.head hab1 hb1b⟩
      · -- local confluence at `a` gives a common `e` of `b1` and `c1`
        obtain ⟨e, hb1e, hc1e⟩ := hlc a b1 c1 hab1 hac1
        -- recurse at `b1`: join `b1 ↠ b` and `b1 ↠ e`
        obtain ⟨d1, hbd1, hed1⟩ := ih b1 hab1 hb1b hb1e
        -- recurse at `c1`: join `c1 ↠ e ↠ d1` and `c1 ↠ c`
        obtain ⟨d, hd1d, hcd⟩ := ih c1 hac1 (hc1e.trans hed1) hc1c
        exact ⟨d, hbd1.trans hd1d, hcd⟩

/-- Generic Newman's lemma: a strongly normalizing (reverse-well-founded) and
locally confluent relation is confluent. -/
theorem confluent_of_wf_of_localConfluent
    (hwf : WellFounded (fun x y => r y x)) (hlc : AbsLocalConfluent r) :
    AbsConfluent r := by
  intro a b c hab hac
  exact absJoin_of_acc r hlc a (hwf.apply a) hab hac

end Newman

/-- Newman's lemma for the rewrite relation: if the one-step relation `Step R` is
strongly normalizing (its reverse is well-founded) and `R` is locally confluent,
then `StepStar R` is confluent. This composes the local-confluence result with the
generic Newman engine; the strong-normalization hypothesis is supplied (for a
concrete system it is discharged by a termination measure, e.g. the Dershowitz-Manna
substrate). -/
theorem stepStar_confluent_of_SN_of_localConfluent {R : TRS sigma nu}
    (hSN : WellFounded (fun x y : Term sigma nu => Step R y x))
    (hlc : localConfluent R) :
    ∀ a b c, StepStar R a b → StepStar R a c →
      ∃ d, StepStar R b d ∧ StepStar R c d := by
  have hlc' : AbsLocalConfluent (Step R) := fun a b c hab hac => hlc a b c hab hac
  exact confluent_of_wf_of_localConfluent (Step R) hSN hlc'

end OperatorKO7.Meta.Rewriting

/-! ## Axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @rootStep_subst
open OperatorKO7.Meta.Rewriting in
#check @step_subst
open OperatorKO7.Meta.Rewriting in
#check @stepStar_subst
open OperatorKO7.Meta.Rewriting in
#check @joinable_subst
open OperatorKO7.Meta.Rewriting in
#check @Step.exists_pos_rootStep
open OperatorKO7.Meta.Rewriting in
#check @StepStar.at_pos
open OperatorKO7.Meta.Rewriting in
#check @joinable_at_pos
open OperatorKO7.Meta.Rewriting in
#check @localConfluent_imp_cp_joinable
open OperatorKO7.Meta.Rewriting in
#check @Term.subtermAt_replaceAt_parallel
open OperatorKO7.Meta.Rewriting in
#check @joinable_of_parallel_peak
open OperatorKO7.Meta.Rewriting in
#check @stepStar_of_pointwise_stepStar
open OperatorKO7.Meta.Rewriting in
#check @joinable_of_variable_overlap
open OperatorKO7.Meta.Rewriting in
#check @confluent_of_wf_of_localConfluent
open OperatorKO7.Meta.Rewriting in
#check @stepStar_confluent_of_SN_of_localConfluent

#print axioms OperatorKO7.Meta.Rewriting.step_subst
#print axioms OperatorKO7.Meta.Rewriting.Step.exists_pos_rootStep
#print axioms OperatorKO7.Meta.Rewriting.joinable_subst
#print axioms OperatorKO7.Meta.Rewriting.joinable_at_pos
#print axioms OperatorKO7.Meta.Rewriting.localConfluent_imp_cp_joinable
#print axioms OperatorKO7.Meta.Rewriting.joinable_of_parallel_peak
#print axioms OperatorKO7.Meta.Rewriting.stepStar_of_pointwise_stepStar
#print axioms OperatorKO7.Meta.Rewriting.joinable_of_variable_overlap
#print axioms OperatorKO7.Meta.Rewriting.confluent_of_wf_of_localConfluent
#print axioms OperatorKO7.Meta.Rewriting.stepStar_confluent_of_SN_of_localConfluent
