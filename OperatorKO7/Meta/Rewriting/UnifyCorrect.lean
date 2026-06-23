import OperatorKO7.Meta.Rewriting.Unify

/-!
# Correctness of first-order unification

Roadmap source: `ROADMAP-01-generic-critical-pair-lemma.md`, sections 3 (the
correctness statements), 5, and 8 (the most-generality blueprint and the
Ribeiro-Camarao / idempotent-MGU mechanizations). This is Wave 3A: the keystone
gate, establishing that the Martelli-Montanari engine `solve`/`unify` of
`Unify.lean` returns a genuine most-general unifier as data.

## What this module delivers

For the singleton problem `unify s t = solve [(s, t)]`:

- `unify_sound`: a returned substitution unifies the two terms,
  `sigma.apply s = sigma.apply t`.
- `unify_complete`: whenever some substitution unifies the two terms, `unify`
  succeeds (`isSome`).
- `unify_mostGeneral`: the returned substitution is most general, in the sense
  that every unifier `tau` factors through it: `∃ rho, ∀ x, tau x = (rho.comp sigma) x`.

## The worklist invariant (the load-bearing structure)

All three headline statements are the singleton specializations of a single
invariant about `solve` over a whole worklist `W : List (Term × Term)`. Writing
`Unifies g W := ∀ p ∈ W, g.apply p.1 = g.apply p.2`:

- `solve_unifies`     : `solve W = some μ → Unifies μ W`;
- `solve_isSome`      : `(∃ τ, Unifies τ W) → (solve W).isSome`;
- `solve_mostGeneral` : `solve W = some μ → ∀ τ, Unifies τ W →
                          ∃ ρ, ∀ x, τ x = (ρ.comp μ) x`.

Each is proved by the custom recursion principle `solve.induct`, which supplies
the induction hypothesis on exactly the smaller worklist each move recurses into,
matching the lexicographic measure that makes `solve` terminate. `solve`'s
five-way case split (empty, delete, two eliminate forms, decompose) plus its four
failure branches (occurs-check ×2, arity/head clash ×2) become the nine
`solve.induct` cases. The eliminate move is the crux, and it rests on the algebraic
identities `Unifies_wlSubst1`/`apply_comp` (relating a substituted worklist to the
composed substitution), `comp_subst1_eq_of_unifies` (a unifier of `x =?= t`
absorbs `subst1 x t`), and the occurs-check, exactly as in the idempotent-MGU
mechanizations.

Trust: kernel-only; baseline-only under `#print axioms` (a subset of
`{propext, Classical.choice, Quot.sound}`, from `Finset`/`DecidableEq` plumbing).
No `sorry`, `axiom`, `native_decide`, `partial`, or `unsafe`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

open Subst

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## The worklist unifier predicate -/

/-- A substitution `g` unifies a worklist `W` when it equalizes both components
of every pair. The whole development is phrased against this predicate; the
single-equation statements specialize it to a singleton worklist. -/
def Unifies (g : Subst sigma nu) (W : List (Term sigma nu × Term sigma nu)) : Prop :=
  ∀ p ∈ W, g.apply p.1 = g.apply p.2

@[simp] theorem Unifies_nil (g : Subst sigma nu) :
    Unifies g ([] : List (Term sigma nu × Term sigma nu)) := by
  intro p hp; simp at hp

@[simp] theorem Unifies_cons (g : Subst sigma nu) (p : Term sigma nu × Term sigma nu)
    (W : List (Term sigma nu × Term sigma nu)) :
    Unifies g (p :: W) ↔ g.apply p.1 = g.apply p.2 ∧ Unifies g W := by
  constructor
  · intro h
    exact ⟨h p (by simp), fun q hq => h q (by simp [hq])⟩
  · rintro ⟨hp, hW⟩ q hq
    rw [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hp
    · exact hW q hq

/-- A unifier of a singleton worklist `[(s, t)]` is exactly a unifier of the
equation `s =?= t`. The bridge from the worklist invariant to the headline
single-equation statements. -/
theorem Unifies_singleton (g : Subst sigma nu) (s t : Term sigma nu) :
    Unifies g [(s, t)] ↔ g.apply s = g.apply t := by
  rw [Unifies_cons]
  simp

theorem Unifies_append (g : Subst sigma nu)
    (W1 W2 : List (Term sigma nu × Term sigma nu)) :
    Unifies g (W1 ++ W2) ↔ Unifies g W1 ∧ Unifies g W2 := by
  induction W1 with
  | nil => simp
  | cons p W ih => simp only [List.cons_append, Unifies_cons, ih]; tauto

/-! ## Substitution algebra for the eliminate move

The eliminate move replaces a worklist `W` by `wlSubst1 x t W` and composes the
recursively returned substitution with `subst1 x t`. Two facts power its analysis:
a substitution unifies the pushed-through worklist exactly when its composite with
`subst1 x t` unifies the original worklist; and a unifier of the equation
`var x =?= t` already absorbs `subst1 x t`, so composing changes nothing. -/

/-- Composition through a worklist substitution: a substitution `g` unifies the
pushed-through worklist `wlSubst1 x t W` exactly when its composite
`g.comp (subst1 x t)` unifies the original worklist `W`. This is the worklist
form of `apply_comp`. -/
theorem Unifies_wlSubst1 [DecidableEq nu] (g : Subst sigma nu) (x : nu)
    (t : Term sigma nu) (W : List (Term sigma nu × Term sigma nu)) :
    Unifies g (wlSubst1 x t W) ↔ Unifies (g.comp (subst1 x t)) W := by
  constructor
  · intro h p hp
    have hmem : (apply (subst1 x t) p.1, apply (subst1 x t) p.2) ∈ wlSubst1 x t W := by
      simp only [wlSubst1, List.mem_map]; exact ⟨p, hp, rfl⟩
    have := h _ hmem
    simpa only [apply_comp] using this
  · intro h p hp
    simp only [wlSubst1, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := h q hq
    simpa only [apply_comp] using this

/-- A unifier of `var x =?= t` absorbs `subst1 x t`: if `g.apply (var x) = g.apply t`,
then composing `g` with the single-point substitution `subst1 x t` leaves `g`
pointwise unchanged. The classic identity behind the eliminate move's
most-generality. -/
theorem comp_subst1_eq_of_unifies [DecidableEq nu] (g : Subst sigma nu) (x : nu)
    (t : Term sigma nu) (h : g.apply (Term.var x) = g.apply t) (y : nu) :
    (g.comp (subst1 x t)) y = g y := by
  rw [comp_apply_var]
  by_cases hy : y = x
  · subst hy
    rw [subst1_same]
    rw [apply_var] at h
    exact h.symm
  · rw [subst1_of_ne t hy, apply_var]

/-- A single-point substitution fixes any term in which its variable is absent. -/
theorem apply_subst1_eq_self_of_not_mem [DecidableEq nu] (x : nu) (t u : Term sigma nu)
    (hx : x ∉ Term.vars u) : apply (subst1 x t) u = u := by
  induction u using Term.rec' with
  | hvar y =>
      rw [Term.vars_var, Finset.mem_singleton] at hx
      rw [apply_var, subst1_of_ne t (fun h => hx h.symm)]
  | happ f args ih =>
      rw [apply_app, applyList_eq_map]
      rw [Term.vars_app, Term.mem_varsList_iff] at hx
      congr 1
      have : args.map (apply (subst1 x t)) = args.map _root_.id := by
        apply List.map_congr_left
        intro a ha
        rw [_root_.id_eq]
        exact ih a ha (fun hmem => hx ⟨a, ha, hmem⟩)
      rw [this, List.map_id]

/-- The head equation of the eliminate move. With the occurs-check passing, the
composite substitution `s₀.comp (subst1 x t)` unifies the equation `var x =?= t`
that the move discharges: both sides reduce to `s₀.apply t`. -/
theorem comp_subst1_unifies_head [DecidableEq nu] (s₀ : Subst sigma nu) (x : nu)
    (t : Term sigma nu) (hx : occurs x t = false) :
    (s₀.comp (subst1 x t)).apply (Term.var x) = (s₀.comp (subst1 x t)).apply t := by
  have hxt : x ∉ Term.vars t := (not_occurs_iff_not_mem_vars x t).1 hx
  rw [apply_comp, apply_comp, apply_var, subst1_same,
    apply_subst1_eq_self_of_not_mem x t t hxt]

/-! ## Decompose-move algebra

A substitution unifies a decomposed argument worklist exactly when it unifies the
two applications they came from. -/

/-- Applying a substitution to matching-arity applications is equal exactly when
the substitution unifies the zipped argument worklist. The decompose move's
correctness, both directions. -/
theorem Unifies_zipPairs_iff (g : Subst sigma nu) (f : sigma)
    (as bs : List (Term sigma nu)) (hlen : as.length = bs.length) :
    Unifies g (zipPairs as bs) ↔ g.apply (Term.app f as) = g.apply (Term.app f bs) := by
  rw [apply_app, apply_app, applyList_eq_map, applyList_eq_map, Term.app.injEq]
  simp only [true_and]
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => simp [zipPairs]
      | cons b bs => simp at hlen
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          simp only [zipPairs, Unifies_cons, List.map_cons, List.cons.injEq]
          rw [ih bs (by simpa using hlen)]

/-! ## Substitution extensionality

`apply` and `Unifies` depend on a substitution only through its pointwise values,
so pointwise-equal substitutions are interchangeable. -/

/-- Pointwise-equal substitutions produce the same application. -/
theorem apply_congr_of_pointwise [DecidableEq nu] {g g' : Subst sigma nu}
    (h : ∀ z, g z = g' z) (t : Term sigma nu) : apply g t = apply g' t := by
  induction t using Term.rec' with
  | hvar x => rw [apply_var, apply_var]; exact h x
  | happ f args ih =>
      rw [apply_app, apply_app, applyList_eq_map, applyList_eq_map]
      congr 1
      exact List.map_congr_left ih

/-- Pointwise-equal substitutions unify the same worklists. -/
theorem Unifies_congr_of_pointwise [DecidableEq nu] {g g' : Subst sigma nu}
    (h : ∀ z, g z = g' z) (W : List (Term sigma nu × Term sigma nu)) :
    Unifies g W ↔ Unifies g' W := by
  constructor <;> intro hU p hp <;>
    · have := hU p hp
      rw [apply_congr_of_pointwise h, apply_congr_of_pointwise h] at *
      simpa [apply_congr_of_pointwise h] using this

/-! ## Occurs-check completeness

If a variable `x` occurs in a strictly larger term `t` (an application), no
substitution can unify `var x =?= t`: applying any substitution makes the image of
`t` strictly larger than the image of `x`. This is what licenses the eliminate
move's occurs-check in the completeness direction: a failed occurs-check means no
unifier existed. -/

/-- A variable's image sits within the image of any term that contains it. The
size of `apply τ (var x)` is at most the size of `apply τ u` whenever `x ∈ vars u`. -/
theorem size_apply_var_le_of_mem [DecidableEq nu] (τ : Subst sigma nu) (x : nu) :
    ∀ (u : Term sigma nu), x ∈ Term.vars u →
      Term.size (apply τ (Term.var x)) ≤ Term.size (apply τ u) := by
  intro u
  induction u using Term.rec' with
  | hvar y =>
      intro hx
      rw [Term.vars_var, Finset.mem_singleton] at hx
      subst hx
      exact le_refl _
  | happ f args ih =>
      intro hx
      rw [Term.vars_app, Term.mem_varsList_iff] at hx
      obtain ⟨a, ha, hxa⟩ := hx
      have hstep := ih a ha hxa
      rw [apply_app]
      have hmem : apply τ a ∈ applyList τ args := by
        rw [applyList_eq_map]; exact List.mem_map_of_mem ha
      have hsub : Term.size (apply τ a) < Term.size (Term.app f (applyList τ args)) :=
        Term.size_lt_of_mem hmem
      omega

/-- The occurs-check is complete for unifiability: if `x` occurs in an application
`app g bs`, then no substitution unifies `var x =?= app g bs`, because the image of
the application is strictly larger than the image of the variable. -/
theorem not_unifies_of_occurs_app [DecidableEq nu] (τ : Subst sigma nu) (x : nu)
    (g : sigma) (bs : List (Term sigma nu)) (hocc : occurs x (Term.app g bs) = true) :
    apply τ (Term.var x) ≠ apply τ (Term.app g bs) := by
  intro heq
  have hx : x ∈ Term.vars (Term.app g bs) := (occurs_iff_mem_vars x _).1 hocc
  rw [Term.vars_app, Term.mem_varsList_iff] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  have hstep := size_apply_var_le_of_mem τ x a hxa
  have hmem : apply τ a ∈ applyList τ bs := by
    rw [applyList_eq_map]; exact List.mem_map_of_mem ha
  have hsub : Term.size (apply τ a) < Term.size (Term.app g (applyList τ bs)) :=
    Term.size_lt_of_mem hmem
  rw [apply_app] at heq
  rw [heq] at hstep
  omega

/-! ## Soundness of the worklist solver

`solve W = some μ` forces `μ` to unify every equation of `W`. Proved by the
custom recursion principle `solve.induct`, which supplies the induction
hypothesis on exactly the smaller worklist each move recurses into. -/

/-- Worklist soundness: a substitution returned by `solve` unifies the whole
worklist. The five moves: the empty list returns the identity, which trivially
unifies the empty problem; delete adds a reflexive head equation; the eliminate
moves rebuild the head equation from `comp_subst1_unifies_head` and the tail from
`Unifies_wlSubst1`; decompose rebuilds the application equation from
`Unifies_zipPairs_iff`. -/
theorem solve_unifies [DecidableEq sigma] [DecidableEq nu]
    (W : List (Term sigma nu × Term sigma nu)) (μ : Subst sigma nu)
    (h : solve W = some μ) : Unifies μ W := by
  induction W using solve.induct generalizing μ with
  | case1 =>
      -- empty worklist
      simp
  | case2 y rest ih =>
      -- delete `var y =?= var y`
      rw [solve] at h
      simp only at h
      have hrest := ih μ h
      rw [Unifies_cons]
      exact ⟨rfl, hrest⟩
  | case3 x y rest hxy ih =>
      -- eliminate `var x := var y`, `x ≠ y`
      rw [solve] at h
      simp only [if_neg hxy, Option.map_eq_some_iff] at h
      obtain ⟨s₀, hs₀, rfl⟩ := h
      have hocc : occurs x (Term.var (sigma := sigma) y) = false := by
        simp only [occurs_var, decide_eq_false_iff_not]; exact hxy
      rw [Unifies_cons]
      refine ⟨comp_subst1_unifies_head s₀ x (Term.var y) hocc, ?_⟩
      exact (Unifies_wlSubst1 s₀ x (Term.var y) rest).1 (ih s₀ hs₀)
  | case4 x g bs rest hocc =>
      -- occurs-check failure: `solve = none`, contradiction
      rw [solve] at h
      simp only [if_pos hocc, reduceCtorEq] at h
  | case5 x g bs rest hocc ih =>
      -- eliminate `var x := app g bs`
      rw [solve] at h
      simp only [if_neg hocc, Option.map_eq_some_iff] at h
      obtain ⟨s₀, hs₀, rfl⟩ := h
      have hoccf : occurs x (Term.app g bs) = false := by simpa using hocc
      rw [Unifies_cons]
      refine ⟨comp_subst1_unifies_head s₀ x (Term.app g bs) hoccf, ?_⟩
      exact (Unifies_wlSubst1 s₀ x (Term.app g bs) rest).1 (ih s₀ hs₀)
  | case6 f as y rest hocc =>
      -- occurs-check failure on the oriented case: `solve = none`, contradiction
      rw [solve] at h
      simp only [if_pos hocc, reduceCtorEq] at h
  | case7 f as y rest hocc ih =>
      -- orient then eliminate `var y := app f as`
      rw [solve] at h
      simp only [if_neg hocc, Option.map_eq_some_iff] at h
      obtain ⟨s₀, hs₀, rfl⟩ := h
      have hoccf : occurs y (Term.app f as) = false := by simpa using hocc
      rw [Unifies_cons]
      refine ⟨?_, ?_⟩
      · -- the head is oriented `app f as =?= var y`; symmetric of the eliminate head
        exact (comp_subst1_unifies_head s₀ y (Term.app f as) hoccf).symm
      · exact (Unifies_wlSubst1 s₀ y (Term.app f as) rest).1 (ih s₀ hs₀)
  | case8 f as g bs rest hfg ih =>
      -- decompose on matching head and arity
      rw [solve] at h
      simp only [if_pos hfg] at h
      have happ := ih μ h
      rw [Unifies_append] at happ
      obtain ⟨hzip, hrest⟩ := happ
      rw [Unifies_cons]
      obtain ⟨hf, hlen⟩ := hfg
      subst hf
      exact ⟨(Unifies_zipPairs_iff μ f as bs hlen).1 hzip, hrest⟩
  | case9 f as g bs rest hfg =>
      -- head/arity clash: `solve = none`, contradiction
      rw [solve] at h
      simp only [if_neg hfg, reduceCtorEq] at h

/-! ## Completeness of the worklist solver

If any substitution unifies the whole worklist, `solve` succeeds. Proved by
`solve.induct`. The eliminate moves transport the assumed unifier across
`wlSubst1` (the unifier absorbs `subst1` by `comp_subst1_eq_of_unifies`), and the
occurs-check branches are impossible because `not_unifies_of_occurs_app` rules out
a unifier of the head equation. -/

/-- Worklist completeness: a unifiable worklist is solved. -/
theorem solve_isSome [DecidableEq sigma] [DecidableEq nu]
    (W : List (Term sigma nu × Term sigma nu)) (hex : ∃ τ : Subst sigma nu, Unifies τ W) :
    (solve W).isSome := by
  induction W using solve.induct with
  | case1 =>
      -- empty worklist
      rw [solve]; rfl
  | case2 y rest ih =>
      -- delete `var y =?= var y`
      rw [solve]; simp only
      apply ih
      obtain ⟨τ, hτ⟩ := hex
      rw [Unifies_cons] at hτ
      exact ⟨τ, hτ.2⟩
  | case3 x y rest hxy ih =>
      -- eliminate `var x := var y`, `x ≠ y`
      rw [solve, if_neg hxy, Option.isSome_map]
      apply ih
      obtain ⟨τ, hτ⟩ := hex
      rw [Unifies_cons] at hτ
      refine ⟨τ, ?_⟩
      rw [Unifies_wlSubst1]
      rw [Unifies_congr_of_pointwise (comp_subst1_eq_of_unifies τ x (Term.var y) hτ.1)]
      exact hτ.2
  | case4 x g bs rest hocc =>
      -- occurs-check failure is impossible under a unifier
      obtain ⟨τ, hτ⟩ := hex
      rw [Unifies_cons] at hτ
      exact absurd hτ.1 (not_unifies_of_occurs_app τ x g bs hocc)
  | case5 x g bs rest hocc ih =>
      -- eliminate `var x := app g bs`
      rw [solve, if_neg hocc, Option.isSome_map]
      apply ih
      obtain ⟨τ, hτ⟩ := hex
      rw [Unifies_cons] at hτ
      refine ⟨τ, ?_⟩
      rw [Unifies_wlSubst1]
      rw [Unifies_congr_of_pointwise (comp_subst1_eq_of_unifies τ x (Term.app g bs) hτ.1)]
      exact hτ.2
  | case6 f as y rest hocc =>
      -- oriented occurs-check failure is impossible under a unifier
      obtain ⟨τ, hτ⟩ := hex
      rw [Unifies_cons] at hτ
      exact absurd hτ.1.symm (not_unifies_of_occurs_app τ y f as hocc)
  | case7 f as y rest hocc ih =>
      -- orient then eliminate `var y := app f as`
      rw [solve, if_neg hocc, Option.isSome_map]
      apply ih
      obtain ⟨τ, hτ⟩ := hex
      rw [Unifies_cons] at hτ
      refine ⟨τ, ?_⟩
      rw [Unifies_wlSubst1]
      rw [Unifies_congr_of_pointwise (comp_subst1_eq_of_unifies τ y (Term.app f as) hτ.1.symm)]
      exact hτ.2
  | case8 f as g bs rest hfg ih =>
      -- decompose on matching head and arity
      rw [solve, if_pos hfg]
      apply ih
      obtain ⟨τ, hτ⟩ := hex
      rw [Unifies_cons] at hτ
      obtain ⟨hf, hlen⟩ := hfg
      subst hf
      refine ⟨τ, ?_⟩
      rw [Unifies_append]
      exact ⟨(Unifies_zipPairs_iff τ f as bs hlen).2 hτ.1, hτ.2⟩
  | case9 f as g bs rest hfg =>
      -- head/arity clash is impossible under a unifier
      obtain ⟨τ, hτ⟩ := hex
      rw [Unifies_cons] at hτ
      -- a unifier forces equal heads and equal arity, contradicting the clash
      exfalso
      apply hfg
      have heq := hτ.1
      rw [apply_app, apply_app] at heq
      have h1 : f = g := by injection heq
      have h2 : applyList τ as = applyList τ bs := by injection heq
      refine ⟨h1, ?_⟩
      have := congrArg List.length h2
      rwa [applyList_eq_map, applyList_eq_map, List.length_map, List.length_map] at this

/-! ## Most-generality of the worklist solver

The keystone. `solve W = some μ` returns a substitution through which every unifier
`τ` of `W` factors: `∃ ρ, ∀ x, τ x = (ρ.comp μ) x`. The eliminate move is the
crux, and the elegant point is that the factoring substitution `ρ` produced by the
induction hypothesis on the pushed-through worklist works unchanged for the
composed result, because the unifier `τ` absorbs the single-point substitution that
the move applied. -/

/-- The eliminate move's most-generality step. If `τ` factors through `s₀` (the
substitution returned for the pushed-through worklist) via `ρ`, and `τ` absorbs the
single-point substitution `subst1 x t` of the move, then the very same `ρ` factors
`τ` through the composed substitution `s₀.comp (subst1 x t)`. -/
theorem factor_through_comp_subst1 [DecidableEq nu] {τ ρ s₀ : Subst sigma nu}
    (x : nu) (t : Term sigma nu)
    (hfac : ∀ z, τ z = ρ.apply (s₀ z))
    (habsorb : ∀ z, (τ.comp (subst1 x t)) z = τ z) :
    ∀ z, τ z = (ρ.comp (s₀.comp (subst1 x t))) z := by
  intro z
  -- unfold the composite into `ρ.apply (s₀.apply (subst1 x t z))`, then refold the
  -- inner two applications into `(ρ.comp s₀).apply (subst1 x t z)`
  rw [comp_apply_var, comp_apply_var, ← apply_comp]
  -- `ρ.comp s₀` and `τ` agree pointwise
  have hpt : ∀ w, (ρ.comp s₀) w = τ w := by
    intro w; rw [comp_apply_var]; exact (hfac w).symm
  rw [apply_congr_of_pointwise hpt (subst1 x t z)]
  have := habsorb z
  rw [comp_apply_var] at this
  exact this.symm

/-- Worklist most-generality: every unifier of the worklist factors through the
substitution `solve` returns. Proved by `solve.induct`; the eliminate cases reuse
the induction hypothesis's factoring substitution unchanged via
`factor_through_comp_subst1`. -/
theorem solve_mostGeneral [DecidableEq sigma] [DecidableEq nu]
    (W : List (Term sigma nu × Term sigma nu)) (μ : Subst sigma nu)
    (h : solve W = some μ) (τ : Subst sigma nu) (hτ : Unifies τ W) :
    ∃ ρ : Subst sigma nu, ∀ x, τ x = (ρ.comp μ) x := by
  induction W using solve.induct generalizing μ τ with
  | case1 =>
      -- empty worklist: `μ = id`, so `τ` factors through `μ` via `τ` itself
      rw [solve, Option.some.injEq] at h
      subst h
      refine ⟨τ, fun z => ?_⟩
      rw [comp_apply_var]; rfl
  | case2 y rest ih =>
      -- delete: factorization is inherited from the tail
      rw [solve] at h
      simp only at h
      rw [Unifies_cons] at hτ
      exact ih μ h τ hτ.2
  | case3 x y rest hxy ih =>
      -- eliminate `var x := var y`, `x ≠ y`
      rw [solve, if_neg hxy, Option.map_eq_some_iff] at h
      obtain ⟨s₀, hs₀, rfl⟩ := h
      rw [Unifies_cons] at hτ
      -- transport the unifier across `wlSubst1`
      have habsorb := comp_subst1_eq_of_unifies τ x (Term.var y) hτ.1
      have hτ' : Unifies τ (wlSubst1 x (Term.var y) rest) := by
        rw [Unifies_wlSubst1, Unifies_congr_of_pointwise habsorb]; exact hτ.2
      obtain ⟨ρ, hρ⟩ := ih s₀ hs₀ τ hτ'
      exact ⟨ρ, factor_through_comp_subst1 x (Term.var y) hρ habsorb⟩
  | case4 x g bs rest hocc =>
      -- occurs-check failure: `solve = none`, contradicts `some μ`
      rw [solve, if_pos hocc] at h
      simp only [reduceCtorEq] at h
  | case5 x g bs rest hocc ih =>
      -- eliminate `var x := app g bs`
      rw [solve, if_neg hocc, Option.map_eq_some_iff] at h
      obtain ⟨s₀, hs₀, rfl⟩ := h
      rw [Unifies_cons] at hτ
      have habsorb := comp_subst1_eq_of_unifies τ x (Term.app g bs) hτ.1
      have hτ' : Unifies τ (wlSubst1 x (Term.app g bs) rest) := by
        rw [Unifies_wlSubst1, Unifies_congr_of_pointwise habsorb]; exact hτ.2
      obtain ⟨ρ, hρ⟩ := ih s₀ hs₀ τ hτ'
      exact ⟨ρ, factor_through_comp_subst1 x (Term.app g bs) hρ habsorb⟩
  | case6 f as y rest hocc =>
      -- oriented occurs-check failure: `solve = none`, contradicts `some μ`
      rw [solve, if_pos hocc] at h
      simp only [reduceCtorEq] at h
  | case7 f as y rest hocc ih =>
      -- orient then eliminate `var y := app f as`
      rw [solve, if_neg hocc, Option.map_eq_some_iff] at h
      obtain ⟨s₀, hs₀, rfl⟩ := h
      rw [Unifies_cons] at hτ
      have habsorb := comp_subst1_eq_of_unifies τ y (Term.app f as) hτ.1.symm
      have hτ' : Unifies τ (wlSubst1 y (Term.app f as) rest) := by
        rw [Unifies_wlSubst1, Unifies_congr_of_pointwise habsorb]; exact hτ.2
      obtain ⟨ρ, hρ⟩ := ih s₀ hs₀ τ hτ'
      exact ⟨ρ, factor_through_comp_subst1 y (Term.app f as) hρ habsorb⟩
  | case8 f as g bs rest hfg ih =>
      -- decompose: factorization is inherited from the argument worklist
      rw [solve, if_pos hfg] at h
      rw [Unifies_cons] at hτ
      obtain ⟨hf, hlen⟩ := hfg
      subst hf
      apply ih μ h τ
      rw [Unifies_append]
      exact ⟨(Unifies_zipPairs_iff τ f as bs hlen).2 hτ.1, hτ.2⟩
  | case9 f as g bs rest hfg =>
      -- head/arity clash: `solve = none`, contradicts `some μ`
      rw [solve, if_neg hfg] at h
      simp only [reduceCtorEq] at h

/-! ## The headline single-equation theorems

`unify s t = solve [(s, t)]` by definition, so the three roadmap headline
statements are the singleton specializations of the worklist invariants above,
bridged through `Unifies_singleton`. -/

/-- Soundness of `unify`: a returned substitution unifies the two terms. Relation:
syntactic equality of substitution images. Strategy: not applicable (unification,
not rewriting). Trust: kernel-only. The singleton specialization of
`solve_unifies`. -/
theorem unify_sound [DecidableEq sigma] [DecidableEq nu] {s t : Term sigma nu}
    {sigma' : Subst sigma nu} (h : unify s t = some sigma') :
    sigma'.apply s = sigma'.apply t := by
  have hsolve : solve [(s, t)] = some sigma' := h
  have := solve_unifies [(s, t)] sigma' hsolve
  rw [Unifies_singleton] at this
  exact this

/-- Completeness of `unify`: whenever some substitution unifies the two terms,
`unify` succeeds. Relation: existence of a unifier. Trust: kernel-only. The
singleton specialization of `solve_isSome`. -/
theorem unify_complete [DecidableEq sigma] [DecidableEq nu] {s t : Term sigma nu}
    (hex : ∃ tau : Subst sigma nu, tau.apply s = tau.apply t) :
    (unify s t).isSome := by
  have hsolve : (solve [(s, t)]).isSome := by
    apply solve_isSome
    obtain ⟨tau, htau⟩ := hex
    exact ⟨tau, (Unifies_singleton tau s t).2 htau⟩
  exact hsolve

/-- Most-generality of `unify`: the returned substitution is the most general
unifier, in that every unifier `tau` of the two terms factors through it,
`∃ rho, ∀ x, tau x = (rho.comp sigma') x`. Relation: factoring of substitutions
through the returned one. Trust: kernel-only. The singleton specialization of
`solve_mostGeneral`; together with `unify_sound` this is the Martelli-Montanari
most-general-unifier characterization, returned as data. -/
theorem unify_mostGeneral [DecidableEq sigma] [DecidableEq nu] {s t : Term sigma nu}
    {sigma' : Subst sigma nu} (h : unify s t = some sigma')
    (tau : Subst sigma nu) (htau : tau.apply s = tau.apply t) :
    ∃ rho : Subst sigma nu, ∀ x, tau x = (rho.comp sigma') x := by
  have hsolve : solve [(s, t)] = some sigma' := h
  exact solve_mostGeneral [(s, t)] sigma' hsolve tau ((Unifies_singleton tau s t).2 htau)

end OperatorKO7.Meta.Rewriting

/-! ## Verification: headline types and axiom audit -/

open OperatorKO7.Meta.Rewriting in
#check @unify_sound
open OperatorKO7.Meta.Rewriting in
#check @unify_complete
open OperatorKO7.Meta.Rewriting in
#check @unify_mostGeneral

open OperatorKO7.Meta.Rewriting in
#print axioms unify_sound
open OperatorKO7.Meta.Rewriting in
#print axioms unify_complete
open OperatorKO7.Meta.Rewriting in
#print axioms unify_mostGeneral
