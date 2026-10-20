import OperatorKO7.Meta.Rewriting.ParallelReductionConfluence
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness

/-!
# One-step reducts of a finite first-order system

For a finite system whose right-hand sides use only left-hand-side variables, the one-step
reducts of a term form a computable finite set: the root reducts come from matching each
left-hand side, and the other reducts rewrite one argument. Without the variable condition one
rule already has a reduct for every variable.

Relation: the one-step rewrite relation `Step R`.
Property: a finite set of reducts, sound and complete for `Step R`.
Trust: kernel only.
Scope: finite rule lists over signature and variable types with decidable equality.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FiniteTRSReducts

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

open scoped Subst

universe u v

variable {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]

omit [DecidableEq sigma] in
/-- Substitutions with equal instances of `t` agree on the variables of `t`. -/
theorem eqOn_vars_of_apply_eq {s s' : Subst sigma nu} :
    ∀ t : Term sigma nu, Subst.apply s t = Subst.apply s' t → ∀ x ∈ Term.vars t, s x = s' x := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
      intro h x hx
      simp only [Subst.apply_var, Term.vars, Finset.mem_singleton] at h hx
      subst hx
      exact h
  | happ f args ih =>
      intro h x hx
      simp only [Subst.apply_app] at h
      have hlist : Subst.applyList s args = Subst.applyList s' args := (Term.app.inj h).2
      have hmap : args.map (Subst.apply s) = args.map (Subst.apply s') := by
        simpa only [Subst.applyList_eq_map] using hlist
      simp only [Term.vars_app] at hx
      rw [Term.mem_varsList_iff] at hx
      obtain ⟨a, ha, hxa⟩ := hx
      exact ih a ha ((List.map_inj_left.1 hmap) a ha) x hxa

/-- The root reducts of `s`: each rule whose left side matches `s` contributes its instance. -/
def rootReducts (R : TRS sigma nu) (s : Term sigma nu) : Finset (Term sigma nu) :=
  (R.filterMap fun rule => (matchAgainst rule.lhs s).map fun σ => Subst.apply σ rule.rhs).toFinset

mutual
/-- All one-step reducts of a term. -/
def reducts (R : TRS sigma nu) : Term sigma nu → Finset (Term sigma nu)
  | .var _ => ∅
  | .app f args => rootReducts R (.app f args) ∪ (reductsList R args).image (Term.app f)

/-- All argument lists one argument step away. -/
def reductsList (R : TRS sigma nu) : List (Term sigma nu) → Finset (List (Term sigma nu))
  | [] => ∅
  | a :: rest => (reducts R a).image (· :: rest) ∪ (reductsList R rest).image (a :: ·)
end

@[simp] theorem reducts_var (R : TRS sigma nu) (x : nu) : reducts R (.var x) = ∅ := rfl

@[simp] theorem reducts_app (R : TRS sigma nu) (f : sigma) (args : List (Term sigma nu)) :
    reducts R (.app f args) =
      rootReducts R (.app f args) ∪ (reductsList R args).image (Term.app f) := rfl

@[simp] theorem reductsList_nil (R : TRS sigma nu) : reductsList R [] = ∅ := rfl

@[simp] theorem reductsList_cons (R : TRS sigma nu) (a : Term sigma nu)
    (rest : List (Term sigma nu)) :
    reductsList R (a :: rest) =
      (reducts R a).image (· :: rest) ∪ (reductsList R rest).image (a :: ·) := rfl

theorem mem_rootReducts_iff (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) (s u : Term sigma nu) :
    u ∈ rootReducts R s ↔ rootStep R s u := by
  constructor
  · intro h
    rw [rootReducts, List.mem_toFinset, List.mem_filterMap] at h
    obtain ⟨rule, hrule, hsome⟩ := h
    rw [Option.map_eq_some_iff] at hsome
    obtain ⟨σ, hmatch, hσu⟩ := hsome
    exact ⟨rule, hrule, σ, (matchAgainst_sound hmatch).symm, hσu.symm⟩
  · rintro ⟨rule, hrule, σ, hsl, hsu⟩
    have hcomp : (matchAgainst rule.lhs s).isSome = true :=
      matchAgainst_complete (l := rule.lhs) (t := s) hsl.symm
    obtain ⟨σ', hσ'⟩ : ∃ σ', matchAgainst rule.lhs s = some σ' := by
      cases hm : matchAgainst rule.lhs s with
      | none =>
          rw [hm] at hcomp
          simp at hcomp
      | some σ' => exact ⟨σ', rfl⟩
    have hsound' := matchAgainst_sound hσ'
    have hst : Subst.apply σ' rule.lhs = Subst.apply σ rule.lhs := by
      rw [hsound', hsl]
    have hrhs : Subst.apply σ' rule.rhs = Subst.apply σ rule.rhs :=
      apply_congr_of_eq_on_vars σ' σ rule.rhs
        (fun x hx => eqOn_vars_of_apply_eq rule.lhs hst x (hvars rule hrule hx))
    rw [rootReducts, List.mem_toFinset, List.mem_filterMap]
    exact ⟨rule, hrule, by rw [hσ']; exact congrArg some (hrhs.trans hsu.symm)⟩

theorem mem_reductsList_iff (R : TRS sigma nu) :
    ∀ xs : List (Term sigma nu), (∀ a ∈ xs, ∀ u, u ∈ reducts R a ↔ Step R a u) →
      ∀ ys, ys ∈ reductsList R xs ↔ ArgStep R xs ys := by
  intro xs
  induction xs with
  | nil =>
      intro _ ys
      rw [reductsList_nil]
      constructor
      · intro h
        exact absurd h (Finset.notMem_empty ys)
      · intro h
        exact absurd h (not_argStep_nil R ys)
  | cons a rest ih =>
      intro hxs ys
      rw [reductsList_cons, Finset.mem_union, Finset.mem_image, Finset.mem_image,
        argStep_cons_iff R a rest ys]
      constructor
      · rintro (⟨b, hb, rfl⟩ | ⟨rest', hrest', rfl⟩)
        · exact Or.inl ⟨b, (hxs a List.mem_cons_self b).1 hb, rfl⟩
        · exact Or.inr ⟨rest',
            (ih (fun b hb => hxs b (List.mem_cons_of_mem a hb)) rest').1 hrest', rfl⟩
      · rintro (⟨b, hab, rfl⟩ | ⟨rest', hrest', rfl⟩)
        · exact Or.inl ⟨b, (hxs a List.mem_cons_self b).2 hab, rfl⟩
        · exact Or.inr ⟨rest',
            (ih (fun b hb => hxs b (List.mem_cons_of_mem a hb)) rest').2 hrest', rfl⟩

/-- **Finite branching.** -/
theorem mem_reducts_iff (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) :
    ∀ t u : Term sigma nu, u ∈ reducts R t ↔ Step R t u := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro u
      rw [reducts_var]
      constructor
      · intro h
        exact absurd h (Finset.notMem_empty u)
      · intro h
        exact absurd h (not_step_var R x u)
  | happ f args ih =>
      intro u
      rw [reducts_app, Finset.mem_union, Finset.mem_image, step_app_iff R f args u]
      constructor
      · rintro (hroot | ⟨a', ha', rfl⟩)
        · exact Or.inl ((mem_rootReducts_iff R hvars (.app f args) u).1 hroot)
        · exact Or.inr ⟨a', (mem_reductsList_iff R args (fun a ha v => ih a ha v) a').1 ha',
            rfl⟩
      · rintro (hroot | ⟨args', harg, rfl⟩)
        · exact Or.inl ((mem_rootReducts_iff R hvars (.app f args) u).2 hroot)
        · exact Or.inr ⟨args',
            (mem_reductsList_iff R args (fun a ha v => ih a ha v) args').2 harg, rfl⟩

/-- **The variable condition is required**: `c → x` has a reduct for every variable. -/
theorem freshTRS_infinitely_branching :
    Set.Infinite {u : Term Unit Nat | Step freshTRS (.app () []) u} := by
  refine Set.infinite_of_injective_forall_mem (f := Term.var) ?_ ?_
  · intro m n h
    cases h
    rfl
  · intro n
    exact Step.root ⟨freshRule, List.mem_cons_self, fun _ => Term.var n, rfl, rfl⟩

end OperatorKO7.Meta.OperationalInexpressibility.FiniteTRSReducts
