import OperatorKO7.Meta.Rewriting.Term

/-!
# Substitutions for the generic rewriting library

Roadmap source: `ROADMAP-01-generic-critical-pair-lemma.md`, sections 4, 5, and
the keystone risk in section 8. A substitution is a total map from variables to
terms; application replaces each variable by its image. This module provides:

- `Subst.apply` (with the scoped notation `s • t`) and its `List` lift, with
  `@[simp]` unfolds for the variable and application cases;
- `Subst.comp` (composition) and `apply_comp` (application of a composite is the
  composite of applications);
- `occurs`, a structural occurs-check, with `occurs_iff_mem_vars`;
- `subst1`, single-point substitution;
- the load-bearing `FV_elim_strict_subset`: when `x` does not occur in `t`,
  applying `subst1 x t` removes `x` from the variable set and keeps the result
  within `(vars u).erase x ∪ vars t`. This bound powers unification termination
  and most-generality in the later unification wave.

Trust: kernel-only; baseline-only under `#print axioms`. The
`Classical.choice`/`propext` dependence comes from `Finset`/`DecidableEq`
plumbing only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

universe u v

/-- A substitution: a total map from variables to terms. -/
def Subst (sigma : Type u) (nu : Type v) := nu → Term sigma nu

namespace Subst

variable {sigma : Type u} {nu : Type v}

mutual
/-- Apply a substitution to a term, replacing each variable by its image. Uses
an auxiliary `applyList` so the nested recursion is structural. Mirrors the
proven `applySubst` blueprint. -/
def apply (s : Subst sigma nu) : Term sigma nu → Term sigma nu
  | .var x => s x
  | .app f args => .app f (applyList s args)
/-- Apply a substitution across an argument list. -/
def applyList (s : Subst sigma nu) : List (Term sigma nu) → List (Term sigma nu)
  | [] => []
  | a :: as => apply s a :: applyList s as
end

@[inherit_doc] scoped infixr:75 " • " => Subst.apply

@[simp] theorem apply_var (s : Subst sigma nu) (x : nu) : apply s (.var x) = s x := rfl
@[simp] theorem apply_app (s : Subst sigma nu) (f : sigma) (args : List (Term sigma nu)) :
    apply s (.app f args) = .app f (applyList s args) := rfl
@[simp] theorem applyList_nil (s : Subst sigma nu) :
    applyList s ([] : List (Term sigma nu)) = [] := rfl
@[simp] theorem applyList_cons (s : Subst sigma nu) (a : Term sigma nu)
    (as : List (Term sigma nu)) :
    applyList s (a :: as) = apply s a :: applyList s as := rfl

/-- `applyList` is the `List.map` of `apply`. -/
theorem applyList_eq_map (s : Subst sigma nu) (args : List (Term sigma nu)) :
    applyList s args = args.map (apply s) := by
  induction args with
  | nil => simp
  | cons a as ih => simp [ih]

/-- The identity substitution maps each variable to itself. -/
def id : Subst sigma nu := fun x => .var x

@[simp] theorem id_apply (t : Term sigma nu) : apply (Subst.id) t = t := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      simp only [apply_app, applyList_eq_map]
      congr 1
      exact List.map_congr_left ih |>.trans (List.map_id'' (fun a => rfl) ..) |>.trans rfl

/-! ## Composition -/

/-- Composition of substitutions: `(comp r s) x = r.apply (s x)`. Applying the
composite equals applying `s` then `r` (see `apply_comp`). -/
def comp (r s : Subst sigma nu) : Subst sigma nu := fun x => apply r (s x)

@[simp] theorem comp_apply_var (r s : Subst sigma nu) (x : nu) :
    comp r s x = apply r (s x) := rfl

/-- Applying a composite substitution equals applying the two substitutions in
sequence. The keystone algebra lemma for substitution. -/
theorem apply_comp (r s : Subst sigma nu) (t : Term sigma nu) :
    apply (comp r s) t = apply r (apply s t) := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      simp only [apply_app, applyList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      simpa using ih a ha

/-! ## Variables of a substituted term -/

/-- A variable occurs in `apply s w` exactly when it occurs in the image `s y`
of some variable `y` occurring in `w`. This is the substitution-image
characterization of the variable set, the engine behind the occurs-check
properties below. -/
theorem mem_vars_apply_iff [DecidableEq nu] (s : Subst sigma nu) :
    ∀ (w : Term sigma nu) (z : nu),
      z ∈ Term.vars (apply s w) ↔ ∃ y ∈ Term.vars w, z ∈ Term.vars (s y) := by
  intro w
  induction w using Term.rec' with
  | hvar x =>
      intro z
      simp only [apply_var, Term.vars_var, Finset.mem_singleton]
      constructor
      · intro hz; exact ⟨x, rfl, hz⟩
      · rintro ⟨y, rfl, hz⟩; exact hz
  | happ f args ih =>
      intro z
      simp only [apply_app, Term.vars_app, applyList_eq_map]
      constructor
      · intro hz
        rw [Term.mem_varsList_iff] at hz
        obtain ⟨c, hc, hzc⟩ := hz
        rw [List.mem_map] at hc
        obtain ⟨a, ha, rfl⟩ := hc
        obtain ⟨y, hy, hzy⟩ := (ih a ha z).1 hzc
        refine ⟨y, ?_, hzy⟩
        rw [Term.mem_varsList_iff]
        exact ⟨a, ha, hy⟩
      · rintro ⟨y, hy, hzy⟩
        rw [Term.mem_varsList_iff] at hy
        obtain ⟨a, ha, hya⟩ := hy
        rw [Term.mem_varsList_iff]
        refine ⟨apply s a, List.mem_map_of_mem ha, ?_⟩
        exact (ih a ha z).2 ⟨y, hya, hzy⟩

/-! ## Occurs-check -/

mutual
/-- Structural occurs-check: `occurs x t` is `true` exactly when the variable `x`
occurs somewhere in `t` (see `occurs_iff_mem_vars`). Uses an auxiliary
`occursList` so the nested recursion is structural. -/
def occurs [DecidableEq nu] (x : nu) : Term sigma nu → Bool
  | .var y => x = y
  | .app _ args => occursList x args
/-- Occurs-check across an argument list. -/
def occursList [DecidableEq nu] (x : nu) : List (Term sigma nu) → Bool
  | [] => false
  | a :: as => occurs x a || occursList x as
end

@[simp] theorem occurs_var [DecidableEq nu] (x y : nu) :
    occurs x (Term.var (sigma := sigma) y) = decide (x = y) := rfl
@[simp] theorem occurs_app [DecidableEq nu] (x : nu) (f : sigma)
    (args : List (Term sigma nu)) : occurs x (Term.app f args) = occursList x args := rfl
@[simp] theorem occursList_nil [DecidableEq nu] (x : nu) :
    occursList x ([] : List (Term sigma nu)) = false := rfl
@[simp] theorem occursList_cons [DecidableEq nu] (x : nu) (a : Term sigma nu)
    (as : List (Term sigma nu)) :
    occursList x (a :: as) = (occurs x a || occursList x as) := rfl

/-- The occurs-check agrees with membership in the variable set. -/
theorem occurs_iff_mem_vars [DecidableEq nu] (x : nu) :
    ∀ (t : Term sigma nu), occurs x t = true ↔ x ∈ Term.vars t := by
  intro t
  induction t using Term.rec' with
  | hvar y => simp [eq_comm]
  | happ f args ih =>
      simp only [occurs_app, Term.vars_app]
      induction args with
      | nil => simp
      | cons a as ihl =>
          simp only [occursList_cons, Bool.or_eq_true, Term.varsList_cons,
            Finset.mem_union]
          rw [ih a (by simp)]
          rw [ihl (fun c hc => ih c (by simp [hc]))]

/-- The occurs-check is `false` exactly when the variable is absent. -/
theorem not_occurs_iff_not_mem_vars [DecidableEq nu] (x : nu) (t : Term sigma nu) :
    occurs x t = false ↔ x ∉ Term.vars t := by
  rw [← occurs_iff_mem_vars (sigma := sigma)]
  simp

/-! ## Single-point substitution -/

/-- Single-point substitution: maps `x` to `t` and fixes every other variable. -/
def subst1 [DecidableEq nu] (x : nu) (t : Term sigma nu) : Subst sigma nu :=
  fun y => if y = x then t else .var y

@[simp] theorem subst1_same [DecidableEq nu] (x : nu) (t : Term sigma nu) :
    subst1 x t x = t := by simp [subst1]

theorem subst1_of_ne [DecidableEq nu] {x y : nu} (t : Term sigma nu) (h : y ≠ x) :
    subst1 x t y = .var y := by simp [subst1, h]

/-- The variable set of a single-point image: it is `vars t` at `x`, and the
singleton `{y}` otherwise. -/
theorem vars_subst1_apply_var [DecidableEq nu] (x : nu) (t : Term sigma nu) (y : nu) :
    Term.vars (subst1 x t y) = if y = x then Term.vars t else {y} := by
  by_cases h : y = x
  · subst h; simp
  · rw [subst1_of_ne t h]; simp [h]

/-! ## The load-bearing FV lemma -/

/-- Keystone for unification termination and most-generality: if `x` does not
occur in `t`, then applying the single-point substitution `subst1 x t` to any
term `u` removes `x` from the variable set, and the resulting variable set sits
within `(vars u).erase x` together with `vars t`.

The first conjunct is what makes the unification eliminate step strictly shrink
the free-variable measure; the second conjunct bounds the variables introduced
by the substitution. -/
theorem FV_elim_strict_subset [DecidableEq nu] (x : nu) (t : Term sigma nu)
    (hx : occurs x t = false) (u : Term sigma nu) :
    x ∉ Term.vars (apply (subst1 x t) u) ∧
      Term.vars (apply (subst1 x t) u) ⊆ (Term.vars u).erase x ∪ Term.vars t := by
  have hxt : x ∉ Term.vars t := (not_occurs_iff_not_mem_vars x t).1 hx
  constructor
  · -- x is absent from the image
    intro hmem
    rw [mem_vars_apply_iff] at hmem
    obtain ⟨y, _, hxy⟩ := hmem
    by_cases h : y = x
    · subst h
      rw [subst1_same] at hxy
      exact hxt hxy
    · rw [subst1_of_ne t h, Term.vars_var, Finset.mem_singleton] at hxy
      exact h hxy.symm
  · -- the image variables are bounded
    intro z hz
    rw [mem_vars_apply_iff] at hz
    obtain ⟨y, hyu, hzy⟩ := hz
    by_cases h : y = x
    · subst h
      rw [subst1_same] at hzy
      exact Finset.mem_union_right _ hzy
    · rw [subst1_of_ne t h, Term.vars_var, Finset.mem_singleton] at hzy
      subst hzy
      refine Finset.mem_union_left _ ?_
      rw [Finset.mem_erase]
      exact ⟨h, hyu⟩

end Subst

end OperatorKO7.Meta.Rewriting

/-! ## Axiom audit -/

open OperatorKO7.Meta.Rewriting in
#print axioms Subst.apply
open OperatorKO7.Meta.Rewriting in
#print axioms Subst.comp
open OperatorKO7.Meta.Rewriting in
#print axioms Subst.apply_comp
open OperatorKO7.Meta.Rewriting in
#print axioms Subst.occurs
open OperatorKO7.Meta.Rewriting in
#print axioms Subst.occurs_iff_mem_vars
open OperatorKO7.Meta.Rewriting in
#print axioms Subst.subst1
open OperatorKO7.Meta.Rewriting in
#print axioms Subst.FV_elim_strict_subset
