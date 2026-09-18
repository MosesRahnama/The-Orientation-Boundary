import OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
import OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope

set_option autoImplicit false

/-!
# Translation theorems for the kernel's classical fragments

Manuscript anchor: the composite-of-classical-fragments subsection of
`Rahnama_The_Distinction_Boundary`.

## Why this module exists

The manuscript reads `merge` as a semilattice, `recΔ` as a System-T recursor,
and `app` as sequential composition. Read as claims about the kernel relation
those readings are false: `merge (delta void) (delta (delta void))` and
`merge (delta (delta void)) (delta void)` are distinct normal forms, so `merge`
carries no commutativity, and `app` carries no root rule at all. The Duck Rule
route is to prove the translation the reading is reaching for instead of either
asserting the identity or dropping the reading. That is what this module does.

## What this module proves

* **Semilattice translation.** The interpretation `sem` sends `void` to the
  empty predicate and `merge` to union, and every other constructor to its own
  singleton. Under `sem` the three kernel merge rules become the unit and
  idempotence laws of a bounded join-semilattice, and associativity,
  commutativity, and idempotence hold in the image. So `merge` presents a
  bounded join-semilattice under a homomorphic interpretation, which is the
  proven form of the reading.
* **Iterator translation.** `recΔ b s (delta^[n] void)` reduces to the `n`-fold
  application of `s`, so the recursor is the iterator of System-T shape on
  `delta`-numerals. That is the proven form of the System-T reading.
* **Application is free.** `app` carries no root rule and is injective in both
  arguments, so it generates a free binary magma and any composition reading is
  an interpretation layered over that freeness.

## Claim boundaries

* `sem` is an interpretation into the metalanguage, not a kernel construction.
  The theorems say the merge fragment maps homomorphically onto a semilattice;
  they do not say the kernel proves associativity or commutativity, and
  `merge_not_commutative_in_kernel` records that it does not.

Relation: `Step`, `StepStar` (root). Closure: root and reflexive-transitive.
Strategy: not applicable. Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.TranslationTheorems

open OperatorKO7 Trace
open MetaSN_KO7
open OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity
open OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope

/-! ## The semilattice translation -/

/-- Interpretation of the kernel into predicates: `void` is the empty join,
`merge` is union, every other constructor contributes itself. -/
def sem : Trace → (Trace → Prop)
  | void => fun _ => False
  | merge a b => fun x => sem a x ∨ sem b x
  | delta t => fun x => x = delta t
  | integrate t => fun x => x = integrate t
  | app a b => fun x => x = app a b
  | recΔ a b c => fun x => x = recΔ a b c
  | eqW a b => fun x => x = eqW a b

/-- The left unit rule is the semilattice unit law. -/
theorem sem_merge_void_left (t : Trace) : sem (merge void t) = sem t := by
  funext x
  simp [sem]

/-- The right unit rule is the semilattice unit law on the other side. -/
theorem sem_merge_void_right (t : Trace) : sem (merge t void) = sem t := by
  funext x
  simp [sem]

/-- The cancel rule is the semilattice idempotence law. -/
theorem sem_merge_cancel (t : Trace) : sem (merge t t) = sem t := by
  funext x
  simp [sem]

/-- Union is commutative in the image. -/
theorem sem_merge_comm (a b : Trace) : sem (merge a b) = sem (merge b a) := by
  funext x
  simp [sem]
  tauto

/-- Union is associative in the image. -/
theorem sem_merge_assoc (a b c : Trace) :
    sem (merge (merge a b) c) = sem (merge a (merge b c)) := by
  funext x
  simp [sem]
  tauto

/-- **Semilattice translation.** Under `sem` the merge fragment satisfies the
bounded join-semilattice laws, and the three kernel rules are its unit and
idempotence laws. -/
theorem merge_presents_bounded_semilattice :
    (∀ t, sem (merge void t) = sem t) ∧
    (∀ t, sem (merge t void) = sem t) ∧
    (∀ t, sem (merge t t) = sem t) ∧
    (∀ a b, sem (merge a b) = sem (merge b a)) ∧
    (∀ a b c, sem (merge (merge a b) c) = sem (merge a (merge b c))) :=
  ⟨sem_merge_void_left, sem_merge_void_right, sem_merge_cancel,
    sem_merge_comm, sem_merge_assoc⟩

/-- Every kernel merge rule is sound for the interpretation, so `sem` is a
homomorphism on the merge fragment. -/
theorem sem_sound_on_merge_rules (t : Trace) :
    sem (merge void t) = sem t ∧ sem (merge t void) = sem t ∧ sem (merge t t) = sem t :=
  ⟨sem_merge_void_left t, sem_merge_void_right t, sem_merge_cancel t⟩

/-- The scope fence: commutativity holds in the image and fails in the kernel,
so the semilattice reading is a translation and not an identity. -/
theorem merge_not_commutative_in_kernel :
    merge (delta void) (delta (delta void)) ≠ merge (delta (delta void)) (delta void) := by
  intro h
  cases h

/-! ## The iterator translation -/

/-- The `n`-fold application of the step argument. -/
def iterApp (b s : Trace) : ℕ → Trace
  | 0 => b
  | (n + 1) => app s (iterApp b s n)

/-- The right `app` congruence lifts to the contextual closure. -/
theorem ctxStar_appR (s : Trace) {x y : Trace}
    (h : CtxStar x y) :
    CtxStar (app s x) (app s y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact ih.tail (StepCtxFull.appR hlast)

/-- **Iterator translation.** On `delta`-numerals the recursor reduces to the
`n`-fold application of its step argument, which is the System-T iterator
shape. The reduction is contextual, since after the first step the remaining
redex sits under `app` and the root relation cannot reach it. -/
theorem recD_reduces_to_iterApp (b s : Trace) :
    ∀ n : ℕ, CtxStar
      (recΔ b s (dpow n)) (iterApp b s n) := by
  intro n
  induction n with
  | zero =>
      exact Relation.ReflTransGen.single (StepCtxFull.root (Step.R_rec_zero b s))
  | succ k ih =>
      refine Relation.ReflTransGen.head
        (StepCtxFull.root (Step.R_rec_succ b s (dpow k))) ?_
      exact ctxStar_appR s ih

/-! ## Application is free -/

/-- `app` carries no root rule. -/
theorem no_root_rule_for_app (a b u : Trace) : ¬ Step (app a b) u := by
  intro h
  cases h

/-- `app` is injective in both arguments, so it generates a free binary magma
and any composition reading is an interpretation over that freeness. -/
theorem app_free (a b c d : Trace) : app a b = app c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    injection h with h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## Non-vacuity -/

/-- R5 witness: the interpretation separates and identifies concretely. -/
theorem sem_nonvacuous :
    sem (merge void (delta void)) = sem (delta void) ∧
      merge (delta void) (delta (delta void)) ≠ merge (delta (delta void)) (delta void) :=
  ⟨sem_merge_void_left (delta void), merge_not_commutative_in_kernel⟩

/-- R5 witness: the iterator translation at a concrete numeral. -/
theorem iterApp_nonvacuous (b s : Trace) :
    iterApp b s 0 = b ∧ iterApp b s 1 = app s b := by
  constructor <;> rfl

end OperatorKO7.Meta.DistinctionBoundary.TranslationTheorems
