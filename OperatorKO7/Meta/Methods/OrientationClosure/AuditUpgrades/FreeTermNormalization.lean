import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination

/-!
# Normalization of the free recursor on terms with variables

Theorem 5.14 of the Orientation Boundary paper states that the free two-rule recursor terminates
and is confluent under root and under contextual rewriting, that every term has a computable normal
form, and that two terms are joinable exactly when their normal forms agree. The module
`FreeRecursorContext` proves this on the closed seven-constructor term type. This module proves it
on the free terms `FreeTerm ν` with variables in an arbitrary type `ν`, for root and for
contextual rewriting.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.AuditUpgrades.FreeTermNormalization

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.FreePolynomialTermination

universe u

variable {ν : Type u}

/-! ## Contextual rewriting -/

theorem star_in_context {a b : FreeTerm ν}
    (h : Relation.ReflTransGen ContextStep a b) (D : FreeContext ν) :
    Relation.ReflTransGen ContextStep (D.plug a) (D.plug b) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hs.outer D)

/-- The natural-valued weight of the coupled polynomial interpretation at the zero valuation. -/
def weight (t : FreeTerm ν) : Nat :=
  (coupledInterpretation 1 2).eval (fun _ => 0) t

theorem weight_context_decreases {a b : FreeTerm ν} (h : ContextStep a b) :
    weight b < weight a :=
  coupled_contextStep_decreases (by decide) (by decide) (fun _ => 0) h

theorem weight_star_le {a b : FreeTerm ν} (h : Relation.ReflTransGen ContextStep a b) :
    weight b ≤ weight a := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (Nat.le_of_lt (weight_context_decreases hs)).trans ih

/-- Evaluate a recursor once its three arguments are in normal form. -/
def recNormal (b s : FreeTerm ν) : FreeTerm ν → FreeTerm ν
  | .zero => b
  | .succ n => .wrap s (recNormal b s n)
  | .var x => .recur b s (.var x)
  | .wrap p q => .recur b s (.wrap p q)
  | .recur x y z => .recur b s (.recur x y z)

/-- The contextual normal form, computed bottom-up. -/
def normalize : FreeTerm ν → FreeTerm ν
  | .var x => .var x
  | .zero => .zero
  | .succ t => .succ (normalize t)
  | .wrap s t => .wrap (normalize s) (normalize t)
  | .recur b s n => recNormal (normalize b) (normalize s) (normalize n)

theorem normalize_recNormal (b s n : FreeTerm ν) :
    normalize (recNormal b s n) = recNormal (normalize b) (normalize s) (normalize n) := by
  induction n with
  | succ n ih => simp only [recNormal, normalize, ih]
  | _ => rfl

theorem normalize_idempotent (t : FreeTerm ν) : normalize (normalize t) = normalize t := by
  induction t <;> simp only [normalize, normalize_recNormal, *]

theorem normalize_context_congr {a b : FreeTerm ν} (C : FreeContext ν)
    (h : normalize a = normalize b) : normalize (C.plug a) = normalize (C.plug b) := by
  induction C <;> simp only [FreeContext.plug, normalize, *]

theorem normalize_root_step {a b : FreeTerm ν} (h : RootStep a b) :
    normalize a = normalize b := by
  cases h <;> rfl

theorem normalize_step {a b : FreeTerm ν} (h : ContextStep a b) : normalize a = normalize b := by
  cases h with
  | lift C hr => exact normalize_context_congr C (normalize_root_step hr)

theorem normalize_star {a b : FreeTerm ν} (h : Relation.ReflTransGen ContextStep a b) :
    normalize a = normalize b := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (normalize_step hs)

theorem recNormal_reachable (b s n : FreeTerm ν) :
    Relation.ReflTransGen ContextStep (.recur b s n) (recNormal b s n) := by
  induction n with
  | zero => exact .single (rootStep_contextStep (.recurZero b s))
  | succ n ih =>
      exact (Relation.ReflTransGen.single (rootStep_contextStep (.recurSucc b s n))).trans
        (star_in_context ih (.wrapRight s .hole))
  | var x => exact .refl
  | wrap p q _ _ => exact .refl
  | recur x y z _ _ _ => exact .refl

theorem normalize_reachable (t : FreeTerm ν) :
    Relation.ReflTransGen ContextStep t (normalize t) := by
  induction t with
  | var x => exact .refl
  | zero => exact .refl
  | succ t ih => exact star_in_context ih (.succ .hole)
  | wrap s t hs ht =>
      exact (star_in_context hs (.wrapLeft .hole t)).trans
        (star_in_context ht (.wrapRight (normalize s) .hole))
  | recur b s n hb hs hn =>
      exact (star_in_context hb (.recurBase .hole s n)).trans
        ((star_in_context hs (.recurStep (normalize b) .hole n)).trans
          ((star_in_context hn (.recurCounter (normalize b) (normalize s) .hole)).trans
            (recNormal_reachable (normalize b) (normalize s) (normalize n))))

theorem normalize_normal (t : FreeTerm ν) : ∀ u, ¬ ContextStep (normalize t) u := by
  intro u hu
  have hd := weight_context_decreases hu
  have hn := weight_star_le (normalize_reachable u)
  have he := normalize_step hu
  rw [normalize_idempotent] at he
  rw [← he] at hn
  omega

/--
Proves: contextual rewriting of the free recursor on terms with variables in any type terminates.
Does not prove: a bound on derivation length; that is `FreeDerivationalComplexity`.
Relation: `ContextStep` on `FreeTerm ν`.
Closure: every one-hole constructor context.
Strategy: the coupled polynomial interpretation.
Trust: Lean kernel with the axioms of `main_free_contextual_termination`.
Scope: every variable type `ν`.
-/
theorem ctx_terminating : WellFounded (fun u t : FreeTerm ν => ContextStep t u) :=
  main_free_contextual_termination ν

/--
Proves: contextual rewriting of the free recursor on terms with variables in any type is
confluent.
Does not prove: confluence of any extension of the two rules.
Relation: `ContextStep` on `FreeTerm ν`.
Closure: every one-hole constructor context.
Strategy: both reducts reach the common normal form `normalize a`.
Trust: Lean kernel.
Scope: every variable type `ν`.
-/
theorem ctx_confluent {a b c : FreeTerm ν}
    (hb : Relation.ReflTransGen ContextStep a b) (hc : Relation.ReflTransGen ContextStep a c) :
    ∃ d, Relation.ReflTransGen ContextStep b d ∧ Relation.ReflTransGen ContextStep c d := by
  refine ⟨normalize a, ?_, ?_⟩
  · rw [normalize_star hb]
    exact normalize_reachable b
  · rw [normalize_star hc]
    exact normalize_reachable c

/--
Proves: every term reduces contextually to `normalize t`, and `normalize t` admits no contextual
step.
Does not prove: anything about other normalization strategies; they reach the same normal form by
`ctx_unique_normal_form`.
Relation: `ContextStep` on `FreeTerm ν`.
Closure: every one-hole constructor context.
Strategy: structural recursion on the term.
Trust: Lean kernel.
Scope: every variable type `ν`, every term.
-/
theorem ctx_normalization_certificate (t : FreeTerm ν) :
    Relation.ReflTransGen ContextStep t (normalize t) ∧ (∀ u, ¬ ContextStep (normalize t) u) :=
  ⟨normalize_reachable t, normalize_normal t⟩

theorem ctx_unique_normal_form {a b : FreeTerm ν}
    (h : Relation.ReflTransGen ContextStep a b) (hb : ∀ u, ¬ ContextStep b u) :
    b = normalize a := by
  have hrefl : ∀ {u}, Relation.ReflTransGen ContextStep b u → b = u := by
    intro u hu
    cases hu using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hs _ _ => exact (hb _ hs).elim
  exact (hrefl (normalize_reachable b)).trans (normalize_star h).symm

/--
Proves: two terms with variables are contextually joinable exactly when their computed normal forms
agree.
Does not prove: anything about convertibility in extensions of the two rules.
Relation: `ContextStep` on `FreeTerm ν`.
Closure: every one-hole constructor context.
Strategy: invariance of `normalize` along steps and reachability of `normalize`.
Trust: Lean kernel.
Scope: every variable type `ν`, every pair of terms.
-/
theorem ctx_joinable_iff (a b : FreeTerm ν) :
    (∃ d, Relation.ReflTransGen ContextStep a d ∧ Relation.ReflTransGen ContextStep b d) ↔
      normalize a = normalize b := by
  constructor
  · rintro ⟨d, ha, hb⟩
    exact (normalize_star ha).trans (normalize_star hb).symm
  · intro he
    refine ⟨normalize b, ?_, normalize_reachable b⟩
    rw [← he]
    exact normalize_reachable a

/-! ## Root rewriting -/

/-- The root normal form: the base rule is followed into the base argument, and the successor rule
stops at the emitted wrapper. -/
def rootNormalize : FreeTerm ν → FreeTerm ν
  | .var x => .var x
  | .zero => .zero
  | .succ t => .succ t
  | .wrap s t => .wrap s t
  | .recur b _ .zero => rootNormalize b
  | .recur b s (.succ n) => .wrap s (.recur b s n)
  | .recur b s (.var x) => .recur b s (.var x)
  | .recur b s (.wrap p q) => .recur b s (.wrap p q)
  | .recur b s (.recur x y z) => .recur b s (.recur x y z)

theorem rootStep_deterministic {a b c : FreeTerm ν} (hb : RootStep a b) (hc : RootStep a c) :
    b = c := by
  cases hb <;> cases hc <;> rfl

theorem rootNormalize_reachable (t : FreeTerm ν) :
    Relation.ReflTransGen RootStep t (rootNormalize t) := by
  induction t with
  | var x => exact .refl
  | zero => exact .refl
  | succ t _ => exact .refl
  | wrap s t _ _ => exact .refl
  | recur b s n hb _ _ =>
      cases n with
      | zero =>
          simp only [rootNormalize]
          exact Relation.ReflTransGen.head (.recurZero b s) hb
      | succ n =>
          simp only [rootNormalize]
          exact .single (.recurSucc b s n)
      | var x => exact .refl
      | wrap p q => exact .refl
      | recur x y z => exact .refl

theorem rootNormalize_normal (t : FreeTerm ν) : ∀ u, ¬ RootStep (rootNormalize t) u := by
  induction t with
  | var x => intro u hu; simp only [rootNormalize] at hu; cases hu
  | zero => intro u hu; simp only [rootNormalize] at hu; cases hu
  | succ t _ => intro u hu; simp only [rootNormalize] at hu; cases hu
  | wrap s t _ _ => intro u hu; simp only [rootNormalize] at hu; cases hu
  | recur b s n hb _ _ =>
      cases n with
      | zero =>
          simp only [rootNormalize]
          exact hb
      | succ n => intro u hu; simp only [rootNormalize] at hu; cases hu
      | var x => intro u hu; simp only [rootNormalize] at hu; cases hu
      | wrap p q => intro u hu; simp only [rootNormalize] at hu; cases hu
      | recur x y z => intro u hu; simp only [rootNormalize] at hu; cases hu

theorem root_star_total {a b c : FreeTerm ν}
    (hb : Relation.ReflTransGen RootStep a b) (hc : Relation.ReflTransGen RootStep a c) :
    Relation.ReflTransGen RootStep b c ∨ Relation.ReflTransGen RootStep c b := by
  induction hb using Relation.ReflTransGen.head_induction_on generalizing c with
  | refl => exact Or.inl hc
  | head hab hrest ih =>
      rcases Relation.ReflTransGen.cases_head hc with heq | ⟨a'', hac, hrest'⟩
      · subst heq
        exact Or.inr (Relation.ReflTransGen.head hab hrest)
      · have hdet := rootStep_deterministic hab hac
        subst hdet
        exact ih hrest'

theorem root_normal_star_eq {x y : FreeTerm ν} (hn : ∀ u, ¬ RootStep x u)
    (h : Relation.ReflTransGen RootStep x y) : x = y := by
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hs _ _ => exact (hn _ hs).elim

/--
Proves: root rewriting of the free recursor on terms with variables in any type terminates and is
confluent.
Does not prove: anything about contextual rewriting; that is `ctx_terminating` and
`ctx_confluent`.
Relation: `RootStep` on `FreeTerm ν`.
Closure: root.
Strategy: termination from the contextual closure; confluence from determinism of the root
relation.
Trust: Lean kernel with the axioms of `main_free_root_termination`.
Scope: every variable type `ν`.
-/
theorem root_terminating_confluent :
    WellFounded (fun u t : FreeTerm ν => RootStep t u) ∧
      ∀ {a b c : FreeTerm ν}, Relation.ReflTransGen RootStep a b →
        Relation.ReflTransGen RootStep a c →
          ∃ d, Relation.ReflTransGen RootStep b d ∧ Relation.ReflTransGen RootStep c d := by
  refine ⟨main_free_root_termination ν, fun hb hc => ?_⟩
  rcases root_star_total hb hc with h | h
  · exact ⟨_, h, .refl⟩
  · exact ⟨_, .refl, h⟩

theorem rootNormalize_star_eq {a b : FreeTerm ν} (h : Relation.ReflTransGen RootStep a b) :
    rootNormalize a = rootNormalize b := by
  rcases root_star_total (rootNormalize_reachable a) (h.trans (rootNormalize_reachable b))
    with h1 | h1
  · exact root_normal_star_eq (rootNormalize_normal a) h1
  · exact (root_normal_star_eq (rootNormalize_normal b) h1).symm

/--
Proves: two terms with variables are root-joinable exactly when their root normal forms agree.
Does not prove: anything about contextual joinability; that is `ctx_joinable_iff`.
Relation: `RootStep` on `FreeTerm ν`.
Closure: root.
Strategy: invariance of `rootNormalize` along root paths and its reachability.
Trust: Lean kernel.
Scope: every variable type `ν`, every pair of terms.
-/
theorem root_joinable_iff (a b : FreeTerm ν) :
    (∃ d, Relation.ReflTransGen RootStep a d ∧ Relation.ReflTransGen RootStep b d) ↔
      rootNormalize a = rootNormalize b := by
  constructor
  · rintro ⟨d, ha, hb⟩
    exact (rootNormalize_star_eq ha).trans (rootNormalize_star_eq hb).symm
  · intro he
    refine ⟨rootNormalize b, ?_, rootNormalize_reachable b⟩
    rw [← he]
    exact rootNormalize_reachable a

/--
Proves: Theorem 5.14 of the Orientation Boundary paper on the free recursor terms with variables
in any type: root and contextual rewriting terminate and are confluent; `normalize` and
`rootNormalize` are computable normal-form functions; two terms are joinable exactly when the
corresponding normal forms agree.
Does not prove: anything about extensions of the two rules.
Relation: `RootStep` and `ContextStep` on `FreeTerm ν`.
Closure: root, and every one-hole constructor context.
Strategy: the coupled polynomial interpretation for termination; computed normal forms for
confluence.
Trust: Lean kernel with the axioms of the two termination theorems.
Scope: every variable type `ν`.
-/
theorem free_term_normalization :
    WellFounded (fun u t : FreeTerm ν => RootStep t u) ∧
      WellFounded (fun u t : FreeTerm ν => ContextStep t u) ∧
      (∀ {a b c : FreeTerm ν}, Relation.ReflTransGen RootStep a b →
        Relation.ReflTransGen RootStep a c →
          ∃ d, Relation.ReflTransGen RootStep b d ∧ Relation.ReflTransGen RootStep c d) ∧
      (∀ {a b c : FreeTerm ν}, Relation.ReflTransGen ContextStep a b →
        Relation.ReflTransGen ContextStep a c →
          ∃ d, Relation.ReflTransGen ContextStep b d ∧ Relation.ReflTransGen ContextStep c d) ∧
      (∀ t : FreeTerm ν, Relation.ReflTransGen ContextStep t (normalize t) ∧
        ∀ u, ¬ ContextStep (normalize t) u) ∧
      (∀ t : FreeTerm ν, Relation.ReflTransGen RootStep t (rootNormalize t) ∧
        ∀ u, ¬ RootStep (rootNormalize t) u) ∧
      (∀ a b : FreeTerm ν,
        (∃ d, Relation.ReflTransGen ContextStep a d ∧ Relation.ReflTransGen ContextStep b d) ↔
          normalize a = normalize b) ∧
      (∀ a b : FreeTerm ν,
        (∃ d, Relation.ReflTransGen RootStep a d ∧ Relation.ReflTransGen RootStep b d) ↔
          rootNormalize a = rootNormalize b) :=
  ⟨root_terminating_confluent.1, ctx_terminating, root_terminating_confluent.2,
    ctx_confluent, ctx_normalization_certificate,
    fun t => ⟨rootNormalize_reachable t, rootNormalize_normal t⟩,
    ctx_joinable_iff, root_joinable_iff⟩

end OperatorKO7.Methods.OrientationClosure.AuditUpgrades.FreeTermNormalization
