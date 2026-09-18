import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel

/-! # Contextual termination, normalization, and confluence of the two-rule recursor -/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorContext

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel

/-- All one-hole contexts of the seven-constructor free syntax. -/
inductive Context where
  | hole
  | delta (C : Context)
  | integrate (C : Context)
  | mergeLeft (C : Context) (b : RecursorTerm)
  | mergeRight (a : RecursorTerm) (C : Context)
  | appLeft (C : Context) (b : RecursorTerm)
  | appRight (a : RecursorTerm) (C : Context)
  | eqLeft (C : Context) (b : RecursorTerm)
  | eqRight (a : RecursorTerm) (C : Context)
  | recBase (C : Context) (s n : RecursorTerm)
  | recPayload (b : RecursorTerm) (C : Context) (n : RecursorTerm)
  | recCounter (b s : RecursorTerm) (C : Context)

def Context.fill : Context → RecursorTerm → RecursorTerm
  | .hole, t => t
  | .delta C, t => .delta (C.fill t)
  | .integrate C, t => .integrate (C.fill t)
  | .mergeLeft C b, t => .merge (C.fill t) b
  | .mergeRight a C, t => .merge a (C.fill t)
  | .appLeft C b, t => .app (C.fill t) b
  | .appRight a C, t => .app a (C.fill t)
  | .eqLeft C b, t => .eqWit (C.fill t) b
  | .eqRight a C, t => .eqWit a (C.fill t)
  | .recBase C s n, t => .recR (C.fill t) s n
  | .recPayload b C n, t => .recR b (C.fill t) n
  | .recCounter b s C, t => .recR b s (C.fill t)

def Context.comp : Context → Context → Context
  | .hole, D => D
  | .delta C, D => .delta (C.comp D)
  | .integrate C, D => .integrate (C.comp D)
  | .mergeLeft C b, D => .mergeLeft (C.comp D) b
  | .mergeRight a C, D => .mergeRight a (C.comp D)
  | .appLeft C b, D => .appLeft (C.comp D) b
  | .appRight a C, D => .appRight a (C.comp D)
  | .eqLeft C b, D => .eqLeft (C.comp D) b
  | .eqRight a C, D => .eqRight a (C.comp D)
  | .recBase C s n, D => .recBase (C.comp D) s n
  | .recPayload b C n, D => .recPayload b (C.comp D) n
  | .recCounter b s C, D => .recCounter b s (C.comp D)

theorem Context.fill_comp (C D : Context) (t : RecursorTerm) :
    (C.comp D).fill t = C.fill (D.fill t) := by
  induction C <;> simp only [Context.comp, Context.fill, *]

theorem Context.weight_strict {a b : RecursorTerm} (C : Context)
    (h : rootWeight a < rootWeight b) : rootWeight (C.fill a) < rootWeight (C.fill b) := by
  induction C <;> simp only [Context.fill, rootWeight] at * <;> first | assumption | omega | nlinarith

/-- One free root contraction at any context position. -/
inductive Step : RecursorTerm → RecursorTerm → Prop
  | inContext (C : Context) {a b : RecursorTerm} (h : FreeRecursorStep a b) :
      Step (C.fill a) (C.fill b)

theorem root_step {a b : RecursorTerm} (h : FreeRecursorStep a b) : Step a b :=
  .inContext .hole h

theorem step_in_context {a b : RecursorTerm} (h : Step a b) (C : Context) :
    Step (C.fill a) (C.fill b) := by
  cases h with
  | inContext D hs => simpa only [Context.fill_comp] using Step.inContext (C.comp D) hs

theorem star_in_context {a b : RecursorTerm}
    (h : Relation.ReflTransGen Step a b) (C : Context) :
    Relation.ReflTransGen Step (C.fill a) (C.fill b) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (step_in_context hs C)

theorem rootWeight_context_decreases {a b : RecursorTerm} (h : Step a b) :
    rootWeight b < rootWeight a := by
  cases h with
  | inContext C hs => exact C.weight_strict (rootWeight_decreases hs)

theorem freeRecursor_ctx_rev_wellFounded : WellFounded (fun a b => Step b a) :=
  Subrelation.wf (fun h => rootWeight_context_decreases h) (measure rootWeight).wf

theorem rootWeight_star_le {a b : RecursorTerm} (h : Relation.ReflTransGen Step a b) :
    rootWeight b ≤ rootWeight a := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (Nat.le_of_lt (rootWeight_context_decreases hs)).trans ih

/-- Evaluate the counter once the three arguments have been normalized. -/
def recNormal (b s : RecursorTerm) : RecursorTerm → RecursorTerm
  | .void => b
  | .delta n => .app s (recNormal b s n)
  | n => .recR b s n

def normalize : RecursorTerm → RecursorTerm
  | .void => .void
  | .delta t => .delta (normalize t)
  | .integrate t => .integrate (normalize t)
  | .merge a b => .merge (normalize a) (normalize b)
  | .app a b => .app (normalize a) (normalize b)
  | .eqWit a b => .eqWit (normalize a) (normalize b)
  | .recR b s n => recNormal (normalize b) (normalize s) (normalize n)

theorem normalize_recNormal (b s n : RecursorTerm) :
    normalize (recNormal b s n) = recNormal (normalize b) (normalize s) (normalize n) := by
  induction n with
  | delta n ih => simp only [recNormal, normalize, ih]
  | _ => rfl

theorem normalize_idempotent (t : RecursorTerm) : normalize (normalize t) = normalize t := by
  induction t <;> simp only [normalize, normalize_recNormal, *]

theorem normalize_context_congr {a b : RecursorTerm} (C : Context)
    (h : normalize a = normalize b) : normalize (C.fill a) = normalize (C.fill b) := by
  induction C <;> simp only [Context.fill, normalize, *]

theorem normalize_root_step {a b : RecursorTerm} (h : FreeRecursorStep a b) :
    normalize a = normalize b := by
  cases h <;> rfl

theorem normalize_step {a b : RecursorTerm} (h : Step a b) : normalize a = normalize b := by
  cases h with
  | inContext C hs => exact normalize_context_congr C (normalize_root_step hs)

theorem normalize_star {a b : RecursorTerm} (h : Relation.ReflTransGen Step a b) :
    normalize a = normalize b := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (normalize_step hs)

theorem recNormal_reachable (b s n : RecursorTerm) :
    Relation.ReflTransGen Step (.recR b s n) (recNormal b s n) := by
  induction n with
  | void => exact .single (root_step (.zero b s))
  | delta n ih =>
      exact (Relation.ReflTransGen.single (root_step (.succ b s n))).trans
        (star_in_context ih (.appRight s .hole))
  | _ => exact .refl

theorem normalize_reachable (t : RecursorTerm) : Relation.ReflTransGen Step t (normalize t) := by
  induction t with
  | void => exact .refl
  | delta t ih => exact star_in_context ih (.delta .hole)
  | integrate t ih => exact star_in_context ih (.integrate .hole)
  | merge a b ha hb =>
      exact (star_in_context ha (.mergeLeft .hole b)).trans
        (star_in_context hb (.mergeRight (normalize a) .hole))
  | app a b ha hb =>
      exact (star_in_context ha (.appLeft .hole b)).trans
        (star_in_context hb (.appRight (normalize a) .hole))
  | eqWit a b ha hb =>
      exact (star_in_context ha (.eqLeft .hole b)).trans
        (star_in_context hb (.eqRight (normalize a) .hole))
  | recR b s n hb hs hn =>
      exact (star_in_context hb (.recBase .hole s n)).trans
        ((star_in_context hs (.recPayload (normalize b) .hole n)).trans
          ((star_in_context hn (.recCounter (normalize b) (normalize s) .hole)).trans
            (recNormal_reachable (normalize b) (normalize s) (normalize n))))

theorem normalize_normal (t : RecursorTerm) : ∀ u, ¬ Step (normalize t) u := by
  intro u hu
  have hd := rootWeight_context_decreases hu
  have hn := rootWeight_star_le (normalize_reachable u)
  have he := normalize_step hu
  rw [normalize_idempotent] at he
  rw [← he] at hn
  omega

theorem freeRecursor_ctx_confluent {a b c : RecursorTerm}
    (hb : Relation.ReflTransGen Step a b) (hc : Relation.ReflTransGen Step a c) :
    ∃ d, Relation.ReflTransGen Step b d ∧ Relation.ReflTransGen Step c d := by
  refine ⟨normalize a, ?_, ?_⟩
  · rw [normalize_star hb]
    exact normalize_reachable b
  · rw [normalize_star hc]
    exact normalize_reachable c

theorem freeRecursor_ctx_unique_normal_form {a b : RecursorTerm}
    (h : Relation.ReflTransGen Step a b) (hb : ∀ u, ¬ Step b u) : b = normalize a := by
  have hrefl : ∀ {u}, Relation.ReflTransGen Step b u → b = u := by
    intro u hu
    cases hu using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hs _ _ => exact (hb _ hs).elim
  exact (hrefl (normalize_reachable b)).trans (normalize_star h).symm

theorem freeRecursor_ctx_normalization_certificate (t : RecursorTerm) :
    Relation.ReflTransGen Step t (normalize t) ∧ (∀ u, ¬ Step (normalize t) u) :=
  ⟨normalize_reachable t, normalize_normal t⟩

theorem freeRecursor_ctx_normal_iff_fixed (t : RecursorTerm) :
    (∀ u, ¬ Step t u) ↔ normalize t = t := by
  constructor
  · intro hn
    exact (freeRecursor_ctx_unique_normal_form .refl hn).symm
  · intro he
    rw [← he]
    exact normalize_normal t

theorem freeRecursor_ctx_joinable_iff (a b : RecursorTerm) :
    (∃ d, Relation.ReflTransGen Step a d ∧ Relation.ReflTransGen Step b d) ↔
      normalize a = normalize b := by
  constructor
  · rintro ⟨d, ha, hb⟩
    exact (normalize_star ha).trans (normalize_star hb).symm
  · intro he
    refine ⟨normalize b, ?_, normalize_reachable b⟩
    rw [← he]
    exact normalize_reachable a

/-- Compare the two computed normal forms. -/
def joinableDecision (a b : RecursorTerm) :
    Decidable (∃ d, Relation.ReflTransGen Step a d ∧ Relation.ReflTransGen Step b d) :=
  if h : normalize a = normalize b then
    isTrue ((freeRecursor_ctx_joinable_iff a b).mpr h)
  else isFalse (fun hj => h ((freeRecursor_ctx_joinable_iff a b).mp hj))

def joinable? (a b : RecursorTerm) : Bool := decide (normalize a = normalize b)

theorem joinable?_eq_true_iff (a b : RecursorTerm) :
    joinable? a b = true ↔
      ∃ d, Relation.ReflTransGen Step a d ∧ Relation.ReflTransGen Step b d := by
  simp only [joinable?, decide_eq_true_eq, freeRecursor_ctx_joinable_iff]

theorem contextual_step_not_root_step :
    Step (.app .void (.recR .void .void .void)) (.app .void .void) ∧
      ¬ FreeRecursorStep (.app .void (.recR .void .void .void)) (.app .void .void) := by
  refine ⟨Step.inContext (.appRight .void .hole) (.zero .void .void), ?_⟩
  intro h
  cases h

end OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorContext
