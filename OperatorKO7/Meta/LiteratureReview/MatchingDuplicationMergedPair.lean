import Mathlib
import OperatorKO7.Meta.SafeStep.NonlinearityDichotomy
import OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance

namespace OperatorKO7.Meta.LiteratureReview

/-!
The manuscript label prop:matching-duplication, obligation 07A-032,
states that the role bijection uniquely identifies matching and duplication
occurrences, preserves their content and place kernels and separating fiber
records, extends to the literal copied subtrees, and identifies the positional
dependency-pair flag as a separator independent of their common content.
The construction retains arbitrary content and side-record types.
The Boolean disequality test concerns content; the kernel Step relation
retains its existing unconditional rules.
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.NonlinearityDichotomy
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance

inductive EqPlace
  | left
  | right
  deriving DecidableEq

def placeEquiv : EqPlace ≃ Role :=
  { toFun := fun r => match r with
      | .left => .frame
      | .right => .active
    invFun := fun r => match r with
      | .frame => .left
      | .active => .right
    left_inv := by intro r; cases r <;> rfl
    right_inv := by intro r; cases r <;> rfl }

def copyIso (Y : Type*) : (Y × EqPlace) ≃ Occ Y :=
  Equiv.prodCongr (Equiv.refl Y) placeEquiv

theorem copyIso_observers {Y : Type*} (o : Y × EqPlace) :
    (copyIso Y o).1 = o.1 ∧
      (copyIso Y o).2 = placeEquiv o.2 :=
  ⟨rfl, rfl⟩

theorem copyIso_bijective (Y : Type*) :
    Function.Bijective (copyIso Y) :=
  (copyIso Y).bijective

theorem copyIso_unique {Y : Type*} (f : (Y × EqPlace) → Occ Y)
    (hc : ∀ o, (f o).1 = o.1)
    (hp : ∀ o, (f o).2 = placeEquiv o.2) :
    f = fun o => copyIso Y o := by
  funext o
  apply Prod.ext
  · exact hc o
  · exact hp o

theorem copyIso_unique_map (Y : Type*) :
    ∃! f : (Y × EqPlace) → Occ Y,
      (∀ o, (f o).1 = o.1) ∧
        (∀ o, (f o).2 = placeEquiv o.2) :=
  ⟨fun o => copyIso Y o, ⟨fun _ => rfl, fun _ => rfl⟩,
    fun f hf => copyIso_unique f hf.1 hf.2⟩

theorem copyIso_observer_kernels {Y : Type*} (o o' : Y × EqPlace) :
    ((copyIso Y o).1 = (copyIso Y o').1 ↔ o.1 = o'.1) ∧
      ((copyIso Y o).2 = (copyIso Y o').2 ↔ o.2 = o'.2) := by
  constructor
  · rfl
  · constructor
    · intro h
      exact placeEquiv.injective h
    · intro h
      exact congrArg placeEquiv h

theorem merged_copy_pairs {Y : Type*} (y : Y) :
    ((y, EqPlace.left) : Y × EqPlace).1 =
        ((y, EqPlace.right) : Y × EqPlace).1 ∧
    ((y, EqPlace.left) : Y × EqPlace) ≠ (y, EqPlace.right) ∧
    ((y, Role.frame) : Occ Y).1 = ((y, Role.active) : Occ Y).1 ∧
    ((y, Role.frame) : Occ Y) ≠ (y, Role.active) := by
  simp

/-- Separation means injectivity of the record on the fixed content fiber. -/
def SeparatesOnContentFiber {Y P C : Type*} (y : Y)
    (s : (Y × P) → C) : Prop :=
  Function.Injective (fun r : P => s (y, r))

def transportSideRecord {Y C : Type*} (s : (Y × EqPlace) → C) :
    Occ Y → C :=
  fun o => s ((copyIso Y).symm o)

theorem transportSideRecord_copyIso {Y C : Type*}
    (s : (Y × EqPlace) → C) (o : Y × EqPlace) :
    transportSideRecord s (copyIso Y o) = s o := by
  exact congrArg s ((copyIso Y).symm_apply_apply o)

theorem transportSideRecord_unique {Y C : Type*}
    (s : (Y × EqPlace) → C) (t : Occ Y → C)
    (ht : ∀ o, t (copyIso Y o) = s o) :
    t = transportSideRecord s := by
  funext o
  simpa [transportSideRecord] using ht ((copyIso Y).symm o)

theorem transport_separating_side_record {Y C : Type*} (y : Y)
    (s : (Y × EqPlace) → C) :
    SeparatesOnContentFiber y (transportSideRecord s) ↔
      SeparatesOnContentFiber y s := by
  constructor
  · intro hs r r' hrr'
    have hv :
        transportSideRecord s (copyIso Y (y, r)) =
          transportSideRecord s (copyIso Y (y, r')) := by
      rw [transportSideRecord_copyIso, transportSideRecord_copyIso]
      exact hrr'
    have hr : placeEquiv r = placeEquiv r' := hs hv
    exact placeEquiv.injective hr
  · intro hs r r' hrr'
    apply placeEquiv.symm.injective
    apply hs
    exact hrr'

theorem transport_fiber_record {C : Type*} (s : EqPlace → C) :
    Function.Injective (fun r : Role => s (placeEquiv.symm r)) ↔
      Function.Injective s :=
  transport_separating_side_record () (fun o : Unit × EqPlace => s o.2)

def eqPath : EqPlace → List Nat
  | .left => [0]
  | .right => [1]

def recPath : Role → List Nat
  | .frame => [0]
  | .active => [1, 1]

def traceChildren : Trace → List Trace
  | .void => []
  | .delta t => [t]
  | .integrate t => [t]
  | .merge a b => [a, b]
  | .app a b => [a, b]
  | .eqW a b => [a, b]
  | .recΔ b s n => [b, s, n]

def listAt {α : Type*} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => listAt xs i

def traceAt : Trace → List Nat → Option Trace
  | t, [] => some t
  | t, i :: p =>
    match listAt (traceChildren t) i with
    | none => none
    | some u => traceAt u p

def inCalleeSubtree : List Nat → Bool
  | 1 :: _ => true
  | _ => false

theorem exact_source_counts :
    occ .a eqwReflLhs = 2 ∧
      occ .s recdSuccLhs = 1 ∧ occ .s recdSuccRhs = 2 := by
  simp [occ, eqwReflLhs, recdSuccLhs, recdSuccRhs]

theorem source_rule_instances (b u n : Trace) :
    Step (eqW u u) void ∧
      Step (recΔ b u (delta n)) (app u (recΔ b u n)) :=
  ⟨Step.R_eq_refl u, Step.R_rec_succ b u n⟩

theorem literal_copy_roots (b u n : Trace) :
    traceAt (eqW u u) [0] = some u ∧
    traceAt (eqW u u) [1] = some u ∧
    traceAt (app u (recΔ b u n)) [0] = some u ∧
    traceAt (app u (recΔ b u n)) [1, 1] = some u := by
  simp [traceAt, traceChildren, listAt]

theorem literal_copy_subtrees (b u n : Trace)
    (r : EqPlace) (p : List Nat) :
    traceAt (eqW u u) (eqPath r ++ p) = traceAt u p ∧
      traceAt (app u (recΔ b u n))
        (recPath (placeEquiv r) ++ p) = traceAt u p := by
  cases r <;> simp [eqPath, recPath, placeEquiv, traceAt, traceChildren, listAt]

theorem copy_path_injective :
    Function.Injective
      (fun q : EqPlace × List Nat => eqPath q.1 ++ q.2) ∧
    Function.Injective
      (fun q : Role × List Nat => recPath q.1 ++ q.2) := by
  constructor
  · rintro ⟨r, p⟩ ⟨s, q⟩ h
    cases r <;> cases s <;> simp_all [eqPath]
  · rintro ⟨r, p⟩ ⟨s, q⟩ h
    cases r <;> cases s <;> simp_all [recPath]

def subtreeCopyIso : (EqPlace × List Nat) ≃ (Role × List Nat) :=
  Equiv.prodCongr placeEquiv (Equiv.refl (List Nat))

theorem subtree_copy_preserves_subterm (b u n : Trace)
    (q : EqPlace × List Nat) :
    traceAt (eqW u u) (eqPath q.1 ++ q.2) =
      traceAt (app u (recΔ b u n))
        (recPath (subtreeCopyIso q).1 ++ (subtreeCopyIso q).2) := by
  have h := literal_copy_subtrees b u n q.1 q.2
  exact h.1.trans h.2.symm

theorem positional_dp_bridge (b u n : Trace) (r : Role) :
    inCalleeSubtree (recPath r) =
      actualDPChannel b u n (((), r) : Occ Unit) := by
  cases r <;>
    simp [inCalleeSubtree, recPath, actualDPChannel, encodedTerm,
      extractRecSuccDP, step_ne_extracted b u n]

theorem positional_dp_bridge_subtrees (b u n : Trace)
    (r : Role) (p : List Nat) :
    inCalleeSubtree (recPath r ++ p) =
      actualDPChannel b u n (((), r) : Occ Unit) := by
  cases r <;>
    simp [inCalleeSubtree, recPath, actualDPChannel, encodedTerm,
      extractRecSuccDP, step_ne_extracted b u n]

theorem payload_role_not_content_factored (u : Trace) :
    ¬ ∃ g : Trace → Bool, ∀ r : Role,
      inCalleeSubtree (recPath r) = g u := by
  rintro ⟨g, hg⟩
  have hf : false = g u := hg Role.frame
  have ha : true = g u := hg Role.active
  have h : false = true := hf.trans ha.symm
  cases h

theorem actual_dp_not_payload_factored (b u n : Trace) :
    ¬ ∃ g : Trace → Bool, ∀ r : Role,
      actualDPChannel b u n (((), r) : Occ Unit) = g u := by
  rintro ⟨g, hg⟩
  apply payload_role_not_content_factored u
  exact ⟨g, fun r => (positional_dp_bridge b u n r).trans (hg r)⟩

noncomputable def contentDisequality {Y P : Type*}
    (o o' : Y × P) : Bool := by
  classical
  exact decide (o.1 ≠ o'.1)

theorem disequality_guard_constant_on_fiber {Y P : Type*}
    (y : Y) (r s : P) :
    contentDisequality (y, r) (y, s) = false := by
  classical
  simp [contentDisequality]

theorem disequality_guard_on_both_pairs {Y : Type*} (y : Y) :
    contentDisequality ((y, EqPlace.left) : Y × EqPlace)
        (y, EqPlace.right) = false ∧
      contentDisequality ((y, Role.frame) : Occ Y)
        (y, Role.active) = false :=
  ⟨disequality_guard_constant_on_fiber y EqPlace.left EqPlace.right,
    disequality_guard_constant_on_fiber y Role.frame Role.active⟩

theorem matching_duplication (Y C : Type*) (b u n : Trace) :
    Function.Bijective (copyIso Y) ∧
    (∀ o : Y × EqPlace,
      (copyIso Y o).1 = o.1 ∧
        (copyIso Y o).2 = placeEquiv o.2) ∧
    (∃! f : (Y × EqPlace) → Occ Y,
      (∀ o, (f o).1 = o.1) ∧
        (∀ o, (f o).2 = placeEquiv o.2)) ∧
    (∀ o o' : Y × EqPlace,
      ((copyIso Y o).1 = (copyIso Y o').1 ↔ o.1 = o'.1) ∧
        ((copyIso Y o).2 = (copyIso Y o').2 ↔ o.2 = o'.2)) ∧
    (∀ (y : Y) (s : (Y × EqPlace) → C),
      SeparatesOnContentFiber y (transportSideRecord s) ↔
        SeparatesOnContentFiber y s) ∧
    (occ .a eqwReflLhs = 2 ∧
      occ .s recdSuccLhs = 1 ∧ occ .s recdSuccRhs = 2) ∧
    (Step (eqW u u) void ∧
      Step (recΔ b u (delta n)) (app u (recΔ b u n))) ∧
    (∀ (r : EqPlace) (p : List Nat),
      traceAt (eqW u u) (eqPath r ++ p) = traceAt u p ∧
        traceAt (app u (recΔ b u n))
          (recPath (placeEquiv r) ++ p) = traceAt u p) ∧
    (Function.Injective
      (fun q : EqPlace × List Nat => eqPath q.1 ++ q.2) ∧
      Function.Injective
        (fun q : Role × List Nat => recPath q.1 ++ q.2)) ∧
    (∀ r : Role, inCalleeSubtree (recPath r) =
      actualDPChannel b u n (((), r) : Occ Unit)) ∧
    (¬ ∃ g : Trace → Bool, ∀ r : Role,
      inCalleeSubtree (recPath r) = g u) ∧
    (contentDisequality ((u, EqPlace.left) : Trace × EqPlace)
        (u, EqPlace.right) = false ∧
      contentDisequality ((u, Role.frame) : Occ Trace)
        (u, Role.active) = false) := by
  exact ⟨copyIso_bijective Y, copyIso_observers, copyIso_unique_map Y,
    copyIso_observer_kernels, transport_separating_side_record,
    exact_source_counts, source_rule_instances b u n,
    literal_copy_subtrees b u n, copy_path_injective,
    positional_dp_bridge b u n, payload_role_not_content_factored u,
    disequality_guard_on_both_pairs u⟩

end OperatorKO7.Meta.LiteratureReview
