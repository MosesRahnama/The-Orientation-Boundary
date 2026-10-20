import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorContext
import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorRoleGate
import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder
import OperatorKO7.Meta.OperationalInexpressibility.ProgressOrbitEquivalence
import OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile
import OperatorKO7.Meta.DependencyPairs_Works

/-!
# Faithful realizations of the free recursor

A signature algebra realizes the seven constructors through its injective fold.
Root steps, transformed calls and contextual steps are images of the corresponding
free relations. Results for another ambient relation require both reflection and
closure under outgoing steps. No termination or confluence theorem is a field.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.OperationalInexpressibility.BinaryForkExactProfile
open OperatorKO7.Meta.OperationalInexpressibility.ProgressOrbitEquivalence
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorRoleGate
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.Rewriting

universe u v w

variable {X : Type u} {Y : Type v}

/-- The interpretation is the constructor fold, not an unrelated carrier map. -/
structure FaithfulRealization (X : Type u) where
  algebra : SigmaAlgebra X
  injective : Function.Injective (RecursorTerm.fold algebra)

namespace FaithfulRealization

def encode (e : FaithfulRealization X) : RecursorTerm → X := RecursorTerm.fold e.algebra

theorem encode_injective (e : FaithfulRealization X) : Function.Injective e.encode :=
  e.injective

theorem encode_hom (e : FaithfulRealization X) : IsSigmaHomomorphism e.encode e.algebra :=
  RecursorTerm.fold_isSigmaHomomorphism e.algebra

def State (e : FaithfulRealization X) := Set.range e.encode

def point (e : FaithfulRealization X) (t : RecursorTerm) : e.State :=
  ⟨e.encode t, t, rfl⟩

noncomputable def equiv (e : FaithfulRealization X) : RecursorTerm ≃ e.State :=
  Equiv.ofInjective e.encode e.injective

noncomputable def decode (e : FaithfulRealization X) : e.State → RecursorTerm := e.equiv.symm

@[simp] theorem decode_point (e : FaithfulRealization X) (t : RecursorTerm) :
    e.decode (e.point t) = t := e.equiv.left_inv t

@[simp] theorem point_decode (e : FaithfulRealization X) (x : e.State) :
    e.point (e.decode x) = x := e.equiv.right_inv x

@[simp] theorem encode_decode (e : FaithfulRealization X) (x : e.State) :
    e.encode (e.decode x) = x.val := congrArg Subtype.val (e.point_decode x)

/-- Only represented endpoints have generated edges; extra ambient edges are separate. -/
def Realized (e : FaithfulRealization X) (R : RecursorTerm → RecursorTerm → Prop)
    (x y : X) : Prop := ∃ a b, R a b ∧ e.encode a = x ∧ e.encode b = y

theorem realized_iff (e : FaithfulRealization X) (R : RecursorTerm → RecursorTerm → Prop)
    (a b : RecursorTerm) : e.Realized R (e.encode a) (e.encode b) ↔ R a b := by
  constructor
  · rintro ⟨c, d, h, hc, hd⟩
    exact e.injective hc ▸ e.injective hd ▸ h
  · intro h
    exact ⟨a, b, h, rfl, rfl⟩

theorem realized_state_iff (e : FaithfulRealization X)
    (R : RecursorTerm → RecursorTerm → Prop) (x y : e.State) :
    e.Realized R x.val y.val ↔ R (e.decode x) (e.decode y) := by
  rw [← e.encode_decode x, ← e.encode_decode y]
  exact e.realized_iff R _ _

def closedEmbedding (e : FaithfulRealization X) (R : RecursorTerm → RecursorTerm → Prop) :
    ClosedRelationEmbedding R (e.Realized R) where
  map := ⟨e.encode, e.injective⟩
  step_iff := (e.realized_iff R _ _).symm
  forward_closed := by
    rintro x y ⟨a, b, _, _, hb⟩
    exact ⟨b, hb⟩

noncomputable def relationIso (e : FaithfulRealization X)
    (R : RecursorTerm → RecursorTerm → Prop) :
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso R
      (fun x y : e.State => e.Realized R x.val y.val) where
  toEquiv := e.equiv
  map_rel_iff := (e.realized_iff R _ _).symm

def Root (e : FaithfulRealization X) := e.Realized FreeRecursorStep
def DP (e : FaithfulRealization X) := e.Realized FreeRecursorDPPair
def Contextual (e : FaithfulRealization X) := e.Realized FreeRecursorContext.Step

/-- Contexts use the actual algebra operations and represented fixed siblings. -/
def contextEval (e : FaithfulRealization X) : FreeRecursorContext.Context → X → X
  | .hole, x => x
  | .delta C, x => e.algebra.delta (e.contextEval C x)
  | .integrate C, x => e.algebra.integrate (e.contextEval C x)
  | .mergeLeft C b, x => e.algebra.merge (e.contextEval C x) (e.encode b)
  | .mergeRight a C, x => e.algebra.merge (e.encode a) (e.contextEval C x)
  | .appLeft C b, x => e.algebra.app (e.contextEval C x) (e.encode b)
  | .appRight a C, x => e.algebra.app (e.encode a) (e.contextEval C x)
  | .eqLeft C b, x => e.algebra.eqWit (e.contextEval C x) (e.encode b)
  | .eqRight a C, x => e.algebra.eqWit (e.encode a) (e.contextEval C x)
  | .recBase C s n, x => e.algebra.recR (e.contextEval C x) (e.encode s) (e.encode n)
  | .recPayload b C n, x => e.algebra.recR (e.encode b) (e.contextEval C x) (e.encode n)
  | .recCounter b s C, x => e.algebra.recR (e.encode b) (e.encode s) (e.contextEval C x)

theorem contextEval_encode (e : FaithfulRealization X) (C : FreeRecursorContext.Context)
    (a : RecursorTerm) : e.contextEval C (e.encode a) = e.encode (C.fill a) := by
  induction C <;> simp_all only [contextEval, FreeRecursorContext.Context.fill,
    encode, RecursorTerm.fold]

theorem contextual_iff_context_contraction (e : FaithfulRealization X) (x y : X) :
    e.Contextual x y ↔ ∃ C a b, e.Root a b ∧
      e.contextEval C a = x ∧ e.contextEval C b = y := by
  constructor
  · rintro ⟨a, b, h, rfl, rfl⟩
    cases h with
    | inContext C hs =>
        exact ⟨C, _, _, ⟨_, _, hs, rfl, rfl⟩, e.contextEval_encode _ _, e.contextEval_encode _ _⟩
  · rintro ⟨C, a, b, ⟨a', b', h, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨C.fill a', C.fill b', .inContext C h,
      (e.contextEval_encode _ _).symm, (e.contextEval_encode _ _).symm⟩

theorem freeRecursor_step_iff_realized_step (e : FaithfulRealization X) (a b : RecursorTerm) :
    FreeRecursorStep a b ↔ e.Root (e.encode a) (e.encode b) :=
  (e.realized_iff _ a b).symm

theorem freeRecursor_dp_iff_realized_dp (e : FaithfulRealization X) (a b : RecursorTerm) :
    FreeRecursorDPPair a b ↔ e.DP (e.encode a) (e.encode b) :=
  (e.realized_iff _ a b).symm

theorem freeRecursor_context_iff_realized_context (e : FaithfulRealization X)
    (a b : RecursorTerm) :
    FreeRecursorContext.Step a b ↔ e.Contextual (e.encode a) (e.encode b) :=
  (e.realized_iff _ a b).symm

end FaithfulRealization

section GeneralTransport

variable {R : X → X → Prop} {S : Y → Y → Prop}

theorem closedEmbedding_acc (e : ClosedRelationEmbedding R S) {x : X}
    (h : Acc (fun b a => R a b) x) : Acc (fun b a => S a b) (e.map x) := by
  induction h with
  | intro x hx ih =>
      apply Acc.intro
      intro y hy
      obtain ⟨z, rfl⟩ := e.forward_closed hy
      exact ih z (e.step_iff.mpr hy)

theorem closedEmbedding_acc_reflect (e : ClosedRelationEmbedding R S) {x : X}
    (h : Acc (fun b a => S a b) (e.map x)) : Acc (fun b a => R a b) x := by
  have pull : ∀ y, Acc (fun b a => S a b) y →
      ∀ z, e.map z = y → Acc (fun b a => R a b) z := by
    intro y hy
    induction hy with
    | intro y hy ih =>
        intro z hz
        apply Acc.intro
        intro t ht
        exact ih (e.map t) (hz ▸ e.step_iff.mp ht) t rfl
  exact pull _ h x rfl

theorem closedEmbedding_acc_iff (e : ClosedRelationEmbedding R S) (x : X) :
    Acc (fun b a => R a b) x ↔ Acc (fun b a => S a b) (e.map x) :=
  ⟨closedEmbedding_acc e, closedEmbedding_acc_reflect e⟩

theorem closedEmbedding_star_map (e : ClosedRelationEmbedding R S) {x y : X}
    (h : Relation.ReflTransGen R x y) : Relation.ReflTransGen S (e.map x) (e.map y) := by
  induction h with
  | refl => exact .refl
  | tail h hs ih => exact ih.tail (e.step_iff.mp hs)

theorem closedEmbedding_star_pull (e : ClosedRelationEmbedding R S) {x : X} {y : Y}
    (h : Relation.ReflTransGen S (e.map x) y) :
    ∃ z, e.map z = y ∧ Relation.ReflTransGen R x z := by
  induction h with
  | refl => exact ⟨x, rfl, .refl⟩
  | tail h hs ih =>
      obtain ⟨a, rfl, ha⟩ := ih
      obtain ⟨b, rfl⟩ := e.forward_closed hs
      exact ⟨b, rfl, ha.tail (e.step_iff.mpr hs)⟩

theorem closedEmbedding_confluent_at (e : ClosedRelationEmbedding R S)
    (hc : ∀ {x a b}, Relation.ReflTransGen R x a → Relation.ReflTransGen R x b →
      ∃ z, Relation.ReflTransGen R a z ∧ Relation.ReflTransGen R b z)
    {x : X} {a b : Y} (ha : Relation.ReflTransGen S (e.map x) a)
    (hb : Relation.ReflTransGen S (e.map x) b) :
    ∃ z, Relation.ReflTransGen S a z ∧ Relation.ReflTransGen S b z := by
  obtain ⟨a', rfl, ha'⟩ := closedEmbedding_star_pull e ha
  obtain ⟨b', rfl, hb'⟩ := closedEmbedding_star_pull e hb
  obtain ⟨z, haz, hbz⟩ := hc ha' hb'
  exact ⟨e.map z, closedEmbedding_star_map e haz, closedEmbedding_star_map e hbz⟩

end GeneralTransport

namespace FaithfulRealization

theorem realized_wellFounded (e : FaithfulRealization X)
    (R : RecursorTerm → RecursorTerm → Prop) (h : WellFounded (fun b a => R a b)) :
    WellFounded (fun b a => e.Realized R a b) := by
  constructor
  intro x
  classical
  by_cases hx : ∃ a, e.encode a = x
  · obtain ⟨a, rfl⟩ := hx
    exact closedEmbedding_acc (e.closedEmbedding R) (h.apply a)
  · exact Acc.intro x (fun y hy => (hx (by obtain ⟨a, b, _, ha, _⟩ := hy; exact ⟨a, ha⟩)).elim)

theorem root_wellFounded (e : FaithfulRealization X) :
    WellFounded (fun b a => e.Root a b) :=
  e.realized_wellFounded _ freeRecursor_step_rev_wellFounded

theorem dp_wellFounded (e : FaithfulRealization X) :
    WellFounded (fun b a => e.DP a b) :=
  e.realized_wellFounded _ freeRecursor_dp_rev_wellFounded

theorem contextual_wellFounded (e : FaithfulRealization X) :
    WellFounded (fun b a => e.Contextual a b) :=
  e.realized_wellFounded _ FreeRecursorContext.freeRecursor_ctx_rev_wellFounded

theorem realized_deterministic (e : FaithfulRealization X)
    (R : RecursorTerm → RecursorTerm → Prop)
    (hd : ∀ {x a b}, R x a → R x b → a = b) {x a b : X}
    (ha : e.Realized R x a) (hb : e.Realized R x b) : a = b := by
  obtain ⟨x', a', ha', rfl, rfl⟩ := ha
  obtain ⟨y', b', hb', he, rfl⟩ := hb
  have heq := e.injective he
  subst y'
  exact congrArg e.encode (hd ha' hb')

theorem root_deterministic (e : FaithfulRealization X) {x a b : X}
    (ha : e.Root x a) (hb : e.Root x b) : a = b :=
  e.realized_deterministic FreeRecursorStep
    (fun h g => freeRecursor_root_deterministic h g) ha hb

theorem dp_deterministic (e : FaithfulRealization X) {x a b : X}
    (ha : e.DP x a) (hb : e.DP x b) : a = b :=
  e.realized_deterministic FreeRecursorDPPair
    (fun h g => freeRecursor_dp_deterministic h g) ha hb

theorem contextual_confluent_at (e : FaithfulRealization X)
    {t : RecursorTerm} {a b : X}
    (ha : Relation.ReflTransGen e.Contextual (e.encode t) a)
    (hb : Relation.ReflTransGen e.Contextual (e.encode t) b) :
    ∃ z, Relation.ReflTransGen e.Contextual a z ∧ Relation.ReflTransGen e.Contextual b z :=
  closedEmbedding_confluent_at (e.closedEmbedding _) FreeRecursorContext.freeRecursor_ctx_confluent
    ha hb

theorem realized_confluent (e : FaithfulRealization X)
    (R : RecursorTerm → RecursorTerm → Prop)
    (hc : ∀ {x a b}, Relation.ReflTransGen R x a → Relation.ReflTransGen R x b →
      ∃ z, Relation.ReflTransGen R a z ∧ Relation.ReflTransGen R b z)
    {x a b : X} (ha : Relation.ReflTransGen (e.Realized R) x a)
    (hb : Relation.ReflTransGen (e.Realized R) x b) :
    ∃ z, Relation.ReflTransGen (e.Realized R) a z ∧ Relation.ReflTransGen (e.Realized R) b z := by
  classical
  by_cases hx : ∃ t, e.encode t = x
  · obtain ⟨t, rfl⟩ := hx
    exact closedEmbedding_confluent_at (e.closedEmbedding R) hc ha hb
  · have terminal : ∀ y, ¬ e.Realized R x y := by
      rintro y ⟨t, s, _, ht, _⟩
      exact hx ⟨t, ht⟩
    have fixed : ∀ {y}, Relation.ReflTransGen (e.Realized R) x y → x = y := by
      intro y h
      cases h using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hs _ _ => exact (terminal _ hs).elim
    obtain rfl := fixed ha
    obtain rfl := fixed hb
    exact ⟨x, .refl, .refl⟩

theorem root_confluent (e : FaithfulRealization X) {x a b : X}
    (ha : Relation.ReflTransGen e.Root x a) (hb : Relation.ReflTransGen e.Root x b) :
    ∃ z, Relation.ReflTransGen e.Root a z ∧ Relation.ReflTransGen e.Root b z :=
  e.realized_confluent _ freeRecursor_root_confluent ha hb

theorem dp_confluent (e : FaithfulRealization X) {x a b : X}
    (ha : Relation.ReflTransGen e.DP x a) (hb : Relation.ReflTransGen e.DP x b) :
    ∃ z, Relation.ReflTransGen e.DP a z ∧ Relation.ReflTransGen e.DP b z :=
  e.realized_confluent _ freeRecursor_dp_confluent ha hb

theorem contextual_confluent (e : FaithfulRealization X) {x a b : X}
    (ha : Relation.ReflTransGen e.Contextual x a) (hb : Relation.ReflTransGen e.Contextual x b) :
    ∃ z, Relation.ReflTransGen e.Contextual a z ∧ Relation.ReflTransGen e.Contextual b z :=
  e.realized_confluent _ FreeRecursorContext.freeRecursor_ctx_confluent ha hb

noncomputable def extractor (e : FaithfulRealization X) (a rhs : e.State) : Option e.State :=
  (extractCall (e.decode a) (e.decode rhs)).map e.point

theorem extractor_point (e : FaithfulRealization X) (a rhs : RecursorTerm) :
    e.extractor (e.point a) (e.point rhs) = (extractCall a rhs).map e.point := by
  simp only [extractor, decode_point]

theorem faithfulRealization_processor_sound (e : FaithfulRealization X) (a rhs c : e.State) :
    e.extractor a rhs = some c ↔ e.Root a.val rhs.val ∧ e.DP a.val c.val := by
  unfold Root DP
  rw [e.realized_state_iff, e.realized_state_iff]
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp h
    have hdc : d = e.decode c := by rw [← he, e.decode_point]
    exact hdc ▸ freeRecursor_extraction_sound hd
  · intro h
    have hh := (freeRecursor_extraction_complete h.1).mpr h.2
    simp only [extractor, hh, Option.map_some, point_decode]

/-- Conjugation of a ranked next-step function by the proved image equivalence. -/
noncomputable def transportMachine (e : FaithfulRealization X)
    (M : RankedMachine RecursorTerm) : RankedMachine e.State where
  next x := (M.next (e.decode x)).map e.point
  rank x := M.rank (e.decode x)
  decreases := by
    intro a b h
    obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp h
    rw [← he, e.decode_point]
    exact M.decreases hc

@[simp] theorem transportMachine_next_point (e : FaithfulRealization X)
    (M : RankedMachine RecursorTerm) (a : RecursorTerm) :
    (e.transportMachine M).next (e.point a) = (M.next a).map e.point := by
  simp only [transportMachine, decode_point]

theorem transportMachine_step_iff (e : FaithfulRealization X)
    (M : RankedMachine RecursorTerm) (a b : e.State) :
    (e.transportMachine M).Step a b ↔ M.Step (e.decode a) (e.decode b) := by
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp h
    rw [← he, e.decode_point]
    exact hc
  · intro h
    change (M.next (e.decode a)).map e.point = some b
    rw [h, Option.map_some, point_decode]

theorem transportMachine_normalize (e : FaithfulRealization X)
    (M : RankedMachine RecursorTerm) (a : RecursorTerm) :
    (e.transportMachine M).normalize (e.point a) = e.point (M.normalize a) := by
  induction hn : M.rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
      cases hs : M.next a with
      | none =>
          rw [(e.transportMachine M).normalize_terminal (by simp [hs]), M.normalize_terminal hs]
      | some b =>
          rw [(e.transportMachine M).normalize_step (by
            change (e.transportMachine M).next (e.point a) = some (e.point b)
            simp [hs]), M.normalize_step hs]
          exact ih (M.rank b) (by simpa [hn] using M.decreases hs) b rfl

theorem transportMachine_cost (e : FaithfulRealization X)
    (M : RankedMachine RecursorTerm) (a : RecursorTerm) :
    (e.transportMachine M).cost (e.point a) = M.cost a := by
  induction hn : M.rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
      cases hs : M.next a with
      | none =>
          rw [(e.transportMachine M).cost_terminal (by simp [hs]), M.cost_terminal hs]
      | some b =>
          rw [(e.transportMachine M).cost_step (by
            change (e.transportMachine M).next (e.point a) = some (e.point b)
            simp [hs]), M.cost_step hs]
          exact congrArg Nat.succ (ih (M.rank b) (by simpa [hn] using M.decreases hs) b rfl)

theorem transportMachine_normalize_state (e : FaithfulRealization X)
    (M : RankedMachine RecursorTerm) (x : e.State) :
    (e.transportMachine M).normalize x = e.point (M.normalize (e.decode x)) := by
  simpa only [point_decode] using e.transportMachine_normalize M (e.decode x)

theorem transportMachine_cost_state (e : FaithfulRealization X)
    (M : RankedMachine RecursorTerm) (x : e.State) :
    (e.transportMachine M).cost x = M.cost (e.decode x) := by
  simpa only [point_decode] using e.transportMachine_cost M (e.decode x)

theorem transportMachine_complete_state (e : FaithfulRealization X)
    (M : RankedMachine RecursorTerm) (x : e.State) :
    (e.transportMachine M).normalize x = e.point (M.normalize (e.decode x)) ∧
      (e.transportMachine M).cost x = M.cost (e.decode x) ∧
      ∀ y : e.State, (e.transportMachine M).Step x y ↔
        M.Step (e.decode x) (e.decode y) :=
  ⟨e.transportMachine_normalize_state M x, e.transportMachine_cost_state M x,
    e.transportMachine_step_iff M x⟩

noncomputable def rootNormalizer (e : FaithfulRealization X) := e.transportMachine rootMachine
noncomputable def dpNormalizer (e : FaithfulRealization X) := e.transportMachine dpMachine

theorem rootNormalizer_step_iff (e : FaithfulRealization X) (a b : e.State) :
    e.rootNormalizer.Step a b ↔ e.Root a.val b.val :=
  (e.transportMachine_step_iff rootMachine a b).trans
    (rootNext_iff.trans (e.realized_state_iff _ a b).symm)

theorem dpNormalizer_step_iff (e : FaithfulRealization X) (a b : e.State) :
    e.dpNormalizer.Step a b ↔ e.DP a.val b.val :=
  (e.transportMachine_step_iff dpMachine a b).trans
    (dpNext_iff.trans (e.realized_state_iff _ a b).symm)

theorem faithfulRealization_root_cost (e : FaithfulRealization X) (a : RecursorTerm) :
    e.rootNormalizer.cost (e.point a) = rootMachine.cost a := e.transportMachine_cost _ a

theorem faithfulRealization_dp_length (e : FaithfulRealization X) (b s n : RecursorTerm) :
    e.dpNormalizer.cost (e.point (.recR b s n)) = deltaPrefix n :=
  (e.transportMachine_cost _ _).trans (freeRecursor_dp_length b s n)

theorem faithfulRealization_dp_normalize (e : FaithfulRealization X) (b s n : RecursorTerm) :
    e.dpNormalizer.normalize (e.point (.recR b s n)) = e.point (.recR b s (stripDelta n)) := by
  rw [dpNormalizer, e.transportMachine_normalize, freeRecursor_dp_normalize]

noncomputable def contextNormalize (e : FaithfulRealization X) (x : e.State) : e.State :=
  e.point (FreeRecursorContext.normalize (e.decode x))

theorem faithfulRealization_context_normalization (e : FaithfulRealization X) (x : e.State) :
    Relation.ReflTransGen e.Contextual x.val (e.contextNormalize x).val ∧
      (∀ y, ¬ e.Contextual (e.contextNormalize x).val y) := by
  refine ⟨?_, (e.closedEmbedding _).normalForm_iff _ |>.mp
    (FreeRecursorContext.normalize_normal (e.decode x))⟩
  simpa only [contextNormalize, point, closedEmbedding, Function.Embedding.coeFn_mk, encode_decode] using
    closedEmbedding_star_map (e.closedEmbedding _) (FreeRecursorContext.normalize_reachable (e.decode x))

noncomputable def observedSubterm (e : FaithfulRealization X) (t : e.State) (path : List Nat) :
    Option X := (subtermAt (e.decode t) path).map e.encode

theorem observedSubterm_point (e : FaithfulRealization X) (t : RecursorTerm) (path : List Nat) :
    e.observedSubterm (e.point t) path = (subtermAt t path).map e.encode := by
  simp only [observedSubterm, decode_point]

noncomputable def roleDecision (e : FaithfulRealization X) (K : FreeBoundaryKernel)
    (r : Role) : Bool := by
  classical
  exact decide (e.observedSubterm (e.point K.output) (branchPath r) =
    (e.extractor (e.point K.source) (e.point K.output)).map Subtype.val)

theorem encode_option_injective (e : FaithfulRealization X) :
    Function.Injective (Option.map e.encode) := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases h
  | some a => cases b with
    | none => cases h
    | some b => exact congrArg some (e.encode_injective (Option.some.inj h))

theorem roleDecision_eq_free (e : FaithfulRealization X) (K : FreeBoundaryKernel) (r : Role) :
    e.roleDecision K r = actualDPChannel K r := by
  classical
  unfold roleDecision actualDPChannel
  rw [e.observedSubterm_point, e.extractor_point, Option.map_map]
  change decide ((subtermAt K.output (branchPath r)).map e.encode =
    (extractCall K.source K.output).map e.encode) = _
  simp only [e.encode_option_injective.eq_iff]

/-- The decision compares realized output branches with the realized extracted call. -/
theorem faithfulRealization_role_separator (e : FaithfulRealization X) (K : FreeBoundaryKernel) :
    e.observedSubterm (e.point K.output) [0] = some (e.encode K.generator) ∧
    e.observedSubterm (e.point K.output) [1, 1] = some (e.encode K.generator) ∧
    e.roleDecision K .frame = false ∧ e.roleDecision K .active = true ∧
    ¬ ∃ g : X → Bool, ∀ r, e.roleDecision K r = g (e.encode (generatorValue K r)) := by
  refine ⟨by rw [e.observedSubterm_point]; rfl,
    by rw [e.observedSubterm_point]; rfl,
    (e.roleDecision_eq_free K .frame).trans (actualDPChannel_frame K),
    (e.roleDecision_eq_free K .active).trans (actualDPChannel_active K), ?_⟩
  rintro ⟨g, hg⟩
  apply freeRecursor_dp_channel_not_value_factored K
  exact ⟨g ∘ e.encode, fun r => (e.roleDecision_eq_free K r).symm.trans (hg r)⟩

noncomputable def realizedOrbit (e : FaithfulRealization X) {I : Type v}
    (O : IndexedOrbitSystem I RecursorTerm) : IndexedOrbitSystem I X where
  state i := e.encode (O.state i)
  injective := e.injective.comp O.injective

noncomputable def faithfulRealization_progress_orbit_iso (e : FaithfulRealization X)
    {I : Type v} (O : IndexedOrbitSystem I RecursorTerm) (J : I → I → Prop) :
    OperatorKO7.Meta.DistinctionBoundary.MinimalFork.RelIso (O.GeneratedStep J)
      ((e.realizedOrbit O).GeneratedStep J) :=
  indexed_orbit_system_isomorphism_of_injective O (e.realizedOrbit O) J

theorem realized_recursor_orbit_dp_iff (e : FaithfulRealization X)
    (b s : RecursorTerm) (m n : Nat) :
    e.DP ((e.realizedOrbit (recursorOrbit b s)).state m)
      ((e.realizedOrbit (recursorOrbit b s)).state n) ↔ m = n + 1 :=
  (e.realized_iff _ _ _).trans (dp_recursorState_iff b s m n)

/-- Transport a whole witness language, including its verifier and target predicate. -/
noncomputable def transportHierarchy (e : FaithfulRealization X)
    (H : OperatorKO7.RepShift.WitnessHierarchy RecursorTerm) :
    OperatorKO7.RepShift.WitnessHierarchy e.State where
  W k P x := H.W k (fun t => P (e.point t)) (e.decode x)
  accepts := H.accepts
  sound := by
    intro k P x w h
    simpa only [e.point_decode] using H.sound w h

theorem transportHierarchy_adequate_iff (e : FaithfulRealization X)
    (H : OperatorKO7.RepShift.WitnessHierarchy RecursorTerm)
    (P : e.State → Prop) (x : e.State) (k : Nat) :
    (e.transportHierarchy H).hasAdequateAtDepth k P x ↔
      H.hasAdequateAtDepth k (fun t => P (e.point t)) (e.decode x) := Iff.rfl

def RootTerminates (e : FaithfulRealization X) (x : e.State) : Prop :=
  Acc (fun b a => e.Root a b) x.val

theorem rootTerminates_point_iff (e : FaithfulRealization X) (t : RecursorTerm) :
    e.RootTerminates (e.point t) ↔ FreeRecursorWitnessOrder.RootTerminates t :=
  (closedEmbedding_acc_iff (e.closedEmbedding _) t).symm

theorem rootTerminates_pullback (e : FaithfulRealization X) :
    (fun t => e.RootTerminates (e.point t)) = FreeRecursorWitnessOrder.RootTerminates := by
  funext t
  exact propext (e.rootTerminates_point_iff t)

/-- These equalities concern exactly the transported S4 languages and their verifiers. -/
theorem faithfulRealization_witness_depths (e : FaithfulRealization X) (x : e.State) (k : Nat) :
    ((e.transportHierarchy FreeRecursorWitnessOrder.truthHierarchy).hasAdequateAtDepth
      k e.RootTerminates x ↔ 1 ≤ k) ∧
    ((e.transportHierarchy FreeRecursorWitnessOrder.boundaryHierarchy).hasAdequateAtDepth
      k e.RootTerminates x ↔ 2 ≤ k) := by
  rw [e.transportHierarchy_adequate_iff, e.transportHierarchy_adequate_iff,
    e.rootTerminates_pullback]
  exact ⟨FreeRecursorWitnessOrder.truthHierarchy_adequate_iff k (e.decode x),
    FreeRecursorWitnessOrder.boundaryHierarchy_adequate_iff k (e.decode x)⟩

theorem faithfulRealization_boundary_minimum (e : FaithfulRealization X) (x : e.State) :
    OperatorKO7.RepShift.RepresentationShiftBottleneck
      (e.transportHierarchy FreeRecursorWitnessOrder.boundaryHierarchy) e.RootTerminates x 2 where
  property_holds := e.root_wellFounded.apply x.val
  no_witness_below := by
    intro k hk hw
    have := (e.faithfulRealization_witness_depths x k).2.mp hw
    omega
  witness_at_k := (e.faithfulRealization_witness_depths x 2).2.mpr (by decide)

end FaithfulRealization

/-! ## The concrete KO7 constructor interpretation -/

def ko7Algebra : SigmaAlgebra OperatorKO7.Trace where
  void := .void
  delta := .delta
  integrate := .integrate
  merge := .merge
  app := .app
  recR := .recΔ
  eqWit := .eqW

def ofTrace : OperatorKO7.Trace → RecursorTerm
  | .void => .void
  | .delta t => .delta (ofTrace t)
  | .integrate t => .integrate (ofTrace t)
  | .merge a b => .merge (ofTrace a) (ofTrace b)
  | .app a b => .app (ofTrace a) (ofTrace b)
  | .recΔ b s n => .recR (ofTrace b) (ofTrace s) (ofTrace n)
  | .eqW a b => .eqWit (ofTrace a) (ofTrace b)

theorem ofTrace_fold (t : RecursorTerm) : ofTrace (RecursorTerm.fold ko7Algebra t) = t := by
  induction t <;> simp_all [RecursorTerm.fold, ko7Algebra, ofTrace]

theorem fold_ofTrace (t : OperatorKO7.Trace) : RecursorTerm.fold ko7Algebra (ofTrace t) = t := by
  induction t <;> simp_all [RecursorTerm.fold, ko7Algebra, ofTrace]

def ko7Realization : FaithfulRealization OperatorKO7.Trace where
  algebra := ko7Algebra
  injective := Function.LeftInverse.injective ofTrace_fold

theorem ko7_encode_ofTrace (t : OperatorKO7.Trace) : ko7Realization.encode (ofTrace t) = t :=
  fold_ofTrace t

/-- Exactly the two recursor rules, not the eight-rule KO7 root relation. -/
inductive KO7RecursorStep : OperatorKO7.Trace → OperatorKO7.Trace → Prop
  | zero (b s : OperatorKO7.Trace) : KO7RecursorStep (.recΔ b s .void) b
  | succ (b s n : OperatorKO7.Trace) :
      KO7RecursorStep (.recΔ b s (.delta n)) (.app s (.recΔ b s n))

theorem ko7_root_exact (x y : OperatorKO7.Trace) :
    ko7Realization.Root x y ↔ KO7RecursorStep x y := by
  constructor
  · rintro ⟨a, b, h, rfl, rfl⟩
    cases h with
    | zero b s => exact .zero _ _
    | succ b s n => exact .succ _ _ _
  · intro h
    induction h with
    | zero b s =>
        refine ⟨.recR (ofTrace b) (ofTrace s) .void, ofTrace b, .zero _ _, ?_, ?_⟩
        · change OperatorKO7.Trace.recΔ (RecursorTerm.fold ko7Algebra (ofTrace b))
            (RecursorTerm.fold ko7Algebra (ofTrace s)) .void = _
          rw [fold_ofTrace, fold_ofTrace]
        · exact ko7_encode_ofTrace b
    | succ b s n =>
        refine ⟨.recR (ofTrace b) (ofTrace s) (.delta (ofTrace n)),
          .app (ofTrace s) (.recR (ofTrace b) (ofTrace s) (ofTrace n)), .succ _ _ _, ?_, ?_⟩
        · exact fold_ofTrace (.recΔ b s (.delta n))
        · exact fold_ofTrace (.app s (.recΔ b s n))

theorem ko7_dp_exact (x y : OperatorKO7.Trace) :
    ko7Realization.DP x y ↔ OperatorKO7.MetaDependencyPairs.DPPair x y := by
  constructor
  · rintro ⟨a, b, h, rfl, rfl⟩
    cases h with
    | succ b s n => exact .rec_succ _ _ _
  · intro h
    cases h with
    | rec_succ b s n =>
        refine ⟨.recR (ofTrace b) (ofTrace s) (.delta (ofTrace n)),
          .recR (ofTrace b) (ofTrace s) (ofTrace n), .succ _ _ _, ?_, ?_⟩
        · exact fold_ofTrace (.recΔ b s (.delta n))
        · exact fold_ofTrace (.recΔ b s n)

theorem ko7RecursorStep_sub_fullStep {x y : OperatorKO7.Trace}
    (h : KO7RecursorStep x y) : OperatorKO7.Step x y := by
  induction h with
  | zero b s => exact .R_rec_zero b s
  | succ b s n => exact .R_rec_succ b s n

theorem ko7_adapter_not_all_root_rules :
    OperatorKO7.Step (.merge .void .void) .void ∧
      ¬ ko7Realization.Root (.merge .void .void) .void := by
  refine ⟨.R_merge_void_left .void, ?_⟩
  intro h
  have hh := (ko7_root_exact _ _).mp h
  cases hh

/-! ## Necessary hypotheses and ambient extensions -/

def unitAlgebra : SigmaAlgebra Unit where
  void := ()
  delta := fun _ => ()
  integrate := fun _ => ()
  merge := fun _ _ => ()
  app := fun _ _ => ()
  recR := fun _ _ _ => ()
  eqWit := fun _ _ => ()

theorem collapsed_realization_not_injective :
    ¬ Function.Injective (RecursorTerm.fold unitAlgebra) := by
  intro hi
  have h : RecursorTerm.void = .delta .void := hi (show
    RecursorTerm.fold unitAlgebra .void = RecursorTerm.fold unitAlgebra (.delta .void) from rfl)
  cases h

theorem unit_fold_constant (t : RecursorTerm) : RecursorTerm.fold unitAlgebra t = () :=
  Subsingleton.elim _ _

/-- The collapsed channel compares the same output branches and extracted call. -/
def collapsedDPChannel (K : FreeBoundaryKernel) (r : Role) : Bool :=
  decide ((subtermAt K.output (branchPath r)).map (RecursorTerm.fold unitAlgebra) =
    (extractCall K.source K.output).map (RecursorTerm.fold unitAlgebra))

theorem collapsedDPChannel_always_true (K : FreeBoundaryKernel) (r : Role) :
    collapsedDPChannel K r = true := by
  unfold collapsedDPChannel
  rw [K.extraction]
  cases r <;> simp [branchPath, FreeBoundaryKernel.output, subtermAt, children, unit_fold_constant]

theorem collapsedDPChannel_fails_separation (K : FreeBoundaryKernel) :
    collapsedDPChannel K .frame = collapsedDPChannel K .active ∧
      ¬ Function.Injective (collapsedDPChannel K) := by
  refine ⟨by rw [collapsedDPChannel_always_true, collapsedDPChannel_always_true], ?_⟩
  intro h
  have he : Role.frame = Role.active := h (by
    rw [collapsedDPChannel_always_true, collapsedDPChannel_always_true])
  cases he

theorem collapsed_realization_cannot_reflect (R : Unit → Unit → Prop)
    (hs : ∀ {a b}, FreeRecursorStep a b →
      R (RecursorTerm.fold unitAlgebra a) (RecursorTerm.fold unitAlgebra b)) :
    ¬ ∀ a b, R (RecursorTerm.fold unitAlgebra a) (RecursorTerm.fold unitAlgebra b) →
      FreeRecursorStep a b := by
  intro hr
  have h : R () () := hs (.zero .void .void)
  have impossible := hr .void .void h
  cases impossible

/-- Image-pair reflection alone permits an exit to an unrepresented self-loop. -/
def EscapingAmbient : Option RecursorTerm → Option RecursorTerm → Prop
  | some a, some b => FreeRecursorStep a b
  | _, none => True
  | none, some _ => False

theorem escapingAmbient_reflects (a b : RecursorTerm) :
    EscapingAmbient (some a) (some b) ↔ FreeRecursorStep a b := Iff.rfl

theorem escapingAmbient_not_outgoing_closed :
    ¬ ∀ {a y}, EscapingAmbient (some a) y → ∃ b, some b = y := by
  intro h
  obtain ⟨b, hb⟩ := h (a := .void) (y := none) trivial
  cases hb

theorem escapingAmbient_not_accessible :
    ¬ Acc (fun b a => EscapingAmbient a b) (some RecursorTerm.void) := by
  intro h
  have hn : Acc (fun b a => EscapingAmbient a b) none := h.inv trivial
  have hh : ∀ x, Acc (fun b a => EscapingAmbient a b) x → x ≠ none := by
    intro x hx
    induction hx with
    | intro x hx ih =>
        intro he
        subst x
        exact ih none trivial rfl
  exact hh none hn rfl

/-- An ambient system can extend a faithful copy only if its outgoing edges also lift. -/
theorem ambient_transport_of_exact_outgoing (e : FaithfulRealization X)
    (R : RecursorTerm → RecursorTerm → Prop) (S : X → X → Prop)
    (hreflect : ∀ a b, S (e.encode a) (e.encode b) ↔ R a b)
    (hclosed : ∀ {a y}, S (e.encode a) y → ∃ b, e.encode b = y)
    (hR : WellFounded (fun b a => R a b)) (a : RecursorTerm) :
    Acc (fun b a => S a b) (e.encode a) :=
  closedEmbedding_acc
    { map := ⟨e.encode, e.injective⟩
      step_iff := (hreflect _ _).symm
      forward_closed := hclosed } (hR.apply a)

/-- Source confluence transports at the same represented start, without
requiring confluence at any other free state. -/
theorem ambient_confluence_of_exact_outgoing (e : FaithfulRealization X)
    (R : RecursorTerm → RecursorTerm → Prop) (S : X → X → Prop)
    (hreflect : ∀ a b, S (e.encode a) (e.encode b) ↔ R a b)
    (hclosed : ∀ {a y}, S (e.encode a) y → ∃ b, e.encode b = y)
    (a : RecursorTerm)
    (hR : ∀ {b c}, Relation.ReflTransGen R a b → Relation.ReflTransGen R a c →
      ∃ z, Relation.ReflTransGen R b z ∧ Relation.ReflTransGen R c z)
    {x y : X} (hx : Relation.ReflTransGen S (e.encode a) x)
    (hy : Relation.ReflTransGen S (e.encode a) y) :
    ∃ z, Relation.ReflTransGen S x z ∧ Relation.ReflTransGen S y z := by
  let i : ClosedRelationEmbedding R S :=
    { map := ⟨e.encode, e.injective⟩
      step_iff := (hreflect _ _).symm
      forward_closed := hclosed }
  obtain ⟨b, rfl, hb⟩ := closedEmbedding_star_pull i hx
  obtain ⟨c, rfl, hc⟩ := closedEmbedding_star_pull i hy
  obtain ⟨z, hbz, hcz⟩ := hR hb hc
  exact ⟨i.map z, closedEmbedding_star_map i hbz, closedEmbedding_star_map i hcz⟩

theorem ambient_exact_outgoing_iff (e : FaithfulRealization X)
    (R : RecursorTerm → RecursorTerm → Prop) (S : X → X → Prop) :
    (∀ a y, S (e.encode a) y ↔ e.Realized R (e.encode a) y) ↔
    (∀ a b, S (e.encode a) (e.encode b) ↔ R a b) ∧
      (∀ {a y}, S (e.encode a) y → ∃ b, e.encode b = y) := by
  constructor
  · intro h
    refine ⟨fun a b => (h a (e.encode b)).trans (e.realized_iff R a b), ?_⟩
    intro a y hs
    obtain ⟨b, c, _, _, hc⟩ := (h a y).mp hs
    exact ⟨c, hc⟩
  · rintro ⟨hr, hc⟩ a y
    constructor
    · intro hs
      obtain ⟨b, rfl⟩ := hc hs
      exact (e.realized_iff R a b).mpr ((hr a b).mp hs)
    · rintro ⟨b, c, h, hb, rfl⟩
      have heq := e.injective hb
      exact (hr a c).mpr (heq ▸ h)

end OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization
