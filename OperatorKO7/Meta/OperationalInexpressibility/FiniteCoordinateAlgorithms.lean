import OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.RepairCover
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.WitnessRank
import OperatorKO7.Meta.Rewriting.CriticalPair

/-!
# Finite-coordinate algorithms

Every executable search receives an explicit complete enumeration. Relation-only
coordinates use only that enumeration and the Boolean edge table. Critical-pair
origin, repair coverage, prices, and adequacy predicates remain separate inputs.
-/

set_option autoImplicit false

open scoped BigOperators
open Relation

namespace OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms

open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation
open OperatorKO7.Meta.DistinctionBoundary.Quantitative
open OperatorKO7.Meta.Rewriting
open scoped Subst

universe u v w z

/-- Executable finite relation presentation. The explicit enumeration is part of
the input, so no executable definition needs to enumerate a `Finset`. -/
structure RelationTable (α : Type u) [DecidableEq α] where
  explicit : Enumeration α
  stepB : α → α → Bool

namespace RelationTable

variable {α : Type u} [DecidableEq α]

/-- Proposition represented by the Boolean edge table. -/
def Step (T : RelationTable α) (a b : α) : Prop := T.stepB a b = true

instance (T : RelationTable α) : DecidableRel T.Step :=
  fun _ _ => Bool.decEq _ _

@[simp] theorem step_iff (T : RelationTable α) (a b : α) :
    T.Step a b ↔ T.stepB a b = true := Iff.rfl

end RelationTable

/-! ## Relation-only coordinates -/

section RelationOnly

variable {α : Type u} [DecidableEq α]

/-- Exact finite reachability through the validated finite-index adapter. -/
def reachableB (T : RelationTable α) (a b : α) : Bool :=
  TransitionConservation.reachableFromB T.explicit T.Step a b

@[simp] theorem reachableB_eq_true_iff (T : RelationTable α) (a b : α) :
    reachableB T a b = true ↔ ReflTransGen T.Step a b := by
  unfold reachableB
  exact TransitionConservation.reachableFromB_eq_true_iff T.explicit T.Step a b

/-- A state is normal exactly when no edge in the complete enumeration leaves it. -/
def normalB (T : RelationTable α) (a : α) : Bool :=
  T.explicit.items.all fun b => !(T.stepB a b)

@[simp] theorem normalB_eq_true_iff (T : RelationTable α) (a : α) :
    normalB T a = true ↔ ∀ b, ¬ T.Step a b := by
  simp [normalB, RelationTable.Step, T.explicit.complete]

/-- Reachable normal states in enumeration order. -/
def terminalSupport (T : RelationTable α) (source : α) : List α :=
  T.explicit.items.filter fun t => reachableB T source t && normalB T t

/-- Number of reachable normal states. -/
def terminalMultiplicity (T : RelationTable α) (source : α) : Nat :=
  (terminalSupport T source).length

/-- Two states are joinable when one enumerated state is reachable from both. -/
def joinableB (T : RelationTable α) (a b : α) : Bool :=
  T.explicit.items.any fun c => reachableB T a c && reachableB T b c

@[simp] theorem joinableB_eq_true_iff (T : RelationTable α) (a b : α) :
    joinableB T a b = true ↔
      ∃ c, ReflTransGen T.Step a c ∧ ReflTransGen T.Step b c := by
  simp [joinableB, reachableB_eq_true_iff, T.explicit.complete]

/-- Finite joinability is symmetric. -/
theorem joinableB_comm (T : RelationTable α) (a b : α) :
    joinableB T a b = joinableB T b a := by
  simp [joinableB, Bool.and_comm]

/-- Confluence on the descendant set of one source. -/
def sourceConfluentB (T : RelationTable α) (source : α) : Bool :=
  T.explicit.items.all fun a =>
    !reachableB T source a ||
      T.explicit.items.all fun b =>
        !reachableB T source b || joinableB T a b

@[simp] theorem sourceConfluentB_eq_true_iff (T : RelationTable α) (source : α) :
    sourceConfluentB T source = true ↔
      ∀ a b, ReflTransGen T.Step source a → ReflTransGen T.Step source b →
        ∃ c, ReflTransGen T.Step a c ∧ ReflTransGen T.Step b c := by
  simp [sourceConfluentB, joinableB_eq_true_iff, T.explicit.complete]
  constructor
  · intro h a b ha hb
    rcases h a with hra | hrest
    · have ht : reachableB T source a = true :=
        (reachableB_eq_true_iff T source a).2 ha
      simp [ht] at hra
    · rcases hrest b with hrb | hj
      · have ht : reachableB T source b = true :=
          (reachableB_eq_true_iff T source b).2 hb
        simp [ht] at hrb
      · exact hj
  · intro h a
    by_cases ha : ReflTransGen T.Step source a
    · right
      intro b
      by_cases hb : ReflTransGen T.Step source b
      · right
        exact h a b ha hb
      · left
        have hnot : reachableB T source b ≠ true := by
          intro ht
          exact hb ((reachableB_eq_true_iff T source b).1 ht)
        exact Bool.eq_false_of_not_eq_true hnot
    · left
      have hnot : reachableB T source a ≠ true := by
        intro ht
        exact ha ((reachableB_eq_true_iff T source a).1 ht)
      exact Bool.eq_false_of_not_eq_true hnot

/-- Node-list representation of a concrete relation path. -/
inductive PathFrom (T : RelationTable α) (source : α) : List α → α → Prop
  | singleton : PathFrom T source [source] source
  | snoc {nodes : List α} {u v : α} :
      PathFrom T source nodes u → T.Step u v →
        PathFrom T source (nodes ++ [v]) v

/-- Every concrete node-list path proves reachability. -/
theorem PathFrom.reachable {T : RelationTable α} {source target : α} {nodes : List α}
    (h : PathFrom T source nodes target) : ReflTransGen T.Step source target := by
  induction h with
  | singleton => exact .refl
  | snoc hp huv ih => exact ih.tail huv

/-- First successful result in explicit list order. -/
def firstSome {A : Type u} {B : Type v} (f : A → Option B) : List A → Option B
  | [] => none
  | a :: as =>
      match f a with
      | some b => some b
      | none => firstSome f as

/-- A successful result came from one listed candidate. -/
theorem firstSome_sound {A : Type u} {B : Type v} (f : A → Option B) :
    ∀ {xs : List A} {b : B}, firstSome f xs = some b →
      ∃ a ∈ xs, f a = some b := by
  intro xs
  induction xs with
  | nil => simp [firstSome]
  | cons a as ih =>
      intro b h
      simp only [firstSome] at h
      cases ha : f a with
      | some c =>
          simp [ha] at h
          subst c
          exact ⟨a, by simp, ha⟩
      | none =>
          simp [ha] at h
          rcases ih h with ⟨x, hx, hfx⟩
          exact ⟨x, by simp [hx], hfx⟩

/-- A successful listed candidate makes the whole search successful. -/
theorem firstSome_isSome_of_mem {A : Type u} {B : Type v}
    (f : A → Option B) {xs : List A} {a : A}
    (ha : a ∈ xs) (hfa : (f a).isSome) : (firstSome f xs).isSome := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [firstSome]
      cases hx : f x with
      | some b => simp
      | none =>
          rcases (List.mem_cons.mp ha) with rfl | ha
          · simp [hx] at hfa
          · exact ih ha

/-- Search failure means every listed candidate failed. -/
theorem firstSome_eq_none_iff {A : Type u} {B : Type v}
    (f : A → Option B) (xs : List A) :
    firstSome f xs = none ↔ ∀ a ∈ xs, f a = none := by
  induction xs with
  | nil => simp [firstSome]
  | cons a as ih =>
      simp only [firstSome]
      cases ha : f a with
      | none => simp [ha, ih]
      | some b => simp [ha]

/-- Bounded path reconstruction. Earlier paths are retained before a new
predecessor edge is appended. The predecessor search uses the supplied carrier
list, never `Finset.toList`. -/
def reconstructPath (T : RelationTable α) (source : α) : Nat → α → Option (List α)
  | 0, target => if target = source then some [source] else none
  | fuel + 1, target =>
      match reconstructPath T source fuel target with
      | some p => some p
      | none =>
          firstSome
            (fun u =>
              if T.stepB u target then
                (reconstructPath T source fuel u).map fun p => p ++ [target]
              else none)
            T.explicit.items

/-- Any indexed bounded-closure member has a reconstructed path on the original
carrier. -/
theorem reconstructPath_isSome_of_mem_indexedReachIter
    (T : RelationTable α) (source : α) :
    ∀ fuel target,
      (enumerationEquiv T.explicit).symm target ∈
        OperatorKO7.FiniteGraphReachability.reachIter
          (indexedRelation T.explicit T.Step)
          ((enumerationEquiv T.explicit).symm source) fuel →
      (reconstructPath T source fuel target).isSome := by
  intro fuel
  induction fuel with
  | zero =>
      intro target hmem
      simp [OperatorKO7.FiniteGraphReachability.reachIter] at hmem
      have hEqIdx :
          (enumerationEquiv T.explicit).symm target =
            (enumerationEquiv T.explicit).symm source := by
        simpa [OperatorKO7.FiniteGraphReachability.reachIter] using hmem
      have hEq : target = source := by
        exact (enumerationEquiv T.explicit).symm.injective hEqIdx
      simp [reconstructPath, hEq]
  | succ fuel ih =>
      intro target hmem
      have hs :
          (enumerationEquiv T.explicit).symm target ∈
            OperatorKO7.FiniteGraphReachability.succSet
              (indexedRelation T.explicit T.Step)
              (OperatorKO7.FiniteGraphReachability.reachIter
                (indexedRelation T.explicit T.Step)
                ((enumerationEquiv T.explicit).symm source) fuel) := by
        simpa [OperatorKO7.FiniteGraphReachability.reachIter] using hmem
      rcases (OperatorKO7.FiniteGraphReachability.mem_succSet
        (R := indexedRelation T.explicit T.Step)).1 hs with hprev | ⟨i, hi, hit⟩
      · have hrec := ih target hprev
        cases h : reconstructPath T source fuel target with
        | none => simp [h] at hrec
        | some p => simp [reconstructPath, h]
      · let u : α := enumerationEquiv T.explicit i
        have hu :
            (reconstructPath T source fuel u).isSome := by
          apply ih u
          simpa [u] using hi
        have hstep : T.stepB u target = true := by
          change T.Step u target
          simpa [indexedRelation, u] using hit
        cases htarget : reconstructPath T source fuel target with
        | some p => simp [reconstructPath, htarget]
        | none =>
            have hcand :
                ((if T.stepB u target then
                    (reconstructPath T source fuel u).map fun p => p ++ [target]
                  else none)).isSome := by
              simp [hstep, hu]
            have hfirst := firstSome_isSome_of_mem
              (fun x =>
                if T.stepB x target then
                  (reconstructPath T source fuel x).map fun p => p ++ [target]
                else none)
              (T.explicit.complete u) hcand
            simpa [reconstructPath, htarget] using hfirst

/-- Public path search at the exact finite-index saturation bound. -/
def path? (T : RelationTable α) (source target : α) : Option (List α) :=
  reconstructPath T source T.explicit.items.length target

/-- Every reachable state receives a concrete path. -/
theorem path?_complete_of_reachable
    (T : RelationTable α) (source target : α)
    (h : ReflTransGen T.Step source target) :
    ∃ nodes, path? T source target = some nodes := by
  have hidx : ReflTransGen (indexedRelation T.explicit T.Step)
      ((enumerationEquiv T.explicit).symm source)
      ((enumerationEquiv T.explicit).symm target) :=
    (indexed_reflTransGen_iff T.explicit T.Step source target).2 h
  have hmem := OperatorKO7.FiniteGraphReachability.mem_reachIter_card_of_reflTransGen
    (R := indexedRelation T.explicit T.Step) hidx
  have hs : (reconstructPath T source T.explicit.items.length target).isSome := by
    apply reconstructPath_isSome_of_mem_indexedReachIter T source
    simpa using hmem
  exact Option.isSome_iff_exists.mp hs

/-- The reconstruction algorithm returns only genuine node-list paths. -/
theorem reconstructPath_sound (T : RelationTable α) (source : α) :
    ∀ fuel target nodes,
      reconstructPath T source fuel target = some nodes →
        PathFrom T source nodes target := by
  intro fuel
  induction fuel with
  | zero =>
      intro target nodes h
      simp only [reconstructPath] at h
      split at h
      · next heq =>
          subst target
          simp at h
          subst nodes
          exact .singleton
      · simp at h
  | succ fuel ih =>
      intro target nodes h
      simp only [reconstructPath] at h
      cases htarget : reconstructPath T source fuel target with
      | some p =>
          simp [htarget] at h
          subst nodes
          exact ih target p htarget
      | none =>
          have hfirst : firstSome
              (fun u =>
                if T.stepB u target then
                  (reconstructPath T source fuel u).map fun p => p ++ [target]
                else none)
              T.explicit.items = some nodes := by
            simpa [htarget] using h
          rcases firstSome_sound _ hfirst with ⟨u, _, hu⟩
          by_cases hstep : T.stepB u target = true
          · have hmap :
                (reconstructPath T source fuel u).map (fun p => p ++ [target]) =
                  some nodes := by
              simpa [hstep] using hu
            rcases Option.map_eq_some_iff.mp hmap with ⟨p, hp, rfl⟩
            exact .snoc (ih u p hp) hstep
          · simp [hstep] at hu

/-- Every returned public path is sound. -/
theorem path?_sound (T : RelationTable α) (source target : α) {nodes : List α}
    (h : path? T source target = some nodes) : PathFrom T source nodes target :=
  reconstructPath_sound T source T.explicit.items.length target nodes h

/-- Distinct reachable normal forms certify nonjoinability. -/
structure NonjoinabilityEvidence (T : RelationTable α) (source : α) where
  left : α
  right : α
  left_mem : left ∈ terminalSupport T source
  right_mem : right ∈ terminalSupport T source
  distinct : left ≠ right

/-- Search for two distinct reachable normal forms. -/
def nonjoinabilityPair? (T : RelationTable α) (source : α) : Option (α × α) :=
  firstSome
    (fun p => if p.1 ≠ p.2 then some p else none)
    ((terminalSupport T source).flatMap fun a =>
      (terminalSupport T source).map fun b => (a, b))

/-- Returned normal-form pairs have the advertised properties. -/
theorem nonjoinabilityPair?_spec
    (T : RelationTable α) (source : α) {p : α × α}
    (h : nonjoinabilityPair? T source = some p) :
    p.1 ∈ terminalSupport T source ∧ p.2 ∈ terminalSupport T source ∧ p.1 ≠ p.2 := by
  unfold nonjoinabilityPair? at h
  rcases firstSome_sound _ h with ⟨q, hqmem, hq⟩
  by_cases hne : q.1 ≠ q.2
  · simp [hne] at hq
    subst p
    have hm : q.1 ∈ terminalSupport T source ∧ q.2 ∈ terminalSupport T source := by
      rcases List.mem_flatMap.mp hqmem with ⟨a, ha, hab⟩
      rcases List.mem_map.mp hab with ⟨b, hb, hqeq⟩
      cases hqeq
      exact ⟨ha, hb⟩
    exact ⟨hm.1, hm.2, hne⟩
  · simp [hne] at hq

/-- Structure-valued certificate for a returned pair. -/
def nonjoinabilityPair?_sound
    (T : RelationTable α) (source : α) {p : α × α}
    (h : nonjoinabilityPair? T source = some p) :
    NonjoinabilityEvidence T source := by
  rcases nonjoinabilityPair?_spec T source h with ⟨hl, hr, hne⟩
  exact ⟨p.1, p.2, hl, hr, hne⟩

/-- Any two distinct reachable normal forms force successful search. -/
theorem nonjoinabilityPair?_complete
    (T : RelationTable α) (source a b : α)
    (ha : a ∈ terminalSupport T source) (hb : b ∈ terminalSupport T source)
    (hne : a ≠ b) : (nonjoinabilityPair? T source).isSome := by
  unfold nonjoinabilityPair?
  let candidate : α × α → Option (α × α) := fun p =>
    if p.1 ≠ p.2 then some p else none
  have hab : (a, b) ∈
      ((terminalSupport T source).flatMap fun x =>
        (terminalSupport T source).map fun y => (x, y)) := by
    simp [ha, hb]
  have hcand : (candidate (a, b)).isSome := by simp [candidate, hne]
  exact firstSome_isSome_of_mem candidate hab hcand

/-- A normal state has no distinct reachable descendant. -/
theorem normal_reachable_eq
    (T : RelationTable α) {a c : α}
    (ha : normalB T a = true) (h : ReflTransGen T.Step a c) : c = a := by
  have hN := (normalB_eq_true_iff T a).1 ha
  induction h with
  | refl => rfl
  | tail hab hbc ih =>
      rw [ih] at hbc
      exact False.elim (hN _ hbc)

/-- Distinct normal forms cannot be joinable. -/
theorem distinct_normal_forms_not_joinable
    (T : RelationTable α) {a b : α}
    (ha : normalB T a = true) (hb : normalB T b = true) (hne : a ≠ b) :
    joinableB T a b = false := by
  by_contra hfalse
  have hj : joinableB T a b = true := by
    cases h : joinableB T a b <;> simp_all
  rcases (joinableB_eq_true_iff T a b).1 hj with ⟨c, hac, hbc⟩
  have hca := normal_reachable_eq T ha hac
  have hcb := normal_reachable_eq T hb hbc
  exact hne (hca.symm.trans hcb)

/-- General source nonjoinability evidence. -/
structure SourceNonjoinabilityEvidence (T : RelationTable α) (source : α) where
  left : α
  right : α
  left_reachable : ReflTransGen T.Step source left
  right_reachable : ReflTransGen T.Step source right
  nonjoinable : joinableB T left right = false

/-- Exhaustive descendant-pair list that fails joinability. -/
def sourceNonjoinablePairs (T : RelationTable α) (source : α) : List (α × α) :=
  (TransitionConservation.enumeratedPairs T.explicit).filter fun p =>
    reachableB T source p.1 && reachableB T source p.2 && !joinableB T p.1 p.2

/-- First general source-nonjoinability witness. -/
def sourceNonjoinabilityPair? (T : RelationTable α) (source : α) : Option (α × α) :=
  firstSome
    (fun p => if reachableB T source p.1 && reachableB T source p.2 &&
        !joinableB T p.1 p.2 then some p else none)
    (TransitionConservation.enumeratedPairs T.explicit)

/-- Every returned pair is a genuine descendant nonjoinability witness. -/
theorem sourceNonjoinabilityPair?_sound
    (T : RelationTable α) (source : α) {p : α × α}
    (h : sourceNonjoinabilityPair? T source = some p) :
    ReflTransGen T.Step source p.1 ∧
      ReflTransGen T.Step source p.2 ∧ joinableB T p.1 p.2 = false := by
  unfold sourceNonjoinabilityPair? at h
  rcases firstSome_sound _ h with ⟨q, _, hq⟩
  simp [reachableB_eq_true_iff] at hq
  rcases hq with ⟨⟨⟨hqa, hqb⟩, hnj⟩, hqp⟩
  subst p
  exact ⟨hqa, hqb, hnj⟩

/-- Search failure is exactly source confluence. -/
theorem sourceNonjoinabilityPair?_eq_none_iff
    (T : RelationTable α) (source : α) :
    sourceNonjoinabilityPair? T source = none ↔ sourceConfluentB T source = true := by
  unfold sourceNonjoinabilityPair?
  rw [firstSome_eq_none_iff, sourceConfluentB_eq_true_iff]
  constructor
  · intro hall a b ha hb
    have hp := hall (a, b) (TransitionConservation.pair_mem_enumeratedPairs T.explicit a b)
    by_cases hj : joinableB T a b = true
    · exact (joinableB_eq_true_iff T a b).1 hj
    · have hra : reachableB T source a = true := (reachableB_eq_true_iff T source a).2 ha
      have hrb : reachableB T source b = true := (reachableB_eq_true_iff T source b).2 hb
      have hjf : joinableB T a b = false := Bool.eq_false_of_not_eq_true hj
      simp [hra, hrb, hjf] at hp
  · intro hconf p hp
    rcases p with ⟨a, b⟩
    by_cases hra : reachableB T source a = true
    · by_cases hrb : reachableB T source b = true
      · rcases hconf a b (reachableB_eq_true_iff T source a |>.1 hra)
          (reachableB_eq_true_iff T source b |>.1 hrb) with ⟨c, hac, hbc⟩
        have hj : joinableB T a b = true :=
          (joinableB_eq_true_iff T a b).2 ⟨c, hac, hbc⟩
        simp [hra, hrb, hj]
      · have hrbf : reachableB T source b = false := Bool.eq_false_of_not_eq_true hrb
        simp [hra, hrbf]
    · have hraf : reachableB T source a = false := Bool.eq_false_of_not_eq_true hra
      simp [hraf]

/-- Symbolic Hartley quantity. Empty terminal support remains explicit. -/
inductive HartleyTerminal where
  | empty
  | log2Support (supportSize : Nat)
deriving DecidableEq, Repr

/-- Exact symbolic terminal-support information. -/
def terminalHartley (T : RelationTable α) (source : α) : HartleyTerminal :=
  match terminalMultiplicity T source with
  | 0 => .empty
  | n + 1 => .log2Support (n + 1)

/-- Real interpretation is intentionally noncomputable. -/
noncomputable def HartleyTerminal.real? : HartleyTerminal → Option ℝ
  | .empty => none
  | .log2Support n => some (Real.logb 2 n)

/-- Nonempty symbolic support interprets as the corresponding real logarithm. -/
theorem terminalHartley_real?_eq
    (T : RelationTable α) (source : α)
    (h : terminalMultiplicity T source ≠ 0) :
    (terminalHartley T source).real? =
      some (Real.logb 2 (terminalMultiplicity T source)) := by
  cases hm : terminalMultiplicity T source with
  | zero => exact (h hm).elim
  | succ n => simp [terminalHartley, hm, HartleyTerminal.real?]

/-- Empty symbolic support is exact. -/
theorem terminalHartley_eq_empty_iff
    (T : RelationTable α) (source : α) :
    terminalHartley T source = .empty ↔ terminalMultiplicity T source = 0 := by
  cases hm : terminalMultiplicity T source <;> simp [terminalHartley, hm]

/-- Relation-only coordinates collected without auxiliary TRS data. -/
structure RelationOnlyCoordinates where
  terminalCount : Nat
  confluentAtSource : Bool
deriving DecidableEq, Repr

/-- Relation-only coordinate computation. -/
def relationOnlyCoordinates (T : RelationTable α) (source : α) : RelationOnlyCoordinates :=
  ⟨terminalMultiplicity T source, sourceConfluentB T source⟩

/-- Identical executable relation presentations have identical relation-only coordinates. -/
theorem relationOnlyCoordinates_congr
    {T U : RelationTable α} (h : T = U) (source : α) :
    relationOnlyCoordinates T source = relationOnlyCoordinates U source := by
  cases h
  rfl

end RelationOnly

/-! ## Auxiliary peak and critical-pair inputs -/

/-- A finite semantic peak item. This is intentionally not called a TRS critical pair. -/
structure PeakItem (α : Type u) where
  source : α
  left : α
  right : α

/-- Complete supplied inventory of the finite one-step peaks under study. -/
structure PeakInput (α : Type u) [DecidableEq α] (T : RelationTable α) where
  items : List (PeakItem α)
  complete : ∀ s a b, T.Step s a → T.Step s b →
    ∃ item ∈ items, item.source = s ∧
      ((item.left = a ∧ item.right = b) ∨ (item.left = b ∧ item.right = a))

/-- A supplied semantic peak is defective exactly when both steps are real and
the reducts fail finite joinability. -/
def PeakItem.IsDefect {α : Type u} [DecidableEq α]
    (T : RelationTable α) (item : PeakItem α) : Prop :=
  T.Step item.source item.left ∧ T.Step item.source item.right ∧
    joinableB T item.left item.right = false

instance peakItemIsDefectDecidable {α : Type u} [DecidableEq α]
    (T : RelationTable α) (item : PeakItem α) : Decidable (item.IsDefect T) := by
  unfold PeakItem.IsDefect
  infer_instance

/-- Executable defective-peak list for the supplied peak inventory. -/
def peakDefects {α : Type u} [DecidableEq α]
    (T : RelationTable α) (I : PeakInput α T) : List (PeakItem α) :=
  I.items.filter fun item => decide (item.IsDefect T)

@[simp] theorem mem_peakDefects_iff {α : Type u} [DecidableEq α]
    (T : RelationTable α) (I : PeakInput α T) (item : PeakItem α) :
    item ∈ peakDefects T I ↔ item ∈ I.items ∧ item.IsDefect T := by
  simp [peakDefects]

/-- A nonjoinable one-step peak represented by the supplied complete inventory is
returned by the executable defect filter. -/
theorem peakDefects_complete {α : Type u} [DecidableEq α]
    (T : RelationTable α) (I : PeakInput α T) {s a b : α}
    (hsa : T.Step s a) (hsb : T.Step s b)
    (hnj : joinableB T a b = false) :
    ∃ item ∈ peakDefects T I, item.source = s ∧
      ((item.left = a ∧ item.right = b) ∨
        (item.left = b ∧ item.right = a)) := by
  rcases I.complete s a b hsa hsb with ⟨item, hmem, hsrc, hpairs⟩
  refine ⟨item, ?_, hsrc, hpairs⟩
  rw [mem_peakDefects_iff]
  refine ⟨hmem, ?_⟩
  rcases hpairs with hpair | hpair
  · rcases hpair with ⟨hl, hr⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hsrc, hl] using hsa
    · simpa [hsrc, hr] using hsb
    · simpa [hl, hr] using hnj
  · rcases hpair with ⟨hl, hr⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hsrc, hl] using hsb
    · simpa [hsrc, hr] using hsa
    · rw [hl, hr, joinableB_comm]
      exact hnj

/-- Backward-compatible names for the semantic peak inventory. -/
abbrev CriticalPairItem (α : Type u) := PeakItem α
abbrev CriticalPairInput (α : Type u) [DecidableEq α] (T : RelationTable α) := PeakInput α T
abbrev criticalPairDefects {α : Type u} [DecidableEq α]
    (T : RelationTable α) (I : CriticalPairInput α T) := peakDefects T I

/-- Backward-compatible membership statement. -/
theorem mem_criticalPairDefects_iff {α : Type u} [DecidableEq α]
    (T : RelationTable α) (I : CriticalPairInput α T) (item : CriticalPairItem α) :
    item ∈ criticalPairDefects T I ↔ item ∈ I.items ∧ item.IsDefect T :=
  mem_peakDefects_iff T I item

/-- First-order TRS critical-pair origin certificate. It records the two source
rules, overlap position, overlapped subterm, unifier, source and both contracta. -/
structure TRSCriticalPairOrigin
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) where
  leftRule : Rule sigma nu
  rightRule : Rule sigma nu
  leftRule_mem : leftRule ∈ R
  rightRule_mem : rightRule ∈ R
  position : Pos
  subterm : Term sigma (RenVar nu)
  unifier : Subst sigma (RenVar nu)
  source : Term sigma (RenVar nu)
  left : Term sigma (RenVar nu)
  right : Term sigma (RenVar nu)
  position_nonvariable : position ∈ nonVarPositions (renameRule (Sum.inl : nu → RenVar nu) leftRule).lhs
  subterm_eq :
    Term.subtermAt (renameRule (Sum.inl : nu → RenVar nu) leftRule).lhs position = some subterm
  unify_eq : unify subterm (renameRule (Sum.inr : nu → RenVar nu) rightRule).lhs = some unifier
  source_eq : source = unifier • (renameRule (Sum.inl : nu → RenVar nu) leftRule).lhs
  left_eq : left = unifier • (renameRule (Sum.inl : nu → RenVar nu) leftRule).rhs
  right_eq : right = unifier •
    Term.replaceAt (renameRule (Sum.inl : nu → RenVar nu) leftRule).lhs position
      (renameRule (Sum.inr : nu → RenVar nu) rightRule).rhs

/-- Every typed origin certificate denotes an actual one-step peak in the
renamed first-order TRS. -/
theorem trsCriticalPairOrigin_is_peak
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (o : TRSCriticalPairOrigin R) :
    OperatorKO7.Meta.Rewriting.Step (renameTRS R) o.source o.left ∧
      OperatorKO7.Meta.Rewriting.Step (renameTRS R) o.source o.right := by
  constructor
  · rw [o.source_eq, o.left_eq]
    exact Step.rootStep_step (renameTRS R) (renameRule_inl_mem o.leftRule_mem) o.unifier
  · rw [o.source_eq, o.right_eq]
    have hsub : Term.subtermAt
        (o.unifier • (renameRule Sum.inl o.leftRule).lhs) o.position =
        some (o.unifier • o.subterm) :=
      subtermAt_apply o.unifier _ _ _ o.subterm_eq
    have hunif : o.unifier • o.subterm =
        o.unifier • (renameRule Sum.inr o.rightRule).lhs :=
      unify_sound o.unify_eq
    have hroot : OperatorKO7.Meta.Rewriting.Step (renameTRS R)
        (o.unifier • o.subterm)
        (o.unifier • (renameRule Sum.inr o.rightRule).rhs) := by
      rw [hunif]
      exact Step.rootStep_step (renameTRS R) (renameRule_inr_mem o.rightRule_mem) o.unifier
    have hat := Step.at_pos (renameTRS R)
      (o.unifier • (renameRule Sum.inl o.leftRule).lhs) o.position
      (o.unifier • o.subterm) (o.unifier • (renameRule Sum.inr o.rightRule).rhs)
      hsub hroot
    rwa [replaceAt_apply o.unifier (renameRule Sum.inr o.rightRule).rhs
      (renameRule Sum.inl o.leftRule).lhs o.position o.subterm o.subterm_eq] at hat

/-- Every member of the library critical-pair enumeration has a typed origin
record naming its ordered source rules, a listed non-variable overlap position,
the successful unifier and the two emitted contracta. -/
theorem exists_trsCriticalPairOrigin_of_mem_criticalPairs
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {q : Term sigma (RenVar nu) × Term sigma (RenVar nu)}
    (hq : q ∈ criticalPairs R) :
    ∃ o : TRSCriticalPairOrigin R, o.left = q.1 ∧ o.right = q.2 := by
  rw [criticalPairs, List.mem_flatMap] at hq
  rcases hq with ⟨r1, hr1, hq⟩
  rw [List.mem_flatMap] at hq
  rcases hq with ⟨r2, hr2, hq⟩
  rw [overlapPairs, List.mem_filterMap] at hq
  rcases hq with ⟨pos, hpos, hpair⟩
  rcases overlapAt_eq_some hpair with
    ⟨sub, μ, hsub, hμ, hleft, hright⟩
  let o : TRSCriticalPairOrigin R :=
    { leftRule := r1
      rightRule := r2
      leftRule_mem := hr1
      rightRule_mem := hr2
      position := pos
      subterm := sub
      unifier := μ
      source := μ • (renameRule Sum.inl r1).lhs
      left := μ • (renameRule Sum.inl r1).rhs
      right := μ • Term.replaceAt (renameRule Sum.inl r1).lhs pos
        (renameRule Sum.inr r2).rhs
      position_nonvariable := hpos
      subterm_eq := hsub
      unify_eq := hμ
      source_eq := rfl
      left_eq := rfl
      right_eq := rfl }
  refine ⟨o, ?_, ?_⟩
  · exact hleft.symm
  · exact hright.symm

/-- Explicit first-order critical-pair list and completeness evidence relative to
the library's canonical `criticalPairs` enumeration. -/
structure TRSCriticalPairInput
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) where
  items : List (TRSCriticalPairOrigin R)
  complete : ∀ q ∈ criticalPairs R,
    ∃ item ∈ items, item.left = q.1 ∧ item.right = q.2

/-- The supplied completeness field is consumed to recover a genuine typed peak
for every member of the library critical-pair enumeration. -/
theorem TRSCriticalPairInput.covers_criticalPairs
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} (I : TRSCriticalPairInput R)
    {q : Term sigma (RenVar nu) × Term sigma (RenVar nu)}
    (hq : q ∈ criticalPairs R) :
    ∃ item ∈ I.items, item.left = q.1 ∧ item.right = q.2 ∧
      OperatorKO7.Meta.Rewriting.Step (renameTRS R) item.source item.left ∧
      OperatorKO7.Meta.Rewriting.Step (renameTRS R) item.source item.right := by
  rcases I.complete q hq with ⟨item, hmem, hl, hr⟩
  rcases trsCriticalPairOrigin_is_peak item with ⟨hleft, hright⟩
  exact ⟨item, hmem, hl, hr, hleft, hright⟩

/-- Finite semantic adapter for a selected first-order critical-pair slice. The
finite table represents only the supplied states; it does not claim to enumerate
the infinite term algebra. -/
structure TRSFiniteAdapter
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (α : Type w) [DecidableEq α] where
  table : RelationTable α
  realize : α → Term sigma (RenVar nu)
  realize_injective : Function.Injective realize
  step_sound : ∀ {a b}, table.Step a b →
    OperatorKO7.Meta.Rewriting.Step (renameTRS R) (realize a) (realize b)
  step_reflect : ∀ {a b},
    OperatorKO7.Meta.Rewriting.Step (renameTRS R) (realize a) (realize b) →
      table.Step a b
  reduction_closed : ∀ {a t},
    OperatorKO7.Meta.Rewriting.Step (renameTRS R) (realize a) t →
      ∃ b, realize b = t

/-- Finite-table reachability maps to rewrite-system reachability. -/
theorem TRSFiniteAdapter.reach_sound
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {α : Type w} [DecidableEq α]
    (A : TRSFiniteAdapter R α) {a b : α}
    (h : ReflTransGen A.table.Step a b) :
    OperatorKO7.Meta.Rewriting.StepStar (renameTRS R) (A.realize a) (A.realize b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (A.step_sound hbc)

/-- Every rewrite sequence starting from a represented state stays represented
and reflects to finite-table reachability. -/
theorem TRSFiniteAdapter.reach_reflect
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {α : Type w} [DecidableEq α]
    (A : TRSFiniteAdapter R α) {a : α} {t : Term sigma (RenVar nu)}
    (h : OperatorKO7.Meta.Rewriting.StepStar (renameTRS R) (A.realize a) t) :
    ∃ b, A.realize b = t ∧ ReflTransGen A.table.Step a b := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | @tail b c hab hbc ih =>
      rcases ih with ⟨x, hx, hax⟩
      have hstep : OperatorKO7.Meta.Rewriting.Step (renameTRS R) (A.realize x) c := by
        simpa [hx] using hbc
      rcases A.reduction_closed hstep with ⟨y, hy⟩
      have hxy : A.table.Step x y := A.step_reflect (by simpa [hy] using hstep)
      exact ⟨y, hy, hax.tail hxy⟩

/-- The finite table and represented rewrite relation have the same reachability. -/
theorem TRSFiniteAdapter.reach_iff
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {α : Type w} [DecidableEq α]
    (A : TRSFiniteAdapter R α) (a b : α) :
    ReflTransGen A.table.Step a b ↔
      OperatorKO7.Meta.Rewriting.StepStar (renameTRS R) (A.realize a) (A.realize b) := by
  constructor
  · exact A.reach_sound
  · intro h
    rcases A.reach_reflect h with ⟨c, hc, hac⟩
    have hcb : c = b := A.realize_injective hc
    simpa [hcb] using hac

/-- Finite-table joinability is equivalent to joinability of the represented
terms in the full renamed rewrite system. -/
theorem TRSFiniteAdapter.joinable_iff
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {α : Type w} [DecidableEq α]
    (A : TRSFiniteAdapter R α) (a b : α) :
    (∃ c, ReflTransGen A.table.Step a c ∧ ReflTransGen A.table.Step b c) ↔
      OperatorKO7.Meta.Rewriting.joinable (renameTRS R) (A.realize a) (A.realize b) := by
  constructor
  · rintro ⟨c, hac, hbc⟩
    exact ⟨A.realize c, A.reach_sound hac, A.reach_sound hbc⟩
  · rintro ⟨t, hat, hbt⟩
    rcases A.reach_reflect hat with ⟨ca, hca, hac⟩
    rcases A.reach_reflect hbt with ⟨cb, hcb, hbc⟩
    have hEq : ca = cb := A.realize_injective (hca.trans hcb.symm)
    exact ⟨ca, hac, by simpa [hEq] using hbc⟩

/-- A finite nonjoinability result transfers to the represented rewrite terms. -/
theorem TRSFiniteAdapter.nonjoinable_of_joinableB_false
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {α : Type w} [DecidableEq α]
    (A : TRSFiniteAdapter R α) {a b : α}
    (h : joinableB A.table a b = false) :
    ¬ OperatorKO7.Meta.Rewriting.joinable (renameTRS R) (A.realize a) (A.realize b) := by
  intro hj
  have htable : ∃ c, ReflTransGen A.table.Step a c ∧ ReflTransGen A.table.Step b c :=
    (A.joinable_iff a b).2 hj
  have htrue : joinableB A.table a b = true :=
    (joinableB_eq_true_iff A.table a b).2 htable
  simp [h] at htrue

/-- A critical-pair origin tied to three addresses in one finite semantic table. -/
structure AdaptedCriticalPair
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {α : Type w} [DecidableEq α]
    (A : TRSFiniteAdapter R α) where
  origin : TRSCriticalPairOrigin R
  sourceAddr : α
  leftAddr : α
  rightAddr : α
  source_realizes : A.realize sourceAddr = origin.source
  left_realizes : A.realize leftAddr = origin.left
  right_realizes : A.realize rightAddr = origin.right

/-- An adapted origin is a genuine semantic peak independently of finite
joinability computations. -/
theorem adaptedCriticalPair_is_genuine
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {α : Type w} [DecidableEq α]
    (A : TRSFiniteAdapter R α) (p : AdaptedCriticalPair A) :
    OperatorKO7.Meta.Rewriting.Step (renameTRS R)
        (A.realize p.sourceAddr) (A.realize p.leftAddr) ∧
      OperatorKO7.Meta.Rewriting.Step (renameTRS R)
        (A.realize p.sourceAddr) (A.realize p.rightAddr) := by
  have hp := trsCriticalPairOrigin_is_peak p.origin
  simpa [p.source_realizes, p.left_realizes, p.right_realizes] using hp

/-- If the finite table reports the adapted critical-pair reducts as
nonjoinable, they are nonjoinable in the renamed rewrite system as well. -/
theorem adaptedCriticalPair_nonjoinable_in_trs
    {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {α : Type w} [DecidableEq α]
    (A : TRSFiniteAdapter R α) (p : AdaptedCriticalPair A)
    (h : joinableB A.table p.leftAddr p.rightAddr = false) :
    ¬ OperatorKO7.Meta.Rewriting.joinable (renameTRS R) p.origin.left p.origin.right := by
  have hnj := A.nonjoinable_of_joinableB_false h
  simpa [p.left_realizes, p.right_realizes] using hnj

/-! ## Repair search -/

/-- Repair data with an explicit intervention enumeration. -/
structure RepairInput (B : Type v) (J : Type w) [DecidableEq B] [DecidableEq J] where
  interventions : Enumeration J
  bad : Finset B
  closes : J → Finset B
  price : J → Nat

/-- Universe-polymorphic finite argmin preserving the first minimum in list order. -/
def argminNat {A : Type u} (cost : A → Nat) : List A → Option A
  | [] => none
  | a :: as =>
      match argminNat cost as with
      | none => some a
      | some b => if cost a ≤ cost b then some a else some b

@[simp] theorem argminNat_eq_none_iff {A : Type u} (cost : A → Nat) (xs : List A) :
    argminNat cost xs = none ↔ xs = [] := by
  induction xs with
  | nil => simp [argminNat]
  | cons a as ih =>
      simp only [argminNat]
      cases argminNat cost as with
      | none => simp
      | some b =>
          by_cases hab : cost a ≤ cost b <;> simp [hab]

/-- Successful argmin membership and optimality over its explicit candidate list. -/
theorem argminNat_sound {A : Type u} (cost : A → Nat) :
    ∀ {xs : List A} {a : A}, argminNat cost xs = some a →
      a ∈ xs ∧ ∀ b ∈ xs, cost a ≤ cost b := by
  intro xs
  induction xs with
  | nil => simp [argminNat]
  | cons x xs ih =>
      intro a h
      simp only [argminNat] at h
      cases htail : argminNat cost xs with
      | none =>
          simp [htail] at h
          subst a
          have hxs : xs = [] := (argminNat_eq_none_iff cost xs).1 htail
          subst xs
          simp
      | some y =>
          have hy := ih htail
          by_cases hxy : cost x ≤ cost y
          · simp [htail, hxy] at h
            subst a
            refine ⟨by simp, ?_⟩
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact le_rfl
            · exact hxy.trans (hy.2 b hb)
          · simp [htail, hxy] at h
            subst a
            refine ⟨by simp [hy.1], ?_⟩
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact Nat.le_of_lt (Nat.lt_of_not_ge hxy)
            · exact hy.2 b hb

/-- Executable list-subset enumeration. -/
def listSubsets {A : Type u} : List A → List (List A)
  | [] => [[]]
  | a :: as =>
      let tail := listSubsets as
      tail ++ tail.map (fun ys => a :: ys)

/-- Filtering any predicate from a list produces one enumerated subset. -/
theorem filter_mem_listSubsets {A : Type u} (p : A → Bool) :
    ∀ xs : List A, xs.filter p ∈ listSubsets xs := by
  intro xs
  induction xs with
  | nil => simp [listSubsets]
  | cons a as ih =>
      simp only [List.filter_cons]
      by_cases h : p a = true
      · simp [h, listSubsets, ih]
      · have hf : p a = false := Bool.eq_false_of_not_eq_true h
        simp [hf, listSubsets, ih]

/-- Every intervention subset, generated from the explicit intervention list. -/
def allRepairSelections {B : Type v} {J : Type w} [DecidableEq B] [DecidableEq J]
    (I : RepairInput B J) : List (Finset J) :=
  (listSubsets I.interventions.items).map List.toFinset

instance repairCoverDecidable {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J] (I : RepairInput B J) (chosen : Finset J) :
    Decidable (IsRepairCover I.bad I.closes chosen) := by
  unfold IsRepairCover
  infer_instance

/-- Executable list of repair covers. -/
def repairCandidatesExec {B : Type v} {J : Type w} [DecidableEq B] [DecidableEq J]
    (I : RepairInput B J) : List (Finset J) :=
  (allRepairSelections I).filter fun chosen =>
    decide (IsRepairCover I.bad I.closes chosen)

/-- Every finite intervention set occurs in the explicit subset enumeration. -/
theorem mem_allRepairSelections {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J]
    (I : RepairInput B J) (chosen : Finset J) :
    chosen ∈ allRepairSelections I := by
  let xs := I.interventions.items.filter (fun j => decide (j ∈ chosen))
  have hxs : xs ∈ listSubsets I.interventions.items :=
    filter_mem_listSubsets (fun j => decide (j ∈ chosen)) I.interventions.items
  have hfin : xs.toFinset = chosen := by
    ext j
    simp [xs, I.interventions.complete j]
  rw [allRepairSelections, List.mem_map]
  exact ⟨xs, hxs, hfin⟩

@[simp] theorem mem_repairCandidatesExec_iff {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J]
    (I : RepairInput B J) (chosen : Finset J) :
    chosen ∈ repairCandidatesExec I ↔ IsRepairCover I.bad I.closes chosen := by
  simp [repairCandidatesExec, mem_allRepairSelections I chosen]

/-- Minimum-cardinality repair if one exists. -/
def minimumRepairCover? {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J] (I : RepairInput B J) : Option (Finset J) :=
  argminNat Finset.card (repairCandidatesExec I)

/-- Minimum-price repair if one exists. -/
def minimumPriceRepair? {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J] (I : RepairInput B J) : Option (Finset J) :=
  argminNat (repairCoverCost I.price) (repairCandidatesExec I)

/-- Returned cardinality optimizer is a globally minimum cover. -/
theorem minimumRepairCover?_sound_minimal {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J]
    (I : RepairInput B J) {chosen : Finset J}
    (h : minimumRepairCover? I = some chosen) :
    IsRepairCover I.bad I.closes chosen ∧
      ∀ other : Finset J, IsRepairCover I.bad I.closes other → chosen.card ≤ other.card := by
  have hs := argminNat_sound Finset.card h
  refine ⟨(mem_repairCandidatesExec_iff I chosen).1 hs.1, ?_⟩
  intro other hother
  exact hs.2 other ((mem_repairCandidatesExec_iff I other).2 hother)

/-- Returned price optimizer is a globally minimum declared-price cover. -/
theorem minimumPriceRepair?_sound_minimal {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J]
    (I : RepairInput B J) {chosen : Finset J}
    (h : minimumPriceRepair? I = some chosen) :
    IsRepairCover I.bad I.closes chosen ∧
      ∀ other : Finset J, IsRepairCover I.bad I.closes other →
        repairCoverCost I.price chosen ≤ repairCoverCost I.price other := by
  have hs := argminNat_sound (repairCoverCost I.price) h
  refine ⟨(mem_repairCandidatesExec_iff I chosen).1 hs.1, ?_⟩
  intro other hother
  exact hs.2 other ((mem_repairCandidatesExec_iff I other).2 hother)

/-- Cardinality search is empty exactly when no intervention subset covers the defects. -/
theorem minimumRepairCover?_eq_none_iff {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J] (I : RepairInput B J) :
    minimumRepairCover? I = none ↔
      ¬ ∃ chosen : Finset J, IsRepairCover I.bad I.closes chosen := by
  rw [minimumRepairCover?, argminNat_eq_none_iff]
  constructor
  · intro hempty hex
    rcases hex with ⟨chosen, hcover⟩
    have hmem := (mem_repairCandidatesExec_iff I chosen).2 hcover
    rw [hempty] at hmem
    simp at hmem
  · intro hnone
    apply List.eq_nil_iff_forall_not_mem.2
    intro chosen hmem
    exact hnone ⟨chosen, (mem_repairCandidatesExec_iff I chosen).1 hmem⟩

/-- Price search has the same exact coverability failure condition. -/
theorem minimumPriceRepair?_eq_none_iff {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J] (I : RepairInput B J) :
    minimumPriceRepair? I = none ↔
      ¬ ∃ chosen : Finset J, IsRepairCover I.bad I.closes chosen := by
  rw [minimumPriceRepair?, argminNat_eq_none_iff]
  constructor
  · intro hempty hex
    rcases hex with ⟨chosen, hcover⟩
    have hmem := (mem_repairCandidatesExec_iff I chosen).2 hcover
    rw [hempty] at hmem
    simp at hmem
  · intro hnone
    apply List.eq_nil_iff_forall_not_mem.2
    intro chosen hmem
    exact hnone ⟨chosen, (mem_repairCandidatesExec_iff I chosen).1 hmem⟩

/-- Agreement with the existing noncomputable cover number when the reference
`Fintype` is taken from the same explicit enumeration. -/
theorem minimumRepairCover?_card_eq_reference {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J]
    (I : RepairInput B J)
    (hcoverable : IsRepairCover I.bad I.closes
      (I.interventions.items.toFinset))
    {chosen : Finset J} (h : minimumRepairCover? I = some chosen) :
    letI : Fintype J := I.interventions.toFintype
    chosen.card = repairCoverNumber I.bad I.closes (by simpa using hcoverable) := by
  letI : Fintype J := I.interventions.toFintype
  have hmin := minimumRepairCover?_sound_minimal I h
  apply Nat.le_antisymm
  · obtain ⟨best, hbestMem, hbestEq⟩ :=
      Finset.exists_mem_eq_inf'
        (repairCandidates_nonempty (by simpa using hcoverable)) Finset.card
    have hbestCover : IsRepairCover I.bad I.closes best :=
      (mem_repairCandidates_iff I.bad I.closes best).1 hbestMem
    have hle := hmin.2 best hbestCover
    unfold repairCoverNumber
    rw [hbestEq]
    exact hle
  · exact repairCoverNumber_le_card (by simpa using hcoverable) hmin.1

/-- Price optimizer agrees with the existing weighted minimum under the same
explicit finite intervention universe. -/
theorem minimumPriceRepair?_cost_eq_reference {B : Type v} {J : Type w}
    [DecidableEq B] [DecidableEq J]
    (I : RepairInput B J)
    (hcoverable : IsRepairCover I.bad I.closes I.interventions.items.toFinset)
    {chosen : Finset J} (h : minimumPriceRepair? I = some chosen) :
    letI : Fintype J := I.interventions.toFintype
    repairCoverCost I.price chosen =
      minimumRepairCoverCost I.bad I.closes I.price (by simpa using hcoverable) := by
  letI : Fintype J := I.interventions.toFintype
  have hmin := minimumPriceRepair?_sound_minimal I h
  apply Nat.le_antisymm
  · obtain ⟨best, hbestMem, hbestEq⟩ :=
      Finset.exists_mem_eq_inf'
        (repairCandidates_nonempty (by simpa using hcoverable)) (repairCoverCost I.price)
    have hbestCover : IsRepairCover I.bad I.closes best :=
      (mem_repairCandidates_iff I.bad I.closes best).1 hbestMem
    have hle := hmin.2 best hbestCover
    unfold minimumRepairCoverCost
    rw [hbestEq]
    exact hle
  · exact minimumRepairCoverCost_le (by simpa using hcoverable) hmin.1

/-! ## Bounded witness rank -/

/-- Search grades `0,...,bound` and return the first successful grade. -/
def boundedWitnessRank? : Nat → (Nat → Bool) → Option Nat
  | 0, adequateB => if adequateB 0 then some 0 else none
  | bound + 1, adequateB =>
      match boundedWitnessRank? bound adequateB with
      | some n => some n
      | none => if adequateB (bound + 1) then some (bound + 1) else none

/-- Returned grades are inside the declared window. -/
theorem boundedWitnessRank?_le
    {bound n : Nat} {adequateB : Nat → Bool}
    (h : boundedWitnessRank? bound adequateB = some n) : n ≤ bound := by
  induction bound with
  | zero =>
      simp [boundedWitnessRank?] at h
      omega
  | succ bound ih =>
      cases hp : boundedWitnessRank? bound adequateB with
      | some k =>
          simp [boundedWitnessRank?, hp] at h
          subst n
          exact Nat.le_succ_of_le (ih hp)
      | none =>
          by_cases hnew : adequateB (bound + 1) = true
          · simp [boundedWitnessRank?, hp, hnew] at h
            subst n
            exact Nat.le_refl _
          · simp [boundedWitnessRank?, hp, hnew] at h

/-- Returned grades satisfy the executable adequacy predicate. -/
theorem boundedWitnessRank?_sound_bool
    {bound n : Nat} {adequateB : Nat → Bool}
    (h : boundedWitnessRank? bound adequateB = some n) : adequateB n = true := by
  induction bound with
  | zero =>
      by_cases h0 : adequateB 0 = true
      · simp [boundedWitnessRank?, h0] at h
        subst n
        exact h0
      · simp [boundedWitnessRank?, h0] at h
  | succ bound ih =>
      cases hp : boundedWitnessRank? bound adequateB with
      | some k =>
          simp [boundedWitnessRank?, hp] at h
          subst n
          exact ih hp
      | none =>
          by_cases hnew : adequateB (bound + 1) = true
          · simp [boundedWitnessRank?, hp, hnew] at h
            subst n
            exact hnew
          · simp [boundedWitnessRank?, hp, hnew] at h

/-- Failed bounded search means every grade in the window failed, and says
nothing about later grades. -/
theorem boundedWitnessRank?_eq_none_iff
    (bound : Nat) (adequateB : Nat → Bool) :
    boundedWitnessRank? bound adequateB = none ↔
      ∀ n, n ≤ bound → adequateB n = false := by
  induction bound with
  | zero => simp [boundedWitnessRank?]
  | succ bound ih =>
      cases hp : boundedWitnessRank? bound adequateB with
      | some n =>
          have hn := boundedWitnessRank?_sound_bool hp
          constructor
          · simp [boundedWitnessRank?, hp]
          · intro hall
            have hle := boundedWitnessRank?_le hp
            have := hall n (Nat.le_succ_of_le hle)
            simp [hn] at this
      | none =>
          have hprev := (ih).1 hp
          by_cases hnew : adequateB (bound + 1) = true
          · constructor
            · simp [boundedWitnessRank?, hp, hnew]
            · intro hall
              have := hall (bound + 1) (Nat.le_refl _)
              simp [hnew] at this
          · constructor
            · intro _ n hn
              by_cases heq : n = bound + 1
              · subst n
                exact Bool.eq_false_of_not_eq_true hnew
              · exact hprev n (by omega)
            · intro _
              simp [boundedWitnessRank?, hp, hnew]

/-- Every smaller grade failed. -/
theorem boundedWitnessRank?_minimal
    {bound n : Nat} {adequateB : Nat → Bool}
    (h : boundedWitnessRank? bound adequateB = some n) :
    ∀ j, j < n → adequateB j = false := by
  induction bound with
  | zero =>
      intro j hj
      have hn := boundedWitnessRank?_le h
      omega
  | succ bound ih =>
      cases hp : boundedWitnessRank? bound adequateB with
      | some k =>
          simp [boundedWitnessRank?, hp] at h
          subst n
          exact ih hp
      | none =>
          by_cases hnew : adequateB (bound + 1) = true
          · simp [boundedWitnessRank?, hp, hnew] at h
            subst n
            intro j hj
            have hprev := (boundedWitnessRank?_eq_none_iff bound adequateB).1 hp
            exact hprev j (by omega)
          · simp [boundedWitnessRank?, hp, hnew] at h

/-- Any successful bounded search for a decidable graded profile equals its
existing unbounded witness rank. -/
theorem boundedWitnessRank?_eq_witnessRank_of_some
    (G : GradedAdequacy) [DecidablePred G.adequate]
    {bound n : Nat}
    (h : boundedWitnessRank? bound (fun i => decide (G.adequate i)) = some n) :
    n = witnessRank G := by
  have hnAdeq : G.adequate n :=
    of_decide_eq_true (boundedWitnessRank?_sound_bool h)
  apply Nat.le_antisymm
  · by_contra hnot
    have hlt : witnessRank G < n := Nat.lt_of_not_ge hnot
    have hfail := boundedWitnessRank?_minimal h (witnessRank G) hlt
    have hgood : decide (G.adequate (witnessRank G)) = true := by
      simp [witnessRank_adequate G]
    simp [hgood] at hfail
  · exact witnessRank_le_of_adequate G hnAdeq

/-- Once the supplied bound reaches the true witness rank, search returns it. -/
theorem boundedWitnessRank?_eq_witnessRank
    (G : GradedAdequacy) [DecidablePred G.adequate]
    {bound : Nat} (hbound : witnessRank G ≤ bound) :
    boundedWitnessRank? bound (fun i => decide (G.adequate i)) = some (witnessRank G) := by
  by_cases hnone : boundedWitnessRank? bound (fun i => decide (G.adequate i)) = none
  · have hall := (boundedWitnessRank?_eq_none_iff bound
      (fun i => decide (G.adequate i))).1 hnone
    have hfail := hall (witnessRank G) hbound
    simp [witnessRank_adequate G] at hfail
  · rcases Option.ne_none_iff_exists'.mp hnone with ⟨n, hn⟩
    have heq := boundedWitnessRank?_eq_witnessRank_of_some G hn
    simpa [heq] using hn

/-- Successful bounded graded search gives adequacy and exact rank. -/
theorem boundedWitnessRank?_sound_graded
    (G : GradedAdequacy) [DecidablePred G.adequate]
    {bound n : Nat}
    (h : boundedWitnessRank? bound (fun i => decide (G.adequate i)) = some n) :
    G.adequate n ∧ witnessRank G = n := by
  have heq := boundedWitnessRank?_eq_witnessRank_of_some G h
  exact ⟨heq.symm ▸ witnessRank_adequate G, heq.symm⟩

/-! ## Required controls -/

/-- Complete empty enumeration. -/
def emptyEnumeration : Enumeration Empty where
  items := []
  nodup := by simp
  complete := by intro x; exact nomatch x

/-- Empty carrier relation. -/
def emptyTable : RelationTable Empty where
  explicit := emptyEnumeration
  stepB := fun x => nomatch x

/-- Singleton enumeration. -/
def unitEnumeration : Enumeration Unit where
  items := [()]
  nodup := by simp
  complete := by intro x; cases x; simp

/-- Singleton loop. -/
def singletonLoop : RelationTable Unit where
  explicit := unitEnumeration
  stepB := fun _ _ => true

/-- Singleton normal relation. -/
def singletonNormal : RelationTable Unit where
  explicit := unitEnumeration
  stepB := fun _ _ => false

/-- Same relation, first auxiliary repair price. -/
def singletonRepairCheap : RepairInput Unit Unit where
  interventions := unitEnumeration
  bad := {()}
  closes := fun _ => {()}
  price := fun _ => 0

/-- Same relation, different auxiliary repair price. -/
def singletonRepairCostly : RepairInput Unit Unit where
  interventions := unitEnumeration
  bad := {()}
  closes := fun _ => {()}
  price := fun _ => 1

/-- Same relation, but the available intervention covers no defect. -/
def singletonRepairUncovering : RepairInput Unit Unit where
  interventions := unitEnumeration
  bad := {()}
  closes := fun _ => ∅
  price := fun _ => 0

/-- Same relation table does not determine repair prices. -/
theorem identical_relation_different_auxiliary_price :
    singletonNormal = singletonNormal ∧
      singletonRepairCheap.price () ≠ singletonRepairCostly.price () := by
  refine ⟨rfl, ?_⟩
  simp [singletonRepairCheap, singletonRepairCostly]

/-- Same relation table does not determine repair coverage. -/
theorem identical_relation_different_auxiliary_coverage :
    singletonNormal = singletonNormal ∧
      singletonRepairCheap.closes () ≠ singletonRepairUncovering.closes () := by
  refine ⟨rfl, ?_⟩
  simp [singletonRepairCheap, singletonRepairUncovering]

/-- Two adequacy predicates attached to the same relation can have different
bounded witness ranks. -/
def adequateAtZero (n : Nat) : Bool := decide (0 ≤ n)

def adequateAtTwo (n : Nat) : Bool := decide (2 ≤ n)

/-- Relation data alone do not determine a witness-rank coordinate or its search
bound. -/
theorem identical_relation_different_adequacy_and_bound :
    singletonNormal = singletonNormal ∧
      boundedWitnessRank? 0 adequateAtZero = some 0 ∧
      boundedWitnessRank? 1 adequateAtTwo = none ∧
      boundedWitnessRank? 2 adequateAtTwo = some 2 := by
  refine ⟨rfl, ?_⟩
  decide

/-- Complete enumeration of `Fin 3`. -/
def fin3Enumeration : Enumeration (Fin 3) where
  items := [0, 1, 2]
  nodup := by decide
  complete := by intro x; fin_cases x <;> decide

/-- Three-node chain. -/
def chain3 : RelationTable (Fin 3) where
  explicit := fin3Enumeration
  stepB := fun a b => decide ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2))

/-- Three-node fork with two terminal successors. -/
def fork3 : RelationTable (Fin 3) where
  explicit := fin3Enumeration
  stepB := fun a b => decide (a = 0 ∧ (b = 1 ∨ b = 2))

@[simp] theorem singletonNormal_has_one_terminal :
    terminalMultiplicity singletonNormal () = 1 := by decide

@[simp] theorem singletonLoop_has_no_terminal :
    terminalMultiplicity singletonLoop () = 0 := by decide

@[simp] theorem chain3_source_confluent :
    sourceConfluentB chain3 0 = true := by decide

@[simp] theorem fork3_source_not_confluent :
    sourceConfluentB fork3 0 = false := by decide

@[simp] theorem rank_zero_found :
    boundedWitnessRank? 4 (fun n => decide (0 ≤ n)) = some 0 := by decide

@[simp] theorem bounded_rank_exhausted :
    boundedWitnessRank? 4 (fun n => decide (7 ≤ n)) = none := by decide

end OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms
