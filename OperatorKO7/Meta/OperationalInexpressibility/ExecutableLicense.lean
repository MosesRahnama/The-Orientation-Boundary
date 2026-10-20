import OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel

/-!
# Executable licensing on explicit enumerations

Given an explicit complete enumeration of the source, the license criterion, observer
refinement, and the target-kernel partition are computed by finite loops. Each executable
definition carries a soundness and completeness theorem against the propositional notion, and the
collision search returns a certificate pair whenever the license fails. Controls: the empty
carrier, the one-point carrier, and the parity of two Boolean coordinates.

Relation: equality of observer and target outputs on enumerated states.
Property: decision procedures with soundness and completeness theorems.
Trust: kernel only; the fixtures are evaluated by `decide`.
Scope: any source type with decidable equality and an explicit complete enumeration; observation
and target types with decidable equality.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.ExecutableLicense

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel

universe u v w z

variable {X : Type u} {Q : Type v} {V : Type w} [DecidableEq X] [DecidableEq Q] [DecidableEq V]

/-! ## License check -/

/-- Executable license check: every enumerated pair with equal observations has equal targets. -/
def licensedB (E : Enumeration X) (q : X → Q) (P : X → V) : Bool :=
  decide (∀ x ∈ E.items, ∀ y ∈ E.items, q x = q y → P x = P y)

/-- The executable check decides the license criterion. -/
theorem licensedB_eq_true_iff (E : Enumeration X) (q : X → Q) (P : X → V) :
    licensedB E q P = true ↔ Licensed q P := by
  unfold licensedB
  rw [decide_eq_true_iff]
  exact ⟨fun h x y => h x (E.complete x) y (E.complete y), fun h x _ y _ => h x y⟩

/-- A negative answer of the check is exactly failure of the license. -/
theorem licensedB_eq_false_iff (E : Enumeration X) (q : X → Q) (P : X → V) :
    licensedB E q P = false ↔ ¬ Licensed q P := by
  rw [← licensedB_eq_true_iff]
  cases licensedB E q P <;> simp

/-! ## Refinement check -/

/-- Executable refinement check: every enumerated pair identified by the first observer is
identified by the second. -/
def observerRefinesB {Q₂ : Type z} [DecidableEq Q₂] (E : Enumeration X) (q₁ : X → Q)
    (q₂ : X → Q₂) : Bool :=
  decide (∀ x ∈ E.items, ∀ y ∈ E.items, q₁ x = q₁ y → q₂ x = q₂ y)

/-- The executable refinement check decides observer refinement. -/
theorem observerRefinesB_eq_true_iff {Q₂ : Type z} [DecidableEq Q₂] (E : Enumeration X)
    (q₁ : X → Q) (q₂ : X → Q₂) :
    observerRefinesB E q₁ q₂ = true ↔ ObserverRefines q₁ q₂ := by
  unfold observerRefinesB
  rw [decide_eq_true_iff]
  constructor
  · intro h x y hxy
    exact h x (E.complete x) y (E.complete y) hxy
  · intro h x _ y _ hxy
    exact h hxy

/-! ## Collision search -/

/-- The first enumerated colliding pair, when one exists. -/
def unlicensedWitness? (E : Enumeration X) (q : X → Q) (P : X → V) : Option (X × X) :=
  (E.items.flatMap fun x => E.items.map fun y => (x, y)).find?
    fun p => decide (q p.1 = q p.2 ∧ P p.1 ≠ P p.2)

/-- Every returned pair is a collision of the observer with the target. -/
theorem unlicensedWitness?_sound (E : Enumeration X) (q : X → Q) (P : X → V) {x y : X}
    (h : unlicensedWitness? E q P = some (x, y)) :
    OperationallyInexpressibleAt q P x y := by
  unfold unlicensedWitness? at h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact hp

/-- The search returns nothing exactly when the observer licenses the target. -/
theorem unlicensedWitness?_eq_none_iff (E : Enumeration X) (q : X → Q) (P : X → V) :
    unlicensedWitness? E q P = none ↔ Licensed q P := by
  unfold unlicensedWitness?
  rw [List.find?_eq_none]
  constructor
  · intro h x y hxy
    by_contra hne
    have hmem : (x, y) ∈ E.items.flatMap (fun x => E.items.map fun y => (x, y)) :=
      List.mem_flatMap.2 ⟨x, E.complete x, List.mem_map.2 ⟨y, E.complete y, rfl⟩⟩
    exact h (x, y) hmem (decide_eq_true ⟨hxy, hne⟩)
  · intro h p _ hp
    obtain ⟨hq, hP⟩ := of_decide_eq_true hp
    exact hP (h p.1 p.2 hq)

/-! ## Target-kernel partition -/

/-- The target-kernel classes: one list of enumerated states for each attained target value, in
order of first appearance. -/
def targetKernelClasses (E : Enumeration X) (P : X → V) : List (List X) :=
  (E.items.map P).dedup.map fun v => E.items.filter fun x => P x = v

/-- Each class is one target fiber, every state lies in its class, and the number of classes is
the number of attained target values. -/
theorem targetKernelClasses_spec (E : Enumeration X) (P : X → V) :
    (∀ c ∈ targetKernelClasses E P, ∃ x₀ : X, ∀ y, y ∈ c ↔ P y = P x₀) ∧
      (∀ x : X, ∃ c ∈ targetKernelClasses E P, x ∈ c) ∧
      (targetKernelClasses E P).length = (E.items.map P).dedup.length := by
  refine ⟨?_, ?_, List.length_map _⟩
  · intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hc
    obtain ⟨x₀, _, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hv)
    refine ⟨x₀, fun y => ?_⟩
    simp [List.mem_filter, E.complete y]
  · intro x
    refine ⟨E.items.filter fun y => P y = P x, ?_, ?_⟩
    · exact List.mem_map.2 ⟨P x, List.mem_dedup.2 (List.mem_map.2 ⟨x, E.complete x, rfl⟩), rfl⟩
    · simp [List.mem_filter, E.complete x]

/-! ## Controls -/

/-- The enumeration of the empty carrier. -/
def emptyEnumeration : Enumeration Empty :=
  ⟨[], List.nodup_nil, fun x => x.elim⟩

/-- On the empty carrier every target is licensed. -/
theorem licensedB_emptyEnumeration (q : Empty → Q) (P : Empty → V) :
    licensedB emptyEnumeration q P = true :=
  (licensedB_eq_true_iff _ _ _).2 fun x => x.elim

/-- The enumeration of the one-point carrier. -/
def unitEnumeration : Enumeration Unit :=
  ⟨[()], List.nodup_singleton (), fun _ => List.mem_singleton.2 rfl⟩

/-- On the one-point carrier every target is licensed. -/
theorem licensedB_unitEnumeration (q : Unit → Q) (P : Unit → V) :
    licensedB unitEnumeration q P = true :=
  (licensedB_eq_true_iff _ _ _).2 fun x y _ => by cases x; cases y; rfl

/-- The enumeration of two Boolean coordinates. -/
def boolPairEnumeration : Enumeration (Bool × Bool) :=
  ⟨[(false, false), (false, true), (true, false), (true, true)], by decide,
    fun p => by rcases p with ⟨a, b⟩; cases a <;> cases b <;> decide⟩

/-- Parity of two Boolean coordinates. -/
def parityTarget (x : Bool × Bool) : Bool :=
  xor x.1 x.2

/-- **Parity fixture.** The first coordinate does not license parity and the search returns the
collision of `(false, false)` and `(false, true)`; the identity observer licenses parity. -/
theorem parity_fixture :
    licensedB boolPairEnumeration Prod.fst parityTarget = false ∧
      unlicensedWitness? boolPairEnumeration Prod.fst parityTarget =
        some ((false, false), (false, true)) ∧
      licensedB boolPairEnumeration (fun x : Bool × Bool => x) parityTarget = true := by
  decide

end OperatorKO7.Meta.OperationalInexpressibility.ExecutableLicense
