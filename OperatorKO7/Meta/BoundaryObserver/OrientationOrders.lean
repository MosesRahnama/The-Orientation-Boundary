import OperatorKO7.Meta.BoundaryObserver.RecursorDecidability
import OperatorKO7.Kernel

set_option autoImplicit false

/-!
# Orientation obstruction over arbitrary well-founded orders

Graph: BOUNDARY-THEOREM-PROOF-GRAPH.md, expansion E3.
The relation concerns RecursorDecidability.Pass on the model
Trace × ℕ, not the contextual term-rewriting relation.
The orientation premise is stated for every pass, with the
original content map and no restriction on the measure's codomain.
The principal obstruction already holds for every irreflexive
relation, without well-foundedness.
Unit 1 is kernel-validated; Unit 2 adds the strict-order, universe and criterion clauses.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.BoundaryObserver.OrientationOrders

open OperatorKO7.Meta.BoundaryObserver.MergedPair
open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability

/-- The E3 goal quantifies over every well-founded relation and every orienting measure. -/
def OrientationOrdersGoal : Prop :=
  ∀ (α : Type) (r : α → α → Prop), WellFounded r →
    ∀ (M : Trace × ℕ → α),
      (∀ x y, Pass x y → r (M y) (M x)) →
        ¬ Determines content M

/-!
## Unit 1: the generalized orientation obstruction

The actual pass from (void, 1) to (void, 0) is
INDEPENDENTLY_PROVED by the definition of Pass.
The content equality on that pass is DERIVED_FROM_CERTIFIED_STRUCTURE
using the donor RecursorDecidability.content.
The orientation and determination premises are ORIGINAL_FINAL_ASSUMPTION.
Irreflexivity is proved from the given well-founded relation.
-/

/-- Every well-founded relation excludes a self-edge. -/
private theorem irrefl_of_wellFounded {α : Type} {r : α → α → Prop}
    (hw : WellFounded r) (x : α) : ¬ r x x := by
  have hx : Acc r x := hw.apply x
  induction hx with
  | intro a _ ih =>
    exact fun haa => ih a haa haa

/-- No measure decreasing along every pass can factor through unchanged content for an irreflexive target relation. -/
theorem no_content_orientation_of_irrefl {α : Type} (r : α → α → Prop)
    (hirr : ∀ a : α, ¬ r a a)
    (M : Trace × ℕ → α)
    (hM : ∀ x y, Pass x y → r (M y) (M x)) :
    ¬ Determines content M := by
  intro hdet
  have hdrop : r (M (void, 0)) (M (void, 1)) :=
    hM (void, 1) (void, 0) ⟨rfl, rfl⟩
  have heq : M (void, 1) = M (void, 0) :=
    hdet (void, 1) (void, 0) rfl
  rw [heq] at hdrop
  exact hirr _ hdrop

/-- E3: every strictly decreasing measure into any well-founded order needs information beyond content. -/
theorem orientationOrdersGoal : OrientationOrdersGoal := by
  intro α r hw M hM
  exact no_content_orientation_of_irrefl r
    (irrefl_of_wellFounded hw) M hM

/-- The counter supplies a genuine orientation, so the impossibility is non-vacuous. -/
theorem natural_orientation_exists :
    (∀ x y : Trace × ℕ, Pass x y → counter y < counter x) ∧
      ¬ Determines (content (T := Trace)) (counter (T := Trace)) :=
  ⟨counter_orients, @counter_not_content_determined Trace ⟨void⟩⟩


/-!
## Unit 2: strict orders, every universe and the exact criterion

The orientation and determination premises are ORIGINAL_FINAL_ASSUMPTION.
Irreflexivity is DERIVED_FROM_CERTIFIED_STRUCTURE through `WellFounded.isIrrefl`
or `IsStrictOrder`. The adjacent pass and the equal content are
INDEPENDENTLY_PROVED by the definitions of `Pass` and `content`.
The criterion states that the obstruction holds exactly for irreflexive relations.
-/

universe u

/-- A map decreases along every recursor pass in the given codomain relation. -/
def PassDecreases {A : Type u} (r : A → A → Prop) (M : Trace × ℕ → A) : Prop :=
  ∀ x y, Pass x y → r (M y) (M x)

/-- A decreasing map into an irreflexive relation separates every two adjacent counters. -/
theorem adjacent_values_ne {A : Type u} (r : A → A → Prop)
    (hirr : ∀ a, ¬ r a a) (M : Trace × ℕ → A) (hM : PassDecreases r M)
    (R : Trace) (k : ℕ) : M (R, k + 1) ≠ M (R, k) := by
  intro heq
  have hstep : r (M (R, k)) (M (R, k + 1)) := hM (R, k + 1) (R, k) ⟨rfl, rfl⟩
  rw [heq] at hstep
  exact hirr _ hstep

/-- Irreflexivity of the codomain relation excludes content determination, in every universe. -/
theorem irreflexive_measure_not_content_determined {A : Type u} (r : A → A → Prop)
    (hirr : ∀ a, ¬ r a a) (M : Trace × ℕ → A) (hM : PassDecreases r M) :
    ¬ Determines content M := by
  intro h
  exact adjacent_values_ne r hirr M hM void 0 (h (void, 1) (void, 0) rfl)

/-- A content-determined decreasing map exists exactly when the relation has a reflexive point. -/
theorem content_determined_decreasing_exists_iff {A : Type u} (r : A → A → Prop) :
    (∃ M : Trace × ℕ → A, Determines content M ∧ PassDecreases r M) ↔
      ∃ a : A, r a a := by
  constructor
  · rintro ⟨M, hcontent, hM⟩
    refine ⟨M (void, 0), ?_⟩
    have hstep : r (M (void, 0)) (M (void, 1)) := hM (void, 1) (void, 0) ⟨rfl, rfl⟩
    have heq : M (void, 1) = M (void, 0) := hcontent (void, 1) (void, 0) rfl
    rw [heq] at hstep
    exact hstep
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, fun _ _ _ => rfl, fun _ _ _ => ha⟩

/-- The universal obstruction for a relation is equivalent to its irreflexivity. -/
theorem measure_obstruction_iff_irreflexive {A : Type u} (r : A → A → Prop) :
    (∀ M : Trace × ℕ → A, PassDecreases r M → ¬ Determines content M) ↔
      ∀ a : A, ¬ r a a := by
  constructor
  · intro h a ha
    exact h (fun _ => a) (fun _ _ _ => ha) (fun _ _ _ => rfl)
  · intro hirr M hM
    exact irreflexive_measure_not_content_determined r hirr M hM

/-- A well-founded codomain relation excludes content-determined decreasing maps in every universe. -/
theorem wellFounded_measure_not_content_determined {A : Type u} (r : A → A → Prop)
    (hwf : WellFounded r) (M : Trace × ℕ → A) (hM : PassDecreases r M) :
    ¬ Determines content M := by
  letI : IsIrrefl A r := hwf.isIrrefl
  exact irreflexive_measure_not_content_determined r (fun a => irrefl a) M hM

/-- Every strict codomain order excludes content-determined decreasing maps. -/
theorem strictOrder_measure_not_content_determined {A : Type u} (r : A → A → Prop)
    [IsStrictOrder A r] (M : Trace × ℕ → A) (hM : PassDecreases r M) :
    ¬ Determines content M :=
  irreflexive_measure_not_content_determined r (fun a => irrefl a) M hM

/-- The full E3 statement: well-founded relations and strict orders in every universe,
the exact irreflexivity criterion, and the reflexive-point converse. -/
def OrientationOrdersFullGoal : Prop :=
  (∀ (A : Type u) (r : A → A → Prop), WellFounded r →
    ∀ M : Trace × ℕ → A, PassDecreases r M → ¬ Determines content M) ∧
  (∀ (A : Type u) (r : A → A → Prop), IsStrictOrder A r →
    ∀ M : Trace × ℕ → A, PassDecreases r M → ¬ Determines content M) ∧
  (∀ (A : Type u) (r : A → A → Prop),
    (∀ M : Trace × ℕ → A, PassDecreases r M → ¬ Determines content M) ↔ ∀ a : A, ¬ r a a) ∧
  (∀ (A : Type u) (r : A → A → Prop),
    (∃ M : Trace × ℕ → A, Determines content M ∧ PassDecreases r M) ↔ ∃ a : A, r a a)

/-- The recursor passes satisfy every clause of the full E3 statement. -/
theorem orientationOrdersFullGoal : OrientationOrdersFullGoal.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A r hwf M hM
    exact wellFounded_measure_not_content_determined r hwf M hM
  · intro A r hstrict M hM
    exact strictOrder_measure_not_content_determined r M hM
  · intro A r
    exact measure_obstruction_iff_irreflexive r
  · intro A r
    exact content_determined_decreasing_exists_iff r

/-- The counter decreases along every pass for the strict order on the naturals and is not
determined by the content; the strict-order clause is therefore not vacuous. -/
theorem counter_strictOrder_control :
    PassDecreases (fun a b : ℕ => a < b) (counter (T := Trace)) ∧
      ¬ Determines (content (T := Trace)) (counter (T := Trace)) :=
  ⟨counter_orients, @counter_not_content_determined Trace ⟨void⟩⟩

/-- The reflexive relation on Unit admits a content-determined decreasing map, so the
irreflexivity premise of the criterion is load-bearing. -/
theorem reflexive_relation_control :
    ∃ M : Trace × ℕ → Unit, Determines content M ∧ PassDecreases (fun _ _ : Unit => True) M :=
  (content_determined_decreasing_exists_iff (fun _ _ : Unit => True)).2 ⟨(), trivial⟩

end OperatorKO7.Meta.BoundaryObserver.OrientationOrders
