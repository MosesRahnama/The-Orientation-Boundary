import OperatorKO7.Kernel
import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.BoundaryGeneral.TwoVoidBoundary

set_option autoImplicit false

/-!
# Equality-test instance: content and the two argument places

This module isolates the KO7 root-Step instance from the general observation
boundary. The relation here is the full unguarded `OperatorKO7.Step` at the
root, not `SafeStep`, a contextual closure, or any difference guard.
Graph: notes/universal-roadmap/UNIVERSAL-OBSERVATION-PROOF-GRAPH.md, V1_L6.
-/

namespace OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest

open OperatorKO7 Trace
open OperatorKO7.Meta.BoundaryObserver.MergedPair

/-- An occurrence of a term at either argument place of `eqW`. -/
abbrev EqualityOccurrence := Trace × Fin 2

/-- The argument content, independent of its occurrence place. -/
def equalityContent : EqualityOccurrence → Trace := Prod.fst

/-- The argument place, independent of its content. -/
def equalityPlace : EqualityOccurrence → Fin 2 := Prod.snd

/-- The left argument occurrence of `eqW a a`. -/
def firstOccurrence (a : Trace) : EqualityOccurrence := (a, 0)

/-- The right argument occurrence of `eqW a a`. -/
def secondOccurrence (a : Trace) : EqualityOccurrence := (a, 1)

/-- The two argument occurrences have different places for every term. -/
theorem equality_places_distinct (a : Trace) :
    equalityPlace (firstOccurrence a) ≠ equalityPlace (secondOccurrence a) := by
  change (0 : Fin 2) ≠ 1
  decide

/-- The two argument occurrences are unequal as occurrences for every term. -/
theorem equality_occurrences_distinct (a : Trace) :
    firstOccurrence a ≠ secondOccurrence a := by
  intro h
  exact equality_places_distinct a (congrArg equalityPlace h)

/-- The occurrences of `a` have one content value for every term. -/
theorem equality_occurrences_same_content (a : Trace) :
    equalityContent (firstOccurrence a) = equalityContent (secondOccurrence a) := rfl

/-- Every term `a` yields a merged pair in the content observer on
`Trace × Fin 2`, not two different syntactic term values. -/
theorem equality_occurrences_merged (a : Trace) :
    IsMergedPair equalityContent (firstOccurrence a) (secondOccurrence a) :=
  ⟨equality_occurrences_distinct a, equality_occurrences_same_content a⟩

/-! ## The two full root-Step rules on occurrence contents -/

/-- At the root, the reflexive equality rule gives `void` exactly for
equal term contents. Argument place does not enter this condition. -/
theorem eqW_root_refl_iff_content_eq (o₀ o₁ : EqualityOccurrence) :
    Step (eqW (equalityContent o₀) (equalityContent o₁)) void ↔
      equalityContent o₀ = equalityContent o₁ := by
  constructor
  · intro h
    have root_eq : ∀ a b : Trace, Step (eqW a b) void → a = b := by
      intro a b hab
      cases hab
      rfl
    exact root_eq (equalityContent o₀) (equalityContent o₁) h
  · intro h
    rw [h]
    exact Step.R_eq_refl (equalityContent o₁)

/-- The difference rule of the full root relation has no side condition:
it applies to every two contents, including equal contents. -/
theorem eqW_root_diff_unconditional (o₀ o₁ : EqualityOccurrence) :
    Step (eqW (equalityContent o₀) (equalityContent o₁))
      (integrate (merge (equalityContent o₀) (equalityContent o₁))) :=
  Step.R_eq_diff (equalityContent o₀) (equalityContent o₁)

/-- An explicit place reading can distinguish the two occurrences even though
the content reading cannot; this place reading is not a guard on `Step`. -/
def sameArgumentPlace (o₀ o₁ : EqualityOccurrence) : Bool :=
  decide (equalityPlace o₀ = equalityPlace o₁)

/-- The finite place reading distinguishes the two copies of every term. -/
theorem equality_place_reading_separates (a : Trace) :
    sameArgumentPlace (firstOccurrence a) (secondOccurrence a) = false ∧
    sameArgumentPlace (firstOccurrence a) (firstOccurrence a) = true := by
  constructor <;>
    simp [sameArgumentPlace, equalityPlace, firstOccurrence, secondOccurrence]

/-- On the actual equal-content, different-place pair, both one-step
full root reductions of `eqW a a` are available. Neither is a contextual step. -/
theorem equality_root_both_rules (a : Trace) :
    Step (eqW (equalityContent (firstOccurrence a))
      (equalityContent (secondOccurrence a))) void ∧
    Step (eqW (equalityContent (firstOccurrence a))
      (equalityContent (secondOccurrence a)))
      (integrate (merge (equalityContent (firstOccurrence a))
        (equalityContent (secondOccurrence a)))) :=
  ⟨Step.R_eq_refl a, Step.R_eq_diff a a⟩

/-- The difference root rule fires at every choice of argument places,
including identical places. No syntactic inequality test is asserted. -/
theorem eqW_root_diff_all_places (a : Trace) (i j : Fin 2) :
    Step (eqW (equalityContent (a, i)) (equalityContent (a, j)))
      (integrate (merge a a)) :=
  Step.R_eq_diff a a

/-- Explicit control: the difference root rule also fires when the two
argument places are equal. -/
theorem eqW_root_diff_equal_place (a : Trace) (i : Fin 2) :
    Step (eqW (equalityContent (a, i)) (equalityContent (a, i)))
      (integrate (merge a a)) :=
  eqW_root_diff_all_places a i i

/-- The occurrence and the two rule conclusions are established together,
with different places but identical term contents at the root. -/
theorem equality_occurrence_rule_bundle (a : Trace) :
    IsMergedPair equalityContent (firstOccurrence a) (secondOccurrence a) ∧
    sameArgumentPlace (firstOccurrence a) (secondOccurrence a) = false ∧
    Step (eqW a a) void ∧ Step (eqW a a) (integrate (merge a a)) :=
  ⟨equality_occurrences_merged a, (equality_place_reading_separates a).1,
    Step.R_eq_refl a, Step.R_eq_diff a a⟩

end OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest

/-! The historical theorem keeps its original fully qualified name in
the rewriting instance, rather than in the mathematics-only merged-pair core.
The corresponding original declaration must be deleted from MergedPair.lean
by its owning import-split worker before these modules are compiled together. -/
namespace OperatorKO7.Meta.BoundaryObserver.MergedPair

open OperatorKO7.Meta.BoundaryGeneral.TwoVoidBoundary

/-- The frame and active occurrences of `void` form a merged pair of the
value observer. Its original namespace and declaration name are preserved. -/
theorem isMergedPair_void_occurrences : IsMergedPair voidValue voidFrame voidActive :=
  ⟨voidFrame_ne_voidActive, voidValue_eq⟩

/-- Example 4.6: the occurrences of the one-point content have one content,
and the place observer is a bijection onto the two roles. Original public
namespace, name and type are preserved in the rewriting instance. -/
theorem unit_occurrences :
    (∀ o o' : OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance.Occ Unit,
      o.1 = o'.1) ∧
    Function.Bijective (fun o :
      OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance.Occ Unit => o.2) := by
  refine ⟨fun o o' => Subsingleton.elim _ _, ?_, ?_⟩
  · rintro ⟨⟨⟩, r⟩ ⟨⟨⟩, r'⟩ h
    exact congrArg (Prod.mk ()) h
  · intro r
    exact ⟨((), r), rfl⟩

end OperatorKO7.Meta.BoundaryObserver.MergedPair
