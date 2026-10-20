import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Data.Set.Disjoint

/-!
# Rule-invariant Galois connection (generic carrier)

For any rule-indexed relation, rule families and invariant families determine
each other by preservation. The two preservation maps form an antitone Galois
connection, their composites are idempotent closure operators, and deleting
from a requested family the rules that fail a requested invariant family gives
the greatest preserving subfamily and the least exclusion. This module is the
carrier of Theorem `thm:rule-invariant-galois` of the Operational
Inexpressibility paper.

Module boundary: this module imports two Mathlib order and set modules and no
OperatorKO7 module. It imports none of the modules that define the concrete
kernel, its guarded relation, the dependency-pair development, or the recursor
trace (Remark `rem:import-independence`).

Namespace: the declarations live in
`OperatorKO7.Meta.OperationalInexpressibility.DynamicLicenseGalois`, the
namespace of the module that held them before the split, so every full name
cited in the paper and the claim-to-code table is unchanged. The module
`DynamicLicenseGalois.lean` imports this module and keeps the KO7 positional
instances.

Relation: an arbitrary rule-indexed relation `step : Rule → X → X → Prop`.
Closure: one step of each rule. Strategy: not applicable. Trust: every
declaration is axiom-free or within `propext`, `Classical.choice`, `Quot.sound`;
`Classical.choice` enters only through the partition proof.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DynamicLicenseGalois

universe u v

/-- A rule preserves a unary predicate along every step that it generates.

Proves: nothing (definition); `RulePreserves step r P` holds iff every
`step r`-edge from a `P`-state ends in a `P`-state.
Does not prove: preservation along the reflexive-transitive closure of the
union of several rules.
Relation: `step r`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary `Rule : Type u` and `X : Type v`. -/
def RulePreserves {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (r : Rule) (P : X → Prop) : Prop :=
  ∀ ⦃x y⦄, step r x y → P x → P y

/-- Predicates preserved by every rule in a selected family (the paper's
`Inv(S)`).

Proves: nothing (definition).
Does not prove: that the family is closed under any logical connective.
Relation: `step r` for `r ∈ S`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
def preservedPredicates {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (S : Set Rule) : Set (X → Prop) :=
  {P | ∀ r ∈ S, RulePreserves step r P}

/-- Rules preserving every predicate in a specified family (the paper's
`Rules(F)`).

Proves: nothing (definition).
Does not prove: that the selected rules preserve predicates outside `F`.
Relation: `step r` for every rule `r`. Closure: one step. Strategy: not
applicable. Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
def preservingRules {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (F : Set (X → Prop)) : Set Rule :=
  {r | ∀ P ∈ F, RulePreserves step r P}

/-- Proves: membership in `preservedPredicates step S` unfolds to preservation
by every rule of `S`.
Does not prove: anything beyond the definitional unfolding.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
@[simp] theorem mem_preservedPredicates_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (S : Set Rule) (P : X → Prop) :
    P ∈ preservedPredicates step S ↔
      ∀ r ∈ S, RulePreserves step r P :=
  Iff.rfl

/-- Proves: membership in `preservingRules step F` unfolds to preservation of
every predicate of `F`.
Does not prove: anything beyond the definitional unfolding.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
@[simp] theorem mem_preservingRules_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (r : Rule) :
    r ∈ preservingRules step F ↔
      ∀ P ∈ F, RulePreserves step r P :=
  Iff.rfl

/-- The defining rule-family/predicate-family antitone Galois law.

Proves: `S ⊆ Rules(F) ↔ F ⊆ Inv(S)` for every rule family `S` and predicate
family `F`.
Does not prove: any statement about confluence or termination of `step`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem rule_le_preservingRules_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (S : Set Rule) (F : Set (X → Prop)) :
    S ⊆ preservingRules step F ↔ F ⊆ preservedPredicates step S := by
  constructor
  · intro h P hP r hr
    exact h hr P hP
  · intro h r hr P hP
    exact h hP r hr

/-- The two antitone maps form a Galois connection after reversing the
predicate-family order.

Proves: `GaloisConnection (toDual ∘ Inv) (Rules ∘ ofDual)` in the Mathlib sense.
Does not prove: that either map is surjective or injective.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`, `Quot.sound`. Scope: arbitrary rule and carrier types. -/
theorem rulePredicate_galoisConnection
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop) :
    GaloisConnection
      (fun S : Set Rule => OrderDual.toDual (preservedPredicates step S))
      (fun F : OrderDual (Set (X → Prop)) =>
        preservingRules step (OrderDual.ofDual F)) :=
  fun S F => (rule_le_preservingRules_iff step S (OrderDual.ofDual F)).symm

/-- Proves: `Inv` is antitone (a larger rule family preserves fewer predicates).
Does not prove: strict antitonicity.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem preservedPredicates_antitone
    {Rule : Type u} {X : Type v} {step : Rule → X → X → Prop}
    {S T : Set Rule} (hST : S ⊆ T) :
    preservedPredicates step T ⊆ preservedPredicates step S := by
  intro P hP r hr
  exact hP r (hST hr)

/-- Proves: `Rules` is antitone (a larger predicate family is preserved by fewer
rules).
Does not prove: strict antitonicity.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem preservingRules_antitone
    {Rule : Type u} {X : Type v} {step : Rule → X → X → Prop}
    {F G : Set (X → Prop)} (hFG : F ⊆ G) :
    preservingRules step G ⊆ preservingRules step F := by
  intro r hr P hP
  exact hr P (hFG hP)

/-- Closure of a rule family under all preservation facts it already forces
(the composite `Rules ∘ Inv`).

Proves: nothing (definition).
Does not prove: the closure laws; those are the theorems below.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
def ruleClosure {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (S : Set Rule) : Set Rule :=
  preservingRules step (preservedPredicates step S)

/-- Closure of a predicate family under all rules that preserve it (the
composite `Inv ∘ Rules`).

Proves: nothing (definition).
Does not prove: the closure laws; those are the theorems below.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
def predicateClosure {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (F : Set (X → Prop)) : Set (X → Prop) :=
  preservedPredicates step (preservingRules step F)

/-- Proves: `Rules ∘ Inv` is extensive.
Does not prove: equality `S = ruleClosure step S`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem subset_ruleClosure
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (S : Set Rule) : S ⊆ ruleClosure step S :=
  (rule_le_preservingRules_iff step S (preservedPredicates step S)).mpr
    (fun _ h => h)

/-- Proves: `Inv ∘ Rules` is extensive.
Does not prove: equality `F = predicateClosure step F`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem subset_predicateClosure
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) : F ⊆ predicateClosure step F :=
  (rule_le_preservingRules_iff step (preservingRules step F) F).mp
    (fun _ h => h)

/-- Proves: `Rules ∘ Inv` is monotone.
Does not prove: strict monotonicity.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem ruleClosure_monotone
    {Rule : Type u} {X : Type v} {step : Rule → X → X → Prop}
    {S T : Set Rule} (hST : S ⊆ T) :
    ruleClosure step S ⊆ ruleClosure step T :=
  preservingRules_antitone (preservedPredicates_antitone hST)

/-- Proves: `Inv ∘ Rules` is monotone.
Does not prove: strict monotonicity.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem predicateClosure_monotone
    {Rule : Type u} {X : Type v} {step : Rule → X → X → Prop}
    {F G : Set (X → Prop)} (hFG : F ⊆ G) :
    predicateClosure step F ⊆ predicateClosure step G :=
  preservedPredicates_antitone (preservingRules_antitone hFG)

/-- Proves: `Rules ∘ Inv` is idempotent.
Does not prove: that every rule family is closed.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`, `Quot.sound`. Scope: arbitrary rule and carrier types. -/
theorem ruleClosure_idempotent
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (S : Set Rule) : ruleClosure step (ruleClosure step S) = ruleClosure step S := by
  apply Set.Subset.antisymm
  · apply preservingRules_antitone
    exact subset_predicateClosure step (preservedPredicates step S)
  · exact subset_ruleClosure step (ruleClosure step S)

/-- Proves: `Inv ∘ Rules` is idempotent.
Does not prove: that every predicate family is closed.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`, `Quot.sound`. Scope: arbitrary rule and carrier types. -/
theorem predicateClosure_idempotent
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) :
    predicateClosure step (predicateClosure step F) = predicateClosure step F := by
  apply Set.Subset.antisymm
  · apply preservedPredicates_antitone
    exact subset_ruleClosure step (preservingRules step F)
  · exact subset_predicateClosure step (predicateClosure step F)

/-- Requested rules retained after deleting exactly those that violate `P`.

Proves: nothing (definition); the singleton case `S ∩ Rules({P})`.
Does not prove: the repair laws; those are the theorems below.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
def invariantRepair {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (P : X → Prop) (S : Set Rule) : Set Rule :=
  S ∩ preservingRules step ({P} : Set (X → Prop))

/-- The rules excluded from the requested family by invariant repair.

Proves: nothing (definition); the set difference of `S` and the singleton
repair.
Does not prove: the least-exclusion law; that is `invariantExclusion_least`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
def invariantExclusion {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (P : X → Prop) (S : Set Rule) : Set Rule :=
  S \ invariantRepair step P S

/-- Proves: a rule is retained by the singleton repair iff it is requested and
preserves `P`.
Does not prove: anything about rules outside `S`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem mem_invariantRepair_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) (r : Rule) :
    r ∈ invariantRepair step P S ↔ r ∈ S ∧ RulePreserves step r P := by
  constructor
  · rintro ⟨hrS, hr⟩
    exact ⟨hrS, hr P rfl⟩
  · rintro ⟨hrS, hr⟩
    refine ⟨hrS, ?_⟩
    intro Q hQ
    have hQP : Q = P := hQ
    rw [hQP]
    exact hr

/-- Proves: a rule is excluded by the singleton repair iff it is requested and
fails to preserve `P`.
Does not prove: anything about rules outside `S`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem mem_invariantExclusion_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) (r : Rule) :
    r ∈ invariantExclusion step P S ↔ r ∈ S ∧ ¬ RulePreserves step r P := by
  constructor
  · intro hr
    refine ⟨hr.1, ?_⟩
    intro hpres
    exact hr.2 ((mem_invariantRepair_iff step P S r).mpr ⟨hr.1, hpres⟩)
  · rintro ⟨hrS, hnot⟩
    refine ⟨hrS, ?_⟩
    intro hr
    exact hnot ((mem_invariantRepair_iff step P S r).mp hr).2

/-- Proves: the singleton repair is contained in the requested family.
Does not prove: strict containment.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem invariantRepair_subset
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) : invariantRepair step P S ⊆ S :=
  fun _ h => h.1

/-- Proves: every rule of the singleton repair preserves `P`.
Does not prove: preservation of any predicate other than `P`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem invariantRepair_preserves
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) :
    P ∈ preservedPredicates step (invariantRepair step P S) := by
  intro r hr
  exact (mem_invariantRepair_iff step P S r).mp hr |>.2

/-- The repaired family is the greatest subfamily of `S` preserving `P`.

Proves: every `T ⊆ S` preserving `P` is contained in the singleton repair.
Does not prove: uniqueness of `T`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem invariantRepair_greatest
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) {S T : Set Rule} (hTS : T ⊆ S)
    (hT : P ∈ preservedPredicates step T) :
    T ⊆ invariantRepair step P S := by
  intro r hr
  exact (mem_invariantRepair_iff step P S r).mpr ⟨hTS hr, hT r hr⟩

/-- Exact least-exclusion theorem: every other invariant-preserving deletion
from `S` excludes every rule excluded by the canonical repair.

Proves: the singleton exclusion lies inside the difference of `S` and `T` for
every `T` preserving `P`.
Does not prove: equality with that difference.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types; `T` need not lie
inside `S`. -/
theorem invariantExclusion_least
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S T : Set Rule)
    (hT : P ∈ preservedPredicates step T) :
    invariantExclusion step P S ⊆ S \ T := by
  intro r hr
  have hexact := (mem_invariantExclusion_iff step P S r).mp hr
  refine ⟨hexact.1, ?_⟩
  intro hrT
  exact hexact.2 (hT r hrT)

/-! ## Exact invariant-family repair -/

/-- Requested rules that preserve every predicate in `F` (the paper's repair
`S ∩ Rules(F)`).

Proves: nothing (definition).
Does not prove: the repair laws; those are the theorems below.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
def familyInvariantRepair {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (F : Set (X → Prop))
    (S : Set Rule) : Set Rule :=
  S ∩ preservingRules step F

/-- Requested rules removed by the invariant-family repair.

Proves: nothing (definition); the set difference of `S` and the family repair.
Does not prove: the least-exclusion law; that is
`familyInvariantExclusion_least`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
def familyInvariantExclusion {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (F : Set (X → Prop))
    (S : Set Rule) : Set Rule :=
  S \ familyInvariantRepair step F S

/-- Proves: the singleton repair is the family repair at `{P}` (definitional).
Does not prove: anything beyond the definitional identity.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem invariantRepair_eq_familyInvariantRepair
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) :
    invariantRepair step P S = familyInvariantRepair step {P} S :=
  rfl

/-- Proves: the singleton exclusion is the family exclusion at `{P}`
(definitional).
Does not prove: anything beyond the definitional identity.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem invariantExclusion_eq_familyInvariantExclusion
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) :
    invariantExclusion step P S = familyInvariantExclusion step {P} S :=
  rfl

/-- Proves: a rule is retained by the family repair iff it is requested and
preserves every predicate of `F`.
Does not prove: anything about rules outside `S`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`. Scope: arbitrary rule and carrier types. -/
theorem mem_familyInvariantRepair_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) (r : Rule) :
    r ∈ familyInvariantRepair step F S ↔
      r ∈ S ∧ ∀ P ∈ F, RulePreserves step r P := by
  change (r ∈ S ∧ r ∈ preservingRules step F) ↔ _
  rw [mem_preservingRules_iff]

/-- Proves: a rule is excluded by the family repair iff it is requested and
fails at least one predicate of `F`.
Does not prove: anything about rules outside `S`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`. Scope: arbitrary rule and carrier types. -/
theorem mem_familyInvariantExclusion_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) (r : Rule) :
    r ∈ familyInvariantExclusion step F S ↔
      r ∈ S ∧ ¬ ∀ P ∈ F, RulePreserves step r P := by
  constructor
  · intro hr
    refine ⟨hr.1, ?_⟩
    intro hpres
    exact hr.2 ((mem_familyInvariantRepair_iff step F S r).mpr ⟨hr.1, hpres⟩)
  · rintro ⟨hrS, hnot⟩
    refine ⟨hrS, ?_⟩
    intro hr
    exact hnot ((mem_familyInvariantRepair_iff step F S r).mp hr).2

/-- Proves: the family repair is contained in the requested family.
Does not prove: strict containment.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: kernel only, no axioms. Scope: arbitrary rule and carrier types. -/
theorem familyInvariantRepair_subset
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) :
    familyInvariantRepair step F S ⊆ S :=
  fun _ h => h.1

/-- Proves: the family repair preserves every predicate of `F`.
Does not prove: preservation of predicates outside `F`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`. Scope: arbitrary rule and carrier types. -/
theorem familyInvariantRepair_preserves
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) :
    F ⊆ preservedPredicates step (familyInvariantRepair step F S) := by
  intro P hP r hr
  exact ((mem_familyInvariantRepair_iff step F S r).mp hr).2 P hP

/-- The family repair is the greatest subfamily of `S` preserving every
predicate in `F`.

Proves: every `T ⊆ S` preserving `F` is contained in the family repair.
Does not prove: uniqueness of `T`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`. Scope: arbitrary rule and carrier types. -/
theorem familyInvariantRepair_greatest
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) {S T : Set Rule} (hTS : T ⊆ S)
    (hT : F ⊆ preservedPredicates step T) :
    T ⊆ familyInvariantRepair step F S := by
  intro r hr
  apply (mem_familyInvariantRepair_iff step F S r).mpr
  exact ⟨hTS hr, fun P hP => hT hP r hr⟩

/-- Any family preserving all predicates in `F` omits every rule removed from
`S` by the canonical family repair. No containment of that family in `S` is
needed.

Proves: the family exclusion lies inside the difference of `S` and `T` for
every `T` preserving `F`.
Does not prove: equality with that difference.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`. Scope: arbitrary rule and carrier types. -/
theorem familyInvariantExclusion_least
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S T : Set Rule)
    (hT : F ⊆ preservedPredicates step T) :
    familyInvariantExclusion step F S ⊆ S \ T := by
  intro r hr
  have hexact := (mem_familyInvariantExclusion_iff step F S r).mp hr
  refine ⟨hexact.1, ?_⟩
  intro hrT
  apply hexact.2
  intro P hP
  exact hT hP r hrT

/-- Proves: the family repair is idempotent.
Does not prove: that the repair is nonempty.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`, `Quot.sound`. Scope: arbitrary rule and carrier types. -/
theorem familyInvariantRepair_idempotent
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) :
    familyInvariantRepair step F (familyInvariantRepair step F S) =
      familyInvariantRepair step F S := by
  apply Set.Subset.antisymm
  · exact familyInvariantRepair_subset step F (familyInvariantRepair step F S)
  · apply familyInvariantRepair_greatest step F
    · exact fun _ h => h
    · exact familyInvariantRepair_preserves step F S

/-- Proves: the family repair and its exclusion cover the requested family.
Does not prove: disjointness; that is
`familyInvariantRepair_exclusion_disjoint`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`, `Classical.choice`, `Quot.sound` (case split on membership).
Scope: arbitrary rule and carrier types. -/
theorem familyInvariantRepair_union_exclusion
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) :
    familyInvariantRepair step F S ∪ familyInvariantExclusion step F S = S := by
  classical
  apply Set.Subset.antisymm
  · intro r hr
    rcases hr with hr | hr
    · exact familyInvariantRepair_subset step F S hr
    · exact hr.1
  · intro r hrS
    by_cases hr : r ∈ familyInvariantRepair step F S
    · exact Or.inl hr
    · exact Or.inr ⟨hrS, hr⟩

/-- Proves: the family repair and its exclusion are disjoint.
Does not prove: the covering law; that is
`familyInvariantRepair_union_exclusion`.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`, `Quot.sound`. Scope: arbitrary rule and carrier types. -/
theorem familyInvariantRepair_exclusion_disjoint
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) :
    Disjoint (familyInvariantRepair step F S)
      (familyInvariantExclusion step F S) := by
  rw [Set.disjoint_left]
  intro r hr hrex
  exact hrex.2 hr

/-- The family construction simultaneously states retention, preservation,
maximality, minimal exclusion, partition, and disjointness.

Proves: the six repair clauses of `thm:rule-invariant-galois` as one
conjunction.
Does not prove: any confluence or termination property of the repaired family.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`, `Classical.choice`, `Quot.sound` (through the partition clause).
Scope: arbitrary rule and carrier types. -/
theorem invariantFamilyRepair_complete
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) :
    familyInvariantRepair step F S ⊆ S
      ∧ F ⊆ preservedPredicates step (familyInvariantRepair step F S)
      ∧ (∀ T : Set Rule, T ⊆ S → F ⊆ preservedPredicates step T →
          T ⊆ familyInvariantRepair step F S)
      ∧ (∀ T : Set Rule, F ⊆ preservedPredicates step T →
          familyInvariantExclusion step F S ⊆ S \ T)
      ∧ familyInvariantRepair step F S ∪ familyInvariantExclusion step F S = S
      ∧ Disjoint (familyInvariantRepair step F S)
          (familyInvariantExclusion step F S) := by
  exact ⟨familyInvariantRepair_subset step F S,
    familyInvariantRepair_preserves step F S,
    fun T hTS hT => familyInvariantRepair_greatest step F hTS hT,
    fun T hT => familyInvariantExclusion_least step F S T hT,
    familyInvariantRepair_union_exclusion step F S,
    familyInvariantRepair_exclusion_disjoint step F S⟩

/-- The Galois law and both idempotent closure laws as one statement.

Proves: the displayed equivalence of `thm:rule-invariant-galois` for all `S`
and `F`, and idempotence of `Rules ∘ Inv` and `Inv ∘ Rules`.
Does not prove: any monotonicity of confluence under rule change.
Relation: `step`. Closure: one step. Strategy: not applicable.
Trust: `propext`, `Quot.sound`. Scope: arbitrary rule and carrier types. -/
theorem dynamic_license_galois_complete
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop) :
    (∀ (S : Set Rule) (F : Set (X → Prop)),
      S ⊆ preservingRules step F ↔ F ⊆ preservedPredicates step S)
      ∧ (∀ S : Set Rule, ruleClosure step (ruleClosure step S) = ruleClosure step S)
      ∧ (∀ F : Set (X → Prop),
        predicateClosure step (predicateClosure step F) = predicateClosure step F) := by
  exact ⟨fun S F => rule_le_preservingRules_iff step S F,
    fun S => ruleClosure_idempotent step S,
    fun F => predicateClosure_idempotent step F⟩

end OperatorKO7.Meta.OperationalInexpressibility.DynamicLicenseGalois
