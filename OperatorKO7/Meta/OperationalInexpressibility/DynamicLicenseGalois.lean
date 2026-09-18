import OperatorKO7.Meta.DistinctionBoundary.WriteClosure

/-!
# Dynamic license Galois connection

For any rule-indexed relation, rule families and invariant families determine
each other by preservation. The resulting antitone Galois connection supplies
closure operators on both sides. Deleting the requested rules that fail at
least one requested invariant gives the greatest preserving subfamily and the
least exclusion. The one-invariant construction is its singleton instance.

The equality-guarded KO7 positional repair is then stated separately. Its
confluence theorem uses the complete positional peak classification, not the
unary preservation Galois law: the repair freezes equality congruence and may
add both application positions forced by recursive-context selection.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DynamicLicenseGalois

universe u v

/-- A rule preserves a unary predicate along every step that it generates. -/
def RulePreserves {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (r : Rule) (P : X → Prop) : Prop :=
  ∀ ⦃x y⦄, step r x y → P x → P y

/-- Predicates preserved by every rule in a selected family. -/
def preservedPredicates {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (S : Set Rule) : Set (X → Prop) :=
  {P | ∀ r ∈ S, RulePreserves step r P}

/-- Rules preserving every predicate in a specified family. -/
def preservingRules {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (F : Set (X → Prop)) : Set Rule :=
  {r | ∀ P ∈ F, RulePreserves step r P}

@[simp] theorem mem_preservedPredicates_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (S : Set Rule) (P : X → Prop) :
    P ∈ preservedPredicates step S ↔
      ∀ r ∈ S, RulePreserves step r P :=
  Iff.rfl

@[simp] theorem mem_preservingRules_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (r : Rule) :
    r ∈ preservingRules step F ↔
      ∀ P ∈ F, RulePreserves step r P :=
  Iff.rfl

/-- The defining rule-family/predicate-family antitone Galois law. -/
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
predicate-family order. -/
theorem rulePredicate_galoisConnection
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop) :
    GaloisConnection
      (fun S : Set Rule => OrderDual.toDual (preservedPredicates step S))
      (fun F : OrderDual (Set (X → Prop)) =>
        preservingRules step (OrderDual.ofDual F)) :=
  fun S F => (rule_le_preservingRules_iff step S (OrderDual.ofDual F)).symm

theorem preservedPredicates_antitone
    {Rule : Type u} {X : Type v} {step : Rule → X → X → Prop}
    {S T : Set Rule} (hST : S ⊆ T) :
    preservedPredicates step T ⊆ preservedPredicates step S := by
  intro P hP r hr
  exact hP r (hST hr)

theorem preservingRules_antitone
    {Rule : Type u} {X : Type v} {step : Rule → X → X → Prop}
    {F G : Set (X → Prop)} (hFG : F ⊆ G) :
    preservingRules step G ⊆ preservingRules step F := by
  intro r hr P hP
  exact hr P (hFG hP)

/-- Closure of a rule family under all preservation facts it already forces. -/
def ruleClosure {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (S : Set Rule) : Set Rule :=
  preservingRules step (preservedPredicates step S)

/-- Closure of a predicate family under all rules that preserve it. -/
def predicateClosure {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (F : Set (X → Prop)) : Set (X → Prop) :=
  preservedPredicates step (preservingRules step F)

theorem subset_ruleClosure
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (S : Set Rule) : S ⊆ ruleClosure step S :=
  (rule_le_preservingRules_iff step S (preservedPredicates step S)).mpr
    (fun _ h => h)

theorem subset_predicateClosure
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) : F ⊆ predicateClosure step F :=
  (rule_le_preservingRules_iff step (preservingRules step F) F).mp
    (fun _ h => h)

theorem ruleClosure_monotone
    {Rule : Type u} {X : Type v} {step : Rule → X → X → Prop}
    {S T : Set Rule} (hST : S ⊆ T) :
    ruleClosure step S ⊆ ruleClosure step T :=
  preservingRules_antitone (preservedPredicates_antitone hST)

theorem predicateClosure_monotone
    {Rule : Type u} {X : Type v} {step : Rule → X → X → Prop}
    {F G : Set (X → Prop)} (hFG : F ⊆ G) :
    predicateClosure step F ⊆ predicateClosure step G :=
  preservedPredicates_antitone (preservingRules_antitone hFG)

theorem ruleClosure_idempotent
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (S : Set Rule) : ruleClosure step (ruleClosure step S) = ruleClosure step S := by
  apply Set.Subset.antisymm
  · apply preservingRules_antitone
    exact subset_predicateClosure step (preservedPredicates step S)
  · exact subset_ruleClosure step (ruleClosure step S)

theorem predicateClosure_idempotent
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) :
    predicateClosure step (predicateClosure step F) = predicateClosure step F := by
  apply Set.Subset.antisymm
  · apply preservedPredicates_antitone
    exact subset_ruleClosure step (preservingRules step F)
  · exact subset_predicateClosure step (predicateClosure step F)

/-- Requested rules retained after deleting exactly those that violate `P`. -/
def invariantRepair {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (P : X → Prop) (S : Set Rule) : Set Rule :=
  S ∩ preservingRules step ({P} : Set (X → Prop))

/-- The rules excluded from the requested family by invariant repair. -/
def invariantExclusion {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (P : X → Prop) (S : Set Rule) : Set Rule :=
  S \ invariantRepair step P S

theorem mem_invariantRepair_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) (r : Rule) :
    r ∈ invariantRepair step P S ↔ r ∈ S ∧ RulePreserves step r P := by
  simp [invariantRepair, preservingRules]

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

theorem invariantRepair_subset
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) : invariantRepair step P S ⊆ S :=
  fun _ h => h.1

theorem invariantRepair_preserves
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) :
    P ∈ preservedPredicates step (invariantRepair step P S) := by
  intro r hr
  exact (mem_invariantRepair_iff step P S r).mp hr |>.2

/-- The repaired family is the greatest subfamily of `S` preserving `P`. -/
theorem invariantRepair_greatest
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) {S T : Set Rule} (hTS : T ⊆ S)
    (hT : P ∈ preservedPredicates step T) :
    T ⊆ invariantRepair step P S := by
  intro r hr
  exact (mem_invariantRepair_iff step P S r).mpr ⟨hTS hr, hT r hr⟩

/-- Exact least-exclusion theorem: every other invariant-preserving deletion
from `S` excludes every rule excluded by the canonical repair. -/
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

/-- Requested rules that preserve every predicate in `F`. -/
def familyInvariantRepair {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (F : Set (X → Prop))
    (S : Set Rule) : Set Rule :=
  S ∩ preservingRules step F

/-- Requested rules removed by the invariant-family repair. -/
def familyInvariantExclusion {Rule : Type u} {X : Type v}
    (step : Rule → X → X → Prop) (F : Set (X → Prop))
    (S : Set Rule) : Set Rule :=
  S \ familyInvariantRepair step F S

theorem invariantRepair_eq_familyInvariantRepair
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) :
    invariantRepair step P S = familyInvariantRepair step {P} S :=
  rfl

theorem invariantExclusion_eq_familyInvariantExclusion
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (P : X → Prop) (S : Set Rule) :
    invariantExclusion step P S = familyInvariantExclusion step {P} S :=
  rfl

theorem mem_familyInvariantRepair_iff
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) (r : Rule) :
    r ∈ familyInvariantRepair step F S ↔
      r ∈ S ∧ ∀ P ∈ F, RulePreserves step r P := by
  change (r ∈ S ∧ r ∈ preservingRules step F) ↔ _
  rw [mem_preservingRules_iff]

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

theorem familyInvariantRepair_subset
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) :
    familyInvariantRepair step F S ⊆ S :=
  fun _ h => h.1

theorem familyInvariantRepair_preserves
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) :
    F ⊆ preservedPredicates step (familyInvariantRepair step F S) := by
  intro P hP r hr
  exact ((mem_familyInvariantRepair_iff step F S r).mp hr).2 P hP

/-- The family repair is the greatest subfamily of `S` preserving every
predicate in `F`. -/
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
needed. -/
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

theorem familyInvariantRepair_exclusion_disjoint
    {Rule : Type u} {X : Type v} (step : Rule → X → X → Prop)
    (F : Set (X → Prop)) (S : Set Rule) :
    Disjoint (familyInvariantRepair step F S)
      (familyInvariantExclusion step F S) := by
  rw [Set.disjoint_left]
  intro r hr hrex
  exact hrex.2 hr

/-- The family construction simultaneously states retention, preservation,
maximality, minimal exclusion, partition, and disjointness. -/
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

/-! ## Singleton invariant repair -/

open OperatorKO7
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.FreezePositions
open OperatorKO7.Meta.DistinctionBoundary.WriteClosure

/-- The positional repair has the exact selected relation named in its type,
is confluent, retains every requested non-equality position, and is the least
such confluent extension. -/
theorem positional_confluenceRepair_universal (S : CtorPos → Prop) :
    (¬ confluenceRepair S .eqW)
      ∧ (∀ c, S c → c ≠ .eqW → confluenceRepair S c)
      ∧ (confluenceRepair S .recD → confluenceRepair S .appL)
      ∧ (confluenceRepair S .recD → confluenceRepair S .appR)
      ∧ ConfluentOnPos (confluenceRepair S) EqGuardedStep
      ∧ (∀ T : CtorPos → Prop,
        ConfluentOnPos T EqGuardedStep →
        (∀ c, S c → c ≠ .eqW → T c) →
        SelectionLE (confluenceRepair S) T) := by
  exact ⟨confluenceRepair_freezes_eqW S,
    confluenceRepair_extends_nonEqW S,
    (confluenceRepair_writeClosed S).1,
    (confluenceRepair_writeClosed S).2,
    confluenceRepair_confluent S,
    fun T hT hExt => confluenceRepair_least hT hExt⟩

/-- Equality-congruence exclusion alone does not ensure confluence: selecting
only the recursive context leaves both contractum application positions
frozen and realizes the compiled recursor peak. -/
theorem recDOnly_not_confluent :
    (¬ recDSeed .eqW) ∧
      ¬ ConfluentOnPos recDSeed EqGuardedStep := by
  exact ⟨fun h => CtorPos.noConfusion h, recDSeed_not_confluent⟩

/-- The complete positional classification, its least repair, and the generic
least invariant exclusion are separate exact results. In particular, no
monotonicity claim for confluence under arbitrary rule change is used. -/
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
