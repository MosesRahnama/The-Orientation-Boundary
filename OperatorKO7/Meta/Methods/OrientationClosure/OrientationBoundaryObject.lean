import OperatorKO7.Meta.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone
import OperatorKO7.Meta.Methods.OrientationClosure.CellClassification
import Mathlib.Data.Set.Basic

set_option autoImplicit false

/-!
# The Orientation Boundary as a mathematical object

The Orientation Boundary of the free recursor is a set of reflected grammar
expressions with two descriptions.  The semantic description collects the
expressions whose induced measure decreases across every actual successor root
step; the syntactic description collects the payload-blind, counter-strict
expressions.  The capstone biconditional is the equality of the two sets.  The
four growth cells of the cost/gain classification form a four-element type, and
at every measure and every base/counter pair one cell holds and no second cell
does.  Every declaration below repackages theorems that already exist in the
development; nothing new about rewriting is proved here.
-/

namespace OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.AttainedPairs
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Methods.OrientationClosure.OrientationBoundaryPublicationCapstone
open OperatorKO7.Methods.OrientationClosure.CellClassification
open OperatorKO7.StepDuplicating

/-! ## The boundary as a set of grammar expressions -/

/--
Proves: nothing; this is the semantic side of the boundary, the set of reflected
scalar grammar expressions whose induced measure decreases across every actual
free-recursor successor root instance.
Does not prove: any property of its members.
Relation: free-recursor successor instances represented by `FreeTerm` and the
successor constructor of `RootStep`.
Closure: root single-step.
Strategy: not applicable.
Trust: definition only.
Scope: every `MeasureExpr`.
-/
def orienters : Set MeasureExpr :=
  {e | ∀ {ν : Type} (b s n : FreeTerm ν),
    profileMeasure e.eval (.wrap s (.recur b s n)) <
      profileMeasure e.eval (.recur b s (.succ n))}

/--
Proves: nothing; this is the syntactic side of the boundary, the set of
reflected scalar grammar expressions whose denotation is payload-blind and
counter-strict.
Does not prove: any property of its members.
Relation: none; the predicates are on the `(counter, payload)` carrier.
Closure: not applicable.
Strategy: not applicable.
Trust: definition only.
Scope: every `MeasureExpr`.
-/
def payloadBlindCounterStrict : Set MeasureExpr :=
  {e | PayloadBlind e.eval ∧ CounterStrict e.eval}

/--
Proves: the Orientation Boundary equality; the set of grammar expressions that
orient every actual free-recursor successor root instance equals the set of
payload-blind, counter-strict grammar expressions.
Does not prove: contextual termination, confluence, or orientation by measures
outside the reflected scalar grammar.
Relation: free-recursor successor instances represented by `FreeTerm` and the
successor constructor of `RootStep`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the foundational axioms inherited from the capstone
biconditional.
Scope: every `MeasureExpr`, as an equality of subsets of `MeasureExpr`.
-/
theorem orientationBoundary_eq : orienters = payloadBlindCounterStrict := by
  ext e
  exact free_successor_orientation_iff_payloadBlind_and_counterStrict e

/--
Proves: the counter projection lies on the orienting side of the boundary.
Does not prove: uniqueness of orienters.
Relation: free-recursor successor instances represented by `FreeTerm`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the axioms of `orientationBoundary_eq`.
Scope: the expression `MeasureExpr.counter`.
-/
theorem counter_mem_orienters : MeasureExpr.counter ∈ orienters := by
  rw [orientationBoundary_eq]
  exact ⟨fun _ _ _ => rfl, fun c _ => Nat.lt_succ_self c⟩

/--
Proves: the payload projection lies outside the orienting side of the boundary.
Does not prove: anything about other payload-dependent expressions beyond what
`orientationBoundary_eq` gives.
Relation: free-recursor successor instances represented by `FreeTerm`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the axioms of `orientationBoundary_eq`.
Scope: the expression `MeasureExpr.payload`.
-/
theorem payload_not_mem_orienters : MeasureExpr.payload ∉ orienters := by
  rw [orientationBoundary_eq]
  rintro ⟨hblind, -⟩
  have h := hblind 0 0 1
  simp [MeasureExpr.eval] at h

/--
Proves: every constant expression lies outside the orienting side of the
boundary, because a constant is not counter-strict.
Does not prove: anything about non-constant payload-blind expressions.
Relation: free-recursor successor instances represented by `FreeTerm`.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the axioms of `orientationBoundary_eq`.
Scope: every `MeasureExpr.const k`.
-/
theorem const_not_mem_orienters (k : Nat) : MeasureExpr.const k ∉ orienters := by
  rw [orientationBoundary_eq]
  rintro ⟨-, hstrict⟩
  have h := hstrict 0 0
  simp [MeasureExpr.eval] at h

/-! ## The growth cells as a four-element type -/

/-- The four growth cells of the cost/gain classification at a fixed base and
counter: `barrier` is unbounded wrapper cost with bounded counter gain. -/
inductive GrowthCell where
  | barrier
  | costUnboundedGainUnbounded
  | costBoundedGainBounded
  | costBoundedGainUnbounded
  deriving DecidableEq, Repr

/--
Proves: nothing; membership of a natural-valued measure in a growth cell at a
fixed base/counter pair, in the order of `four_cell_coverage`.
Does not prove: coverage or uniqueness, which are the theorems below.
Relation: the duplicating rule of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: not applicable.
Trust: definition only.
Scope: every schema, every natural-valued measure, every base/counter pair.
-/
def InCell {S : StepDuplicatingSchema} (M : S.T → Nat) (b n : S.T) : GrowthCell → Prop
  | .barrier => WrapUnboundedAt M b n ∧ GainBoundedAt M b n
  | .costUnboundedGainUnbounded => WrapUnboundedAt M b n ∧ GainUnboundedAt M b n
  | .costBoundedGainBounded => WrapBoundedAt M b n ∧ GainBoundedAt M b n
  | .costBoundedGainUnbounded => WrapBoundedAt M b n ∧ GainUnboundedAt M b n

/--
Proves: at every base/counter pair, every natural-valued measure lies in some
growth cell.
Does not prove: uniqueness of that cell.
Relation: the duplicating rule of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the axioms of `four_cell_coverage`.
Scope: every schema, every natural-valued measure, every base/counter pair.
-/
theorem exists_cell {S : StepDuplicatingSchema} (M : S.T → Nat) (b n : S.T) :
    ∃ c : GrowthCell, InCell M b n c := by
  rcases four_cell_coverage M b n with h | h | h | h
  · exact ⟨.barrier, h⟩
  · exact ⟨.costUnboundedGainUnbounded, h⟩
  · exact ⟨.costBoundedGainBounded, h⟩
  · exact ⟨.costBoundedGainUnbounded, h⟩

/--
Proves: wrapper cost is never both unbounded and bounded at one base/counter
pair.
Does not prove: which of the two holds.
Relation: the duplicating rule of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; arithmetic only.
Scope: every schema, every natural-valued measure, every base/counter pair.
-/
theorem not_wrapUnbounded_and_wrapBounded {S : StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T)
    (hu : WrapUnboundedAt M b n) (hb : WrapBoundedAt M b n) : False := by
  obtain ⟨K, hK⟩ := hb
  obtain ⟨s, hs⟩ := hu K
  have h := hK s
  omega

/--
Proves: counter gain is never both bounded and unbounded at one base/counter
pair.
Does not prove: which of the two holds.
Relation: the duplicating rule of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; arithmetic only.
Scope: every schema, every natural-valued measure, every base/counter pair.
-/
theorem not_gainBounded_and_gainUnbounded {S : StepDuplicatingSchema}
    (M : S.T → Nat) (b n : S.T)
    (hb : GainBoundedAt M b n) (hu : GainUnboundedAt M b n) : False := by
  obtain ⟨K, hK⟩ := hb
  obtain ⟨s, hs⟩ := hu K
  have h := hK s
  omega

/--
Proves: at every base/counter pair, a natural-valued measure lies in at most one
growth cell.
Does not prove: existence, which is `exists_cell`.
Relation: the duplicating rule of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel; arithmetic only.
Scope: every schema, every natural-valued measure, every base/counter pair.
-/
theorem cell_unique {S : StepDuplicatingSchema} (M : S.T → Nat) (b n : S.T)
    {c c' : GrowthCell} (h : InCell M b n c) (h' : InCell M b n c') : c = c' := by
  cases c <;> cases c' <;> simp only [InCell] at h h' <;> first
    | rfl
    | exact (not_wrapUnbounded_and_wrapBounded M b n h.1 h'.1).elim
    | exact (not_wrapUnbounded_and_wrapBounded M b n h'.1 h.1).elim
    | exact (not_gainBounded_and_gainUnbounded M b n h.2 h'.2).elim
    | exact (not_gainBounded_and_gainUnbounded M b n h'.2 h.2).elim

/--
Proves: the barrier cell excludes uniform orientation of the duplicating step at
its base/counter pair.
Does not prove: anything about the other three cells; `nonbarrier_cells_have_both_verdicts`
covers them on the free schema.
Relation: the duplicating rule of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with the axioms of `barrier_cell_excludes_orientation`.
Scope: every schema, every natural-valued measure, every base/counter pair.
-/
theorem barrier_cell_excludes {S : StepDuplicatingSchema} (M : S.T → Nat) (b n : S.T)
    (h : InCell M b n .barrier) :
    ¬ ∀ s : S.T, M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n)) :=
  barrier_cell_excludes_orientation M b n h.1 h.2

/--
Proves: nothing; the growth cell of a measure at a base/counter pair, chosen
from `exists_cell`.
Does not prove: computability; the choice is classical.
Relation: the duplicating rule of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: not applicable.
Trust: `Classical.choice`.
Scope: every schema, every natural-valued measure, every base/counter pair.
-/
noncomputable def growthCell {S : StepDuplicatingSchema} (M : S.T → Nat) (b n : S.T) :
    GrowthCell :=
  Classical.choose (exists_cell M b n)

/--
Proves: the chosen growth cell is a cell of the measure at that pair.
Does not prove: uniqueness, which is `growthCell_eq_iff`.
Relation: the duplicating rule of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with `Classical.choice` and the axioms of `exists_cell`.
Scope: every schema, every natural-valued measure, every base/counter pair.
-/
theorem growthCell_spec {S : StepDuplicatingSchema} (M : S.T → Nat) (b n : S.T) :
    InCell M b n (growthCell M b n) :=
  Classical.choose_spec (exists_cell M b n)

/--
Proves: the growth cell of a measure at a pair is the cell `c` if and only if
the measure lies in `c` there; the classification is a function.
Does not prove: computability of that function.
Relation: the duplicating rule of an arbitrary step-duplicating schema.
Closure: root single-step.
Strategy: not applicable.
Trust: Lean kernel with `Classical.choice` and the axioms of `exists_cell`.
Scope: every schema, every natural-valued measure, every base/counter pair, every cell.
-/
theorem growthCell_eq_iff {S : StepDuplicatingSchema} (M : S.T → Nat) (b n : S.T)
    {c : GrowthCell} : growthCell M b n = c ↔ InCell M b n c :=
  ⟨fun h => h ▸ growthCell_spec M b n,
    fun h => cell_unique M b n (growthCell_spec M b n) h⟩

end OperatorKO7.Methods.OrientationClosure.OrientationBoundaryObject
