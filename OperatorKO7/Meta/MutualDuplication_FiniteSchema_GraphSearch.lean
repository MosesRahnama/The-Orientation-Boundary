import OperatorKO7.Meta.MutualDuplication_FiniteSchema_BuilderMapping

/-!
# Finite-Cycle Graph-Search Certificate Mapping

This module inserts one theorem-visible layer between graph-edge search data and the
existing H3 finite-cycle search-certificate or builder surfaces.

The point is not to discover graph edges algorithmically. The graph certificate still
stores the searched finite-cycle edge data explicitly. Once those edges certify the local
successor transition at each cycle index, the existing finite-cycle barrier stack follows.
-/

namespace OperatorKO7.MutualDuplicationFiniteSchema

open OperatorKO7.StepDuplicating

namespace FiniteCycleGraphSearch

/-- First-class theorem-visible graph-search certificate for a finite cycle of length `k + 1`.
It separates the searched graph edges from the derived local successor-step family. -/
structure GraphSearchCertificate (k : Nat) where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : Fin (k + 1) → T → T → T → T
  Edge : Fin (k + 1) → Fin (k + 1) → Prop
  Step : T → T → Prop
  local_graph_edge : ∀ i : Fin (k + 1), Edge i (FiniteCycleBuilder.advance i)
  step_succ_of_edge :
    ∀ {i j : Fin (k + 1)}, Edge i j → ∀ b s n,
      Step (recur i b s (succ n)) (wrap s (recur j b s n))

namespace GraphSearchCertificate

/-- The graph certificate derives the local successor-step family needed by the existing
finite-cycle search-certificate surface. -/
theorem local_step_succ_derived
    {k : Nat} (C : GraphSearchCertificate k) :
    ∀ (i : Fin (k + 1)) b s n,
      C.Step (C.recur i b s (C.succ n))
        (C.wrap s (C.recur (FiniteCycleBuilder.advance i) b s n)) := by
  intro i b s n
  exact C.step_succ_of_edge (C.local_graph_edge i) b s n

/-- Forget the graph-edge bookkeeping and expose the existing finite-cycle
search-certificate surface. -/
def toSearchCertificate {k : Nat} (C : GraphSearchCertificate k) :
    FiniteCycleBuilderMapping.SearchCertificate k where
  T := C.T
  base := C.base
  succ := C.succ
  wrap := C.wrap
  recur := C.recur
  Step := C.Step
  local_step_succ := C.local_step_succ_derived

/-- The graph certificate also transports directly to the existing builder surface. -/
def toBuilder {k : Nat} (C : GraphSearchCertificate k) : FiniteCycleBuilder.Builder k :=
  C.toSearchCertificate.toBuilder

@[simp] theorem toSearchCertificate_toBuilder_eq
    {k : Nat} (C : GraphSearchCertificate k) :
    C.toSearchCertificate.toBuilder = C.toBuilder :=
  rfl

/-- The realized finite-cycle contextual relation carried by the graph certificate. -/
abbrev StepCtx {k : Nat} (C : GraphSearchCertificate k) : C.T → C.T → Prop :=
  FiniteCycleBuilderMapping.SearchCertificate.StepCtx C.toSearchCertificate

/-- The realized finite-cycle contextual orientation predicate carried by the graph
certificate. -/
def GlobalOrientsCtx {k : Nat} {α : Type} (C : GraphSearchCertificate k) (m : C.T → α)
    (lt : α → α → Prop) : Prop :=
  FiniteCycleBuilderMapping.SearchCertificate.GlobalOrientsCtx C.toSearchCertificate m lt

/-- The graph-certificate affine one-cycle witness at node `i`. -/
abbrev KCycleAffineAt {k : Nat} {C : GraphSearchCertificate k}
    (i : Fin (k + 1)) (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema) :=
  FiniteCycleBuilderMapping.SearchCertificate.KCycleAffineAt i M

/-- The graph-certificate affine one-cycle witness at node `0`. -/
abbrev KCycleAffineAtZero {k : Nat} {C : GraphSearchCertificate k}
    (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema) :=
  FiniteCycleBuilderMapping.SearchCertificate.KCycleAffineAtZero M

/-- Every discovered node on the certified finite cycle realizes the induced cycle path. -/
theorem cycle_realized_at
    {k : Nat} (C : GraphSearchCertificate k) (i : Fin (k + 1)) (b s n : C.T) :
    Relation.TransGen (C.StepCtx)
      (KCycleSchema.cycleSource C.toBuilder.toKCycleSystem.toKCycleSchema i b s n)
      (KCycleSchema.cycleTarget C.toBuilder.toKCycleSystem.toKCycleSchema i b s n) := by
  exact FiniteCycleBuilderMapping.SearchCertificate.cycle_realized_at C.toSearchCertificate i b s n

/-- Additive contextual barriers transport from the derived builder through the graph
certificate. -/
theorem no_global_orients_ctx_additive
    {k : Nat} {C : GraphSearchCertificate k}
    (M : KCycleSchema.AdditiveMeasure C.toBuilder.toKCycleSystem.toKCycleSchema) :
    ¬ C.GlobalOrientsCtx M.eval (· < ·) := by
  exact FiniteCycleBuilderMapping.SearchCertificate.no_global_orients_ctx_additive M

/-- Arbitrary-node affine contextual barriers transport from the derived builder through the
graph certificate once the chosen-node derived one-cycle witness is unbounded. -/
theorem no_global_orients_ctx_affine_of_unbounded_at
    {k : Nat} {C : GraphSearchCertificate k}
    (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema)
    (i : Fin (k + 1))
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (C.KCycleAffineAt i M)) :
    ¬ C.GlobalOrientsCtx M.eval (· < ·) := by
  exact
    FiniteCycleBuilderMapping.SearchCertificate.no_global_orients_ctx_affine_of_unbounded_at
      M i hunbounded

/-- Node-`0` compatibility wrapper for the graph-certificate affine contextual barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded
    {k : Nat} {C : GraphSearchCertificate k}
    (M : KCycleSchema.AffineMeasure C.toBuilder.toKCycleSystem.toKCycleSchema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange (C.KCycleAffineAtZero M)) :
    ¬ C.GlobalOrientsCtx M.eval (· < ·) := by
  exact FiniteCycleBuilderMapping.SearchCertificate.no_global_orients_ctx_affine_of_unbounded M hunbounded

end GraphSearchCertificate

end FiniteCycleGraphSearch

namespace Constructors

/-- Two-rule constructor data as a finite-cycle graph-search certificate. -/
def TwoRuleData.toGraphSearchCertificate (D : TwoRuleData) :
    FiniteCycleGraphSearch.GraphSearchCertificate 1 where
  T := D.T
  base := D.base
  succ := D.succ
  wrap := D.wrap
  recur := fun i =>
    match i.1 with
    | 0 => D.recurA
    | _ => D.recurB
  Edge := fun i j => j = FiniteCycleBuilder.advance i
  Step := D.Step
  local_graph_edge := by
    intro i
    rfl
  step_succ_of_edge := by
    intro i j hij b s n
    subst j
    fin_cases i
    · simpa [FiniteCycleBuilder.advance] using D.stepA_succ b s n
    · simpa [FiniteCycleBuilder.advance] using D.stepB_succ b s n

/-- Three-rule constructor data as a finite-cycle graph-search certificate. -/
def ThreeRuleData.toGraphSearchCertificate (D : ThreeRuleData) :
    FiniteCycleGraphSearch.GraphSearchCertificate 2 where
  T := D.T
  base := D.base
  succ := D.succ
  wrap := D.wrap
  recur := fun i =>
    match i.1 with
    | 0 => D.recur0
    | 1 => D.recur1
    | _ => D.recur2
  Edge := fun i j => j = FiniteCycleBuilder.advance i
  Step := D.Step
  local_graph_edge := by
    intro i
    rfl
  step_succ_of_edge := by
    intro i j hij b s n
    subst j
    fin_cases i
    · simpa [FiniteCycleBuilder.advance] using D.step0_succ b s n
    · simpa [FiniteCycleBuilder.advance] using D.step1_succ b s n
    · simpa [FiniteCycleBuilder.advance] using D.step2_succ b s n

end Constructors

namespace KCycleSystem

/-- Concrete graph-search wrapper for the two-rule witness data. -/
def twoRuleWitnessGraphSearchCertificate : FiniteCycleGraphSearch.GraphSearchCertificate 1 :=
  twoRuleWitnessData.toGraphSearchCertificate

/-- Concrete graph-search wrapper for the three-rule witness data. -/
def threeRuleWitnessGraphSearchCertificate : FiniteCycleGraphSearch.GraphSearchCertificate 2 :=
  threeRuleWitnessData.toGraphSearchCertificate

end KCycleSystem

end OperatorKO7.MutualDuplicationFiniteSchema
