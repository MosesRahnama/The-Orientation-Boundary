import OperatorKO7.Meta.LicensedBoundaryCalculus.FailureObject

/-!
# Universal boundary completion and semantic repair frontier

`SafeRel R P` is the greatest subrelation of `R` that preserves `P` one step.
Together with the existing greatest stable sublicense `Box R P`, it gives two
exact endpoint repairs.  The module proves their mutual fixed-point laws and
places actual relation/predicate pairs in a partial order, separating endpoint
greatestness from global incomparability.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense

universe u

/-- Pointwise inclusion of relations. -/
def RelationLE {α : Type u} (S R : α → α → Prop) : Prop :=
  ∀ x y : α, S x y → R x y

/-- Pointwise inclusion of predicates. -/
def PredicateLE {α : Type u} (Q P : α → Prop) : Prop :=
  ∀ x : α, Q x → P x

/-- One-step preservation of a predicate by a relation. -/
def Preserves {α : Type u} (R : α → α → Prop) (P : α → Prop) : Prop :=
  ∀ x y : α, R x y → P x → P y

/-- Universal dynamics-side completion: retain exactly raw edges that cannot
cross from `P` to `¬P`. -/
def SafeRel {α : Type u} (R : α → α → Prop) (P : α → Prop)
    (x y : α) : Prop :=
  R x y ∧ (P x → P y)

/-- `SafeRel` never adds an edge. -/
theorem safeRel_subset {α : Type u} (R : α → α → Prop) (P : α → Prop) :
    RelationLE (SafeRel R P) R := by
  intro _ _ h
  exact h.1

/-- `SafeRel` preserves `P` by construction. -/
theorem safeRel_preserves {α : Type u} (R : α → α → Prop) (P : α → Prop) :
    Preserves (SafeRel R P) P := by
  intro _ _ h hx
  exact h.2 hx

/-- Greatestness ranges over an independent candidate relation `S`. -/
theorem safeRel_greatest {α : Type u} {R S : α → α → Prop} {P : α → Prop}
    (hsub : RelationLE S R) (hpres : Preserves S P) :
    RelationLE S (SafeRel R P) := by
  intro x y hxy
  exact ⟨hsub x y hxy, fun hx => hpres x y hxy hx⟩

/-- A real boundary crossing is precisely an edge that `SafeRel` must delete. -/
theorem boundaryEdge_removed_by_safeRel {α : Type u}
    {R : α → α → Prop} {P : α → Prop} {x y : α}
    (h : BoundaryEdge R P x y) :
    R x y ∧ ¬ SafeRel R P x y := by
  refine ⟨h.1, ?_⟩
  rintro ⟨_, hpres⟩
  exact h.2.2 (hpres h.2.1)

/-- A `SafeRel` path preserves `P` at every endpoint. -/
theorem safeRel_star_preserves {α : Type u} {R : α → α → Prop} {P : α → Prop}
    {x y : α} (hx : P x) (hxy : Relation.ReflTransGen (SafeRel R P) x y) :
    P y := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact hstep.2 ih

/-! The live `Box` donor is universe-0, so the exact state/dynamics mutual laws
below use that scope. -/

/-- Once the predicate has been repaired to `Box R P`, every raw `R` edge is safe. -/
theorem safeRel_box_eq {α : Type} (R : α → α → Prop) (P : α → Prop) :
    SafeRel R (Box R P) = R := by
  funext x y
  apply propext
  constructor
  · exact fun h => h.1
  · intro hxy
    refine ⟨hxy, ?_⟩
    intro hx
    exact box_forwardInvariant hx (Relation.ReflTransGen.single hxy)

/-- Once dynamics is repaired to `SafeRel R P`, every currently licensed point
has persistent license: `Box` performs no further state restriction. -/
theorem box_safeRel_eq {α : Type} (R : α → α → Prop) (P : α → Prop) :
    Box (SafeRel R P) P = P := by
  funext x
  apply propext
  constructor
  · exact fun h => h.holds
  · intro hx
    exact ⟨hx, fun y hy => safeRel_star_preserves hx hy⟩

/-- The two universal repairs fix one another exactly. -/
theorem state_dynamics_mutual_stabilization {α : Type}
    (R : α → α → Prop) (P : α → Prop) :
    SafeRel R (Box R P) = R ∧ Box (SafeRel R P) P = P :=
  ⟨safeRel_box_eq R P, box_safeRel_eq R P⟩

/-- One-step preservation extends to the full reflexive-transitive closure. -/
theorem preserves_to_forwardInvariant {α : Type}
    {R : α → α → Prop} {Q : α → Prop} (h : Preserves R Q) :
    ForwardInvariant R Q := by
  intro x y hx hxy
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact h _ _ hstep ih

/-! ## Actual semantic repair poset -/

/-- A repair point consists of an actual retained relation and retained predicate. -/
structure RepairSystem (α : Type u) where
  rel : α → α → Prop
  pred : α → Prop

/-- Product inclusion: a larger repair retains at least as many edges and states. -/
def RepairLE {α : Type u} (A B : RepairSystem α) : Prop :=
  RelationLE A.rel B.rel ∧ PredicateLE A.pred B.pred

instance repairSystemLE {α : Type u} : LE (RepairSystem α) := ⟨RepairLE⟩

/-- The semantic repair order is a genuine partial order on relation/predicate pairs. -/
instance repairSystemPartialOrder {α : Type u} : PartialOrder (RepairSystem α) where
  le_refl A := ⟨fun _ _ h => h, fun _ h => h⟩
  le_trans A B C hAB hBC :=
    ⟨fun x y h => hBC.1 x y (hAB.1 x y h),
      fun x h => hBC.2 x (hAB.2 x h)⟩
  le_antisymm A B hAB hBA := by
    cases A with
    | mk relA predA =>
      cases B with
      | mk relB predB =>
        have hrel : relA = relB := by
          funext x y
          apply propext
          exact ⟨fun h => hAB.1 x y h, fun h => hBA.1 x y h⟩
        have hpred : predA = predB := by
          funext x
          apply propext
          exact ⟨fun h => hAB.2 x h, fun h => hBA.2 x h⟩
        cases hrel
        cases hpred
        rfl

/-- A stable repair of `(R,P)` keeps only raw edges/states and its retained
relation preserves its retained predicate. -/
def IsStableRepair {α : Type u} (R : α → α → Prop) (P : α → Prop)
    (A : RepairSystem α) : Prop :=
  RelationLE A.rel R ∧ PredicateLE A.pred P ∧ Preserves A.rel A.pred

/-- Dynamics-side endpoint: keep all licensed states and maximally retain safe edges. -/
def dynamicsRepair {α : Type u} (R : α → α → Prop) (P : α → Prop) :
    RepairSystem α :=
  ⟨SafeRel R P, P⟩

/-- State-side endpoint: keep all dynamics and retain the greatest persistent sublicense. -/
def predicateRepair {α : Type} (R : α → α → Prop) (P : α → Prop) :
    RepairSystem α :=
  ⟨R, Box R P⟩

/-- The dynamics endpoint is a stable repair. -/
theorem dynamicsRepair_stable {α : Type u} (R : α → α → Prop) (P : α → Prop) :
    IsStableRepair R P (dynamicsRepair R P) :=
  ⟨safeRel_subset R P, (fun _ h => h), safeRel_preserves R P⟩

/-- The predicate endpoint is a stable repair. -/
theorem predicateRepair_stable {α : Type} (R : α → α → Prop) (P : α → Prop) :
    IsStableRepair R P (predicateRepair R P) := by
  refine ⟨(fun _ _ h => h), (fun _ h => h.holds), ?_⟩
  intro x y hxy hx
  exact box_forwardInvariant hx (Relation.ReflTransGen.single hxy)

/-- Endpoint maximality on the dynamics-only fiber: any `S ⊆ R` preserving the
full predicate lies below `SafeRel R P`. -/
theorem dynamicsRepair_greatest_with_fullPredicate {α : Type u}
    {R S : α → α → Prop} {P : α → Prop}
    (hsub : RelationLE S R) (hpres : Preserves S P) :
    (RepairSystem.mk S P) ≤ dynamicsRepair R P :=
  ⟨safeRel_greatest hsub hpres, fun _ h => h⟩

/-- Endpoint maximality on the predicate-only fiber: every forward-invariant
`Q ⊆ P` lies below `Box R P`. -/
theorem predicateRepair_greatest_with_fullDynamics {α : Type}
    {R : α → α → Prop} {P Q : α → Prop}
    (hsub : PredicateLE Q P) (hpres : Preserves R Q) :
    (RepairSystem.mk R Q) ≤ predicateRepair R P := by
  refine ⟨(fun _ _ h => h), ?_⟩
  intro x hx
  exact box_greatest (fun q hq => hsub q hq) (preserves_to_forwardInvariant hpres) hx

/-! ## A concrete stable frontier with incomparable endpoint repairs -/

/-- The dynamics endpoint deletes the fixture crossing. -/
theorem fixture_dynamicsRepair_deletes_crossing :
    ¬ SafeRel failureFixtureStep failureFixturePredicate
      FailureFixtureState.safe FailureFixtureState.failed :=
  (boundaryEdge_removed_by_safeRel
    (R := failureFixtureStep) (P := failureFixturePredicate)
    (x := FailureFixtureState.safe) (y := FailureFixtureState.failed)
    ⟨⟨rfl, rfl⟩, rfl, by intro h; cases h⟩).2

/-- The state endpoint loses the fixture source because the raw edge reaches failure. -/
theorem fixture_source_not_box :
    ¬ Box failureFixtureStep failureFixturePredicate FailureFixtureState.safe := by
  intro hbox
  have hfail := hbox.persists FailureFixtureState.failed
    (Relation.ReflTransGen.single (show failureFixtureStep
      FailureFixtureState.safe FailureFixtureState.failed from ⟨rfl, rfl⟩))
  cases hfail

/-- The two canonical stable repairs on the same carrier are genuinely incomparable.

The state repair retains the crossing edge but loses the source state; the
dynamics repair keeps the source state but deletes the crossing edge. -/
theorem fixture_endpoint_repairs_incomparable :
    ¬ predicateRepair failureFixtureStep failureFixturePredicate ≤
        dynamicsRepair failureFixtureStep failureFixturePredicate ∧
    ¬ dynamicsRepair failureFixtureStep failureFixturePredicate ≤
        predicateRepair failureFixtureStep failureFixturePredicate := by
  constructor
  · intro hle
    exact fixture_dynamicsRepair_deletes_crossing
      (hle.1 FailureFixtureState.safe FailureFixtureState.failed
        (show failureFixtureStep FailureFixtureState.safe FailureFixtureState.failed
          from ⟨rfl, rfl⟩))
  · intro hle
    exact fixture_source_not_box
      (hle.2 FailureFixtureState.safe (show failureFixturePredicate FailureFixtureState.safe from rfl))

/-- Nonvacuity package: both incomparable endpoints are stable repairs of the
same real relation/predicate pair. -/
theorem fixture_real_stable_repair_frontier :
    IsStableRepair failureFixtureStep failureFixturePredicate
      (predicateRepair failureFixtureStep failureFixturePredicate) ∧
    IsStableRepair failureFixtureStep failureFixturePredicate
      (dynamicsRepair failureFixtureStep failureFixturePredicate) ∧
    (¬ predicateRepair failureFixtureStep failureFixturePredicate ≤
        dynamicsRepair failureFixtureStep failureFixturePredicate) ∧
    (¬ dynamicsRepair failureFixtureStep failureFixturePredicate ≤
        predicateRepair failureFixtureStep failureFixturePredicate) :=
  ⟨predicateRepair_stable _ _, dynamicsRepair_stable _ _, fixture_endpoint_repairs_incomparable⟩

end OperatorKO7.Meta.LicensedBoundaryCalculus
