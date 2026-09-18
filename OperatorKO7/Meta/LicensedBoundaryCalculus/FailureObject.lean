import OperatorKO7.Meta.DistinctionBoundary.PersistentLicense

/-!
# Failure as a first-class boundary object

The constructive surface uses an exact proof-relevant finite path.  A
`FailureObject` is indexed by that exact path and records a safe prefix, the
first `P`-to-`¬P` crossing edge, and the remaining suffix.  Global failure of
the existing `PersistentLicense.Box` is handled separately: proof-level
reachability yields `Nonempty` path data rather than an invalid proof-to-data
eliminator.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense

universe u

/-- An exact one-step boundary crossing. -/
def BoundaryEdge {α : Type u} (R : α → α → Prop) (P : α → Prop)
    (x y : α) : Prop :=
  R x y ∧ P x ∧ ¬ P y

/-- A proof-relevant finite path whose first edge is explicit. -/
inductive FinitePath {α : Type u} (R : α → α → Prop) : α → α → Type u
  | refl (x : α) : FinitePath R x x
  | cons {x y z : α} (edge : R x y) (tail : FinitePath R y z) :
      FinitePath R x z

namespace FinitePath

/-- Concatenate exact finite paths. -/
def append {α : Type u} {R : α → α → Prop} {a b c : α} :
    FinitePath R a b → FinitePath R b c → FinitePath R a c
  | .refl _, q => q
  | .cons h t, q => .cons h (append t q)

/-- Forget proof-relevant path syntax to ordinary reflexive-transitive reachability. -/
theorem toReflTransGen {α : Type u} {R : α → α → Prop} {a b : α}
    (p : FinitePath R a b) : Relation.ReflTransGen R a b := by
  induction p with
  | refl => exact Relation.ReflTransGen.refl
  | cons h _ ih => exact Relation.ReflTransGen.head h ih

/-- A proof-level reachability derivation guarantees existence of exact path data.

The codomain is `Nonempty`, hence remains in `Prop`; this avoids an invalid
elimination from proof-level `ReflTransGen` into path data. -/
theorem nonempty_ofReflTransGen {α : Type u} {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) : Nonempty (FinitePath R a b) := by
  induction h with
  | refl => exact ⟨.refl _⟩
  | tail _ hlast ih =>
      rcases ih with ⟨p⟩
      exact ⟨append p (.cons hlast (.refl _))⟩

/-- Every state occurring in a path satisfies `P`. -/
inductive All {α : Type u} {R : α → α → Prop} (P : α → Prop) :
    {a b : α} → FinitePath R a b → Prop
  | refl {x : α} (hx : P x) : All P (.refl x)
  | cons {x y z : α} {h : R x y} {tail : FinitePath R y z}
      (hx : P x) (htail : All P tail) : All P (.cons h tail)

/-- The source of an all-safe path is safe. -/
theorem All.source {α : Type u} {R : α → α → Prop} {P : α → Prop}
    {a b : α} {p : FinitePath R a b} (h : All P p) : P a := by
  cases h with
  | refl hx => exact hx
  | cons hx _ => exact hx

/-- The endpoint of an all-safe path is safe. -/
theorem All.endpoint {α : Type u} {R : α → α → Prop} {P : α → Prop}
    {a b : α} {p : FinitePath R a b} (h : All P p) : P b := by
  induction h with
  | refl hx => exact hx
  | cons _ _ ih => exact ih

end FinitePath

/-- A proof-relevant failed path indexed by the exact audited path. -/
structure FailureObject {α : Type u} (R : α → α → Prop) (P : α → Prop)
    (source endpoint : α) (path : FinitePath R source endpoint) : Type u where
  /-- Last point on the audited prefix where `P` still holds. -/
  lastSafe : α
  /-- First point after that prefix where `P` fails. -/
  firstFail : α
  /-- The source really starts inside the licensed region. -/
  sourceSafe : P source
  /-- The audited endpoint really fails the license. -/
  endpointFails : ¬ P endpoint
  /-- Prefix ending at the last safe point. -/
  safePrefix : FinitePath R source lastSafe
  /-- Every state on the safe prefix satisfies the license. -/
  safePrefixProof : FinitePath.All P safePrefix
  /-- The actual crossing edge, carrying both endpoint predicates. -/
  crossing : BoundaryEdge R P lastSafe firstFail
  /-- Remaining path after the first failing point. -/
  suffix : FinitePath R firstFail endpoint
  /-- The indexed path is exactly safe-prefix, crossing, suffix. -/
  decomposition :
    path = FinitePath.append safePrefix (.cons crossing.1 suffix)

namespace FailureObject

/-- The stored edge is a genuine boundary edge. -/
theorem crossing_is_boundary {α : Type u} {R : α → α → Prop} {P : α → Prop}
    {source endpoint : α} {path : FinitePath R source endpoint}
    (f : FailureObject R P source endpoint path) :
    BoundaryEdge R P f.lastSafe f.firstFail :=
  f.crossing

/-- Everything before the first crossing, including the last safe point, satisfies `P`. -/
theorem prefix_is_safe {α : Type u} {R : α → α → Prop} {P : α → Prop}
    {source endpoint : α} {path : FinitePath R source endpoint}
    (f : FailureObject R P source endpoint path) :
    FinitePath.All P f.safePrefix :=
  f.safePrefixProof

/-- The crossing really occurs in the exact audited path. -/
theorem crossing_lies_on_path {α : Type u} {R : α → α → Prop} {P : α → Prop}
    {source endpoint : α} {path : FinitePath R source endpoint}
    (f : FailureObject R P source endpoint path) :
    path = FinitePath.append f.safePrefix (.cons f.crossing.1 f.suffix) :=
  f.decomposition

/-- The indexed path yields ordinary reachability. -/
theorem reachable_endpoint {α : Type u} {R : α → α → Prop} {P : α → Prop}
    {source endpoint : α} {path : FinitePath R source endpoint}
    (_f : FailureObject R P source endpoint path) :
    Relation.ReflTransGen R source endpoint :=
  FinitePath.toReflTransGen path

/-- Constructively, an explicit failed path has a first crossing.

Only `DecidablePred P` is used; no classical principle is hidden here. -/
theorem of_explicit_path {α : Type u} {R : α → α → Prop} {P : α → Prop}
    [DecidablePred P] {source endpoint : α}
    (path : FinitePath R source endpoint) (hsource : P source)
    (hend : ¬ P endpoint) : Nonempty (FailureObject R P source endpoint path) := by
  induction path with
  | refl x => exact False.elim (hend hsource)
  | @cons x y z edge tail ih =>
      by_cases hy : P y
      · rcases ih hy hend with ⟨f⟩
        refine ⟨{
          lastSafe := f.lastSafe
          firstFail := f.firstFail
          sourceSafe := hsource
          endpointFails := hend
          safePrefix := .cons edge f.safePrefix
          safePrefixProof := .cons hsource f.safePrefixProof
          crossing := f.crossing
          suffix := f.suffix
          decomposition := ?_ }⟩
        exact congrArg (fun q => FinitePath.cons edge q) f.decomposition
      · refine ⟨{
          lastSafe := x
          firstFail := y
          sourceSafe := hsource
          endpointFails := hend
          safePrefix := .refl x
          safePrefixProof := .refl hsource
          crossing := ⟨edge, hsource, hy⟩
          suffix := tail
          decomposition := rfl }⟩

/-! The current `PersistentLicense.Box` donor is universe-0 (`α : Type`), so the
bridge theorems below intentionally use that exact live scope. -/

/-- Any concrete failure object refutes persistence at its source. -/
theorem not_box {α : Type} {R : α → α → Prop} {P : α → Prop}
    {source endpoint : α} {path : FinitePath R source endpoint}
    (f : FailureObject R P source endpoint path) :
    ¬ Box R P source := by
  intro hbox
  exact f.endpointFails (hbox.persists endpoint f.reachable_endpoint)

/-- Classical global failure produces a concrete reachable failing endpoint. -/
theorem not_box_exists_reachable_failure_classical
    {α : Type} {R : α → α → Prop} {P : α → Prop} {source : α}
    (hsource : P source) (hnot : ¬ Box R P source) :
    ∃ endpoint, Relation.ReflTransGen R source endpoint ∧ ¬ P endpoint := by
  classical
  by_contra hnone
  apply hnot
  refine ⟨hsource, ?_⟩
  intro endpoint hreach
  by_contra hfail
  apply hnone
  exact ⟨endpoint, hreach, hfail⟩

/-- The endpoint form is exactly equivalent to failure of `Box` at a licensed source. -/
theorem not_box_iff_exists_reachable_failure_classical
    {α : Type} {R : α → α → Prop} {P : α → Prop} {source : α}
    (hsource : P source) :
    (¬ Box R P source) ↔
      ∃ endpoint, Relation.ReflTransGen R source endpoint ∧ ¬ P endpoint := by
  constructor
  · exact not_box_exists_reachable_failure_classical hsource
  · rintro ⟨endpoint, hreach, hfail⟩ hbox
    exact hfail (hbox.persists endpoint hreach)

/-- With a decidable license, classical global failure yields existence of exact path-data first crossing. -/
theorem not_box_to_failureObject_classical
    {α : Type} {R : α → α → Prop} {P : α → Prop}
    [DecidablePred P] {source : α} (hsource : P source)
    (hnot : ¬ Box R P source) :
    ∃ endpoint path, Nonempty (FailureObject R P source endpoint path) := by
  obtain ⟨endpoint, hreach, hfail⟩ :=
    not_box_exists_reachable_failure_classical hsource hnot
  obtain ⟨path⟩ := FinitePath.nonempty_ofReflTransGen hreach
  exact ⟨endpoint, path, of_explicit_path path hsource hfail⟩

/-- At a licensed source, `¬Box` is equivalent to existence of an exact first-crossing object. -/
theorem not_box_iff_exists_failureObject_classical
    {α : Type} {R : α → α → Prop} {P : α → Prop}
    [DecidablePred P] {source : α} (hsource : P source) :
    (¬ Box R P source) ↔
      ∃ endpoint path, Nonempty (FailureObject R P source endpoint path) := by
  constructor
  · exact not_box_to_failureObject_classical hsource
  · rintro ⟨endpoint, path, ⟨f⟩⟩
    exact f.not_box

end FailureObject

/-! ## Non-vacuity and hypothesis-necessity fixtures -/

inductive FailureFixtureState where
  | safe
  | failed

/-- A one-edge fixture crossing from safe to failed. -/
def failureFixtureStep (x y : FailureFixtureState) : Prop :=
  x = FailureFixtureState.safe ∧ y = FailureFixtureState.failed

/-- The license holds exactly at the source of the fixture edge. -/
def failureFixturePredicate (x : FailureFixtureState) : Prop :=
  x = FailureFixtureState.safe

/-- The explicit finite path used by the positive fixture. -/
def failureFixturePath :
    FinitePath failureFixtureStep FailureFixtureState.safe FailureFixtureState.failed :=
  .cons ⟨rfl, rfl⟩ (.refl FailureFixtureState.failed)

/-- Positive non-vacuity: an actual first-crossing object for the fixture path. -/
def positiveFailureObject :
    FailureObject failureFixtureStep failureFixturePredicate
      FailureFixtureState.safe FailureFixtureState.failed failureFixturePath where
  lastSafe := FailureFixtureState.safe
  firstFail := FailureFixtureState.failed
  sourceSafe := rfl
  endpointFails := by intro h; cases h
  safePrefix := .refl FailureFixtureState.safe
  safePrefixProof := .refl rfl
  crossing := ⟨⟨rfl, rfl⟩, rfl, by intro h; cases h⟩
  suffix := .refl FailureFixtureState.failed
  decomposition := rfl

/-- The positive fixture stores the actual crossing edge. -/
theorem positiveFailureObject_crosses :
    BoundaryEdge failureFixtureStep failureFixturePredicate
      positiveFailureObject.lastSafe positiveFailureObject.firstFail :=
  positiveFailureObject.crossing

/-- No-expiry fixture: an always-true predicate admits no FailureObject. -/
theorem noFailureObject_when_predicate_true
    {α : Type u} (R : α → α → Prop) (source endpoint : α)
    (path : FinitePath R source endpoint) :
    ¬ Nonempty (FailureObject R (fun _ => True) source endpoint path) := by
  rintro ⟨f⟩
  exact f.endpointFails trivial

/-- Source satisfaction is necessary: endpoint failure plus a path need not contain a crossing. -/
theorem source_satisfaction_is_necessary :
    Nonempty (FinitePath failureFixtureStep FailureFixtureState.safe FailureFixtureState.failed) ∧
      ¬ (fun _ : FailureFixtureState => False) FailureFixtureState.failed ∧
      ¬ ∃ x y, BoundaryEdge failureFixtureStep
        (fun _ : FailureFixtureState => False) x y := by
  refine ⟨⟨failureFixturePath⟩, (fun h => h), ?_⟩
  rintro ⟨x, y, _, hfalse, _⟩
  exact hfalse

/-- Endpoint failure is necessary: a path inside an always-true license has no crossing. -/
theorem endpoint_failure_is_necessary :
    Nonempty (FinitePath failureFixtureStep FailureFixtureState.safe FailureFixtureState.failed) ∧
      (fun _ : FailureFixtureState => True) FailureFixtureState.safe ∧
      ¬ ∃ x y, BoundaryEdge failureFixtureStep
        (fun _ : FailureFixtureState => True) x y := by
  refine ⟨⟨failureFixturePath⟩, trivial, ?_⟩
  rintro ⟨x, y, _, _, hnot⟩
  exact hnot trivial

end OperatorKO7.Meta.LicensedBoundaryCalculus
