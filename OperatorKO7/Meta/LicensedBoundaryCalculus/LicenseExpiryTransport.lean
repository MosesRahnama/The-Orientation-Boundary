/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryCategory

/-!
# Pairwise transport for the three live license-expiry objects

Intent: decide every ordered transport between the equality-coalescence,
quote/evaluation, and role-erasure expiry objects. Five directions are blocked
by a concrete preservation law. The sixth direction, equality-coalescence to
quote/evaluation, is constructed through a natural-number rank of the live
root dynamics.

The rank is not guessed. `EqGuardedStep` is well-founded in reverse and has a
unique target at each source. Well-founded recursion therefore assigns every
root state the length of its unique remaining root path, and every guarded
root step lowers that rank by one. Componentwise addition grades `PairStep`.
A canonical chain of merge-redexes then realizes that grade inside the
under-quotation dynamics.

The second half adds closure and consumption operations. The three concrete
full objects use identity closure and the distinguished consume state as their
canonical terminal consumption. Every ordinary expiry morphism therefore
lifts to a full morphism, so the six-way table survives the refinement.

Relation: `PairStep`, `QuoteEvalStep true`, and `RoleCollapseStep`.
Closure: one-step transport in the first half; reflexive-transitive reach in
`ExpiryObjectFull.close_reaches`.
Strategy: unrestricted root dynamics.
External trust: Mathlib baseline only.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryTransport

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.DistinctionBoundary.GodelPartial
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryCategory

universe u v w

/-! ## Elementary obstruction lemmas -/

/-- The role-erasure consume state has a genuine dynamics self-loop. -/
theorem role_consume_self_loop :
    roleExpiry.dynamics roleExpiry.consume roleExpiry.consume :=
  rfl

/-- No componentwise guarded step leaves the equality-coalescence consume
state. -/
theorem no_pairStep_from_consume {p : Trace × Trace} :
    ¬ PairStep (void, void) p := by
  intro h
  cases h with
  | left hL => exact eqGuardedStep_not_void hL
  | right hR => exact eqGuardedStep_not_void hR

/-- No quote/evaluation step leaves the quote consume state. -/
theorem no_quoteStep_from_consume {c : QuoteEvalCfg} :
    ¬ QuoteEvalStep true (.value void) c :=
  no_step_from_value

/-- A role-collapse step can never land at an active occurrence. -/
theorem roleCollapseStep_target_not_active {Y : Type u} {x y : Occ Y}
    (hxy : RoleCollapseStep x y) : ¬ isActive y := by
  intro hy
  rw [hxy] at hy
  exact Role.noConfusion hy

/-- Every successor of the equality-coalescence issue is its consume state.
The three overlapping merge constructors agree on that target, and the right
component `void` has no root successor. -/
theorem pairStep_from_issue_unique {p : Trace × Trace}
    (h : PairStep (merge void void, void) p) : p = (void, void) := by
  cases h with
  | left hL =>
      have ht : _ = void := eqGuarded_unique_target hL merge_void_void_steps_void
      cases ht
      rfl
  | right hR =>
      exact (eqGuardedStep_not_void hR).elim

/-! ## Five negative ordered pairs -/

/-- Role expiry cannot map to equality expiry: the source consume state has a
self-loop, while the target consume state has no outgoing `PairStep`. -/
theorem no_hom_role_eqW : IsEmpty (Hom roleExpiry eqWExpiry) := by
  refine ⟨?_⟩
  intro f
  have hstep := f.dynamics_preserve role_consume_self_loop
  rw [f.consume_map] at hstep
  exact no_pairStep_from_consume hstep

/-- Role expiry cannot map to quote expiry: the source consume state has a
self-loop, while a quote value has no outgoing step. -/
theorem no_hom_role_quote : IsEmpty (Hom roleExpiry quoteExpiry) := by
  refine ⟨?_⟩
  intro f
  have hstep := f.dynamics_preserve role_consume_self_loop
  rw [f.consume_map] at hstep
  exact no_quoteStep_from_consume hstep

/-- Equality expiry cannot map to role expiry. A concrete `PairStep` lands at a
still-distinct target, so license preservation makes the target active, while
dynamics preservation makes it the frame-valued role collapse of its source. -/
theorem no_hom_eqW_role : IsEmpty (Hom eqWExpiry roleExpiry) := by
  refine ⟨?_⟩
  intro f
  let p : Trace × Trace := (merge void (delta void), void)
  let q : Trace × Trace := (delta void, void)
  have hpq : PairStep p q := PairStep.left (EqGuardedStep.R_merge_void_left _)
  have hqDistinct : Distinct q := by
    intro h
    cases h
  have hactive : isActive (f.toFun q) := f.license_preserve hqDistinct
  have hcollapse : RoleCollapseStep (f.toFun p) (f.toFun q) :=
    f.dynamics_preserve hpq
  exact roleCollapseStep_target_not_active hcollapse hactive

/-- Quote expiry cannot map to role expiry. The under-quotation arm lands at a
configuration that remains reducible, hence licensed, but every role-collapse
target is inactive. -/
theorem no_hom_quote_role : IsEmpty (Hom quoteExpiry roleExpiry) := by
  refine ⟨?_⟩
  intro f
  have htargetLicensed : QuoteReducible (.evalQuoted void void) :=
    ⟨.diverged, freeze_peak_eval_diverge⟩
  have hactive : isActive (f.toFun (.evalQuoted void void)) :=
    f.license_preserve htargetLicensed
  have hcollapse : RoleCollapseStep (f.toFun freezePeakSource)
      (f.toFun (.evalQuoted void void)) :=
    f.dynamics_preserve freeze_peak_under_quote
  exact roleCollapseStep_target_not_active hcollapse hactive

/-- Quote expiry cannot map to equality expiry. The first arm out of the quote
issue is forced to the equality consume state; the following diverging arm
would then require an impossible step out of that consume state. -/
theorem no_hom_quote_eqW : IsEmpty (Hom quoteExpiry eqWExpiry) := by
  refine ⟨?_⟩
  intro f
  have hfirst : PairStep eqWExpiry.issue (f.toFun (.evalQuoted void void)) := by
    rw [← f.issue_map]
    exact f.dynamics_preserve freeze_peak_under_quote
  have htarget : f.toFun (.evalQuoted void void) = eqWExpiry.consume :=
    pairStep_from_issue_unique hfirst
  have hsecond := f.dynamics_preserve freeze_peak_eval_diverge
  rw [htarget] at hsecond
  exact no_pairStep_from_consume hsecond

/-! ## The positive ordered pair: equality expiry to quote expiry -/

/-- A guarded-root rank obtained by well-founded recursion. Determinism of the
root target makes the recursive successor independent of the existential
witness chosen by the definition. -/
noncomputable def eqGuardedRank : Trace → Nat := by
  classical
  exact wf_EqGuardedStepRev.fix fun t rec =>
    if h : ∃ u, EqGuardedStep t u then
      rec (Classical.choose h) (Classical.choose_spec h) + 1
    else
      0

/-- Every guarded root step lowers `eqGuardedRank` by one. -/
theorem eqGuardedRank_step {t u : Trace} (h : EqGuardedStep t u) :
    eqGuardedRank t = eqGuardedRank u + 1 := by
  unfold eqGuardedRank
  rw [WellFounded.fix_eq]
  let hex : ∃ v, EqGuardedStep t v := ⟨u, h⟩
  rw [dif_pos hex]
  have hchoose : Classical.choose hex = u :=
    eqGuarded_unique_target (Classical.choose_spec hex) h
  have hRank : eqGuardedRank (Classical.choose hex) = eqGuardedRank u :=
    congrArg eqGuardedRank hchoose
  change eqGuardedRank (Classical.choose hex) + 1 = eqGuardedRank u + 1
  exact congrArg (fun n => n + 1) hRank

/-- The guarded root relation is genuinely graded by a natural number. -/
theorem eqGuardedStep_graded :
    ∃ d : Trace → Nat, ∀ {t u}, EqGuardedStep t u → d t = d u + 1 :=
  ⟨eqGuardedRank, fun h => eqGuardedRank_step h⟩

/-- Add the two component ranks. -/
noncomputable def pairRank (p : Trace × Trace) : Nat :=
  eqGuardedRank p.1 + eqGuardedRank p.2

/-- Every componentwise pair step lowers the pair rank by one. -/
theorem pairRank_step {p q : Trace × Trace} (h : PairStep p q) :
    pairRank p = pairRank q + 1 := by
  cases h with
  | left hL =>
      simp only [pairRank, eqGuardedRank_step hL]
      omega
  | right hR =>
      simp only [pairRank, eqGuardedRank_step hR]
      omega

/-- The pair dynamics is naturally graded. -/
theorem pairStep_graded :
    ∃ d : Trace × Trace → Nat,
      ∀ {p q}, PairStep p q → d p = d q + 1 :=
  ⟨pairRank, fun h => pairRank_step h⟩

/-- The normal root `void` has rank zero. -/
theorem eqGuardedRank_void : eqGuardedRank void = 0 := by
  unfold eqGuardedRank
  rw [WellFounded.fix_eq]
  have hnone : ¬ ∃ u, EqGuardedStep void u := by
    rintro ⟨u, hu⟩
    exact eqGuardedStep_not_void hu
  rw [dif_neg hnone]

/-- The equality-expiry consume state has pair rank zero. -/
theorem pairRank_consume : pairRank (void, void) = 0 := by
  simp [pairRank, eqGuardedRank_void]

/-- The coalescing merge redex has root rank one. -/
theorem eqGuardedRank_merge_void_void :
    eqGuardedRank (merge void void) = 1 := by
  rw [eqGuardedRank_step merge_void_void_steps_void, eqGuardedRank_void]

/-- The equality-expiry issue state has pair rank one. -/
theorem pairRank_issue : pairRank (merge void void, void) = 1 := by
  simp [pairRank, eqGuardedRank_merge_void_void, eqGuardedRank_void]

/-- Canonical merge chain realizing every positive rank in the quote dynamics. -/
def rankChain : Nat → Trace
  | 0 => void
  | n + 1 => merge void (rankChain n)

/-- The canonical chain takes one guarded root step at every successor. -/
theorem rankChain_succ_step (n : Nat) :
    EqGuardedStep (rankChain (n + 1)) (rankChain n) :=
  EqGuardedStep.R_merge_void_left (rankChain n)

/-- Every quoted rank-chain state is reducible: rank zero diverges, and every
positive rank has an enabled under-quotation step. -/
theorem rankChain_quoteReducible (n : Nat) :
    QuoteReducible (.evalQuoted (rankChain n) void) := by
  cases n with
  | zero =>
      exact ⟨.diverged, QuoteEvalStep.evalDiverge quote_void_diverges_at_void⟩
  | succ n =>
      exact ⟨.evalQuoted (rankChain n) void,
        QuoteEvalStep.underQuote rfl (rankChain_succ_step n)⟩

/-- State map from equality expiry into quote expiry. The equality consume
state maps to the quote value; every other pair maps to a quoted rank-chain
state. -/
noncomputable def eqWToQuoteMap (p : Trace × Trace) : QuoteEvalCfg :=
  if p = (void, void) then .value void
  else .evalQuoted (rankChain (pairRank p)) void

/-- The equality issue maps to the quote issue. -/
theorem eqWToQuoteMap_issue :
    eqWToQuoteMap (merge void void, void) = freezePeakSource := by
  simp [eqWToQuoteMap, pairRank_issue, rankChain, freezePeakSource]

/-- The equality consume state maps to the quote consume state. -/
theorem eqWToQuoteMap_consume :
    eqWToQuoteMap (void, void) = .value void := by
  simp [eqWToQuoteMap]

/-- Disequality implies that the mapped quote configuration is reducible. -/
theorem eqWToQuoteMap_license {p : Trace × Trace} (hp : Distinct p) :
    QuoteReducible (eqWToQuoteMap p) := by
  have hne : p ≠ (void, void) := by
    intro h
    subst p
    exact hp rfl
  rw [eqWToQuoteMap, if_neg hne]
  exact rankChain_quoteReducible (pairRank p)

/-- Every `PairStep` is transported to one quote/evaluation step. Steps into
the equality consume state use the converging arm of the quote peak; all other
steps use the rank-chain under-quotation arm. -/
theorem eqWToQuoteMap_step {p q : Trace × Trace} (h : PairStep p q) :
    QuoteEvalStep true (eqWToQuoteMap p) (eqWToQuoteMap q) := by
  have hpne : p ≠ (void, void) := by
    intro hp
    subst p
    exact no_pairStep_from_consume h
  by_cases hq : q = (void, void)
  · subst q
    have hrank : pairRank p = 1 := by
      rw [pairRank_step h, pairRank_consume]
    rw [eqWToQuoteMap, if_neg hpne, eqWToQuoteMap_consume, hrank]
    exact freeze_peak_eval_converge
  · rw [eqWToQuoteMap, if_neg hpne, eqWToQuoteMap, if_neg hq]
    rw [pairRank_step h]
    exact QuoteEvalStep.underQuote rfl (rankChain_succ_step (pairRank q))

/-- The sixth ordered pair lands: equality-coalescence expiry maps into the
quote/evaluation expiry through the graded rank-chain construction. -/
noncomputable def hom_eqW_quote : Hom eqWExpiry quoteExpiry where
  toFun := eqWToQuoteMap
  issue_map := eqWToQuoteMap_issue
  consume_map := eqWToQuoteMap_consume
  dynamics_preserve := eqWToQuoteMap_step
  license_preserve := eqWToQuoteMap_license

/-! ## Typed transport table -/

/-- The law names used by the negative transport catalog. -/
inductive ExpiryTransportLaw
  | dynamicsPreservation
  | licensePreservation
  | issueMap
  | consumeMap
deriving DecidableEq, Repr

/-- The three live expiry objects as a finite catalog. -/
inductive ExpiryKind
  | eqW
  | quote
  | role
deriving DecidableEq, Repr

/-- Catalog of the first failing law for every ordered pair. `none` means that
a morphism is supplied in this module or that the source and target coincide. -/
def failingLaw : ExpiryKind → ExpiryKind → Option ExpiryTransportLaw
  | .role, .eqW => some .dynamicsPreservation
  | .role, .quote => some .dynamicsPreservation
  | .eqW, .role => some .licensePreservation
  | .quote, .role => some .licensePreservation
  | .quote, .eqW => some .dynamicsPreservation
  | _, _ => none

@[simp] theorem failingLaw_role_eqW :
    failingLaw .role .eqW = some .dynamicsPreservation := rfl
@[simp] theorem failingLaw_role_quote :
    failingLaw .role .quote = some .dynamicsPreservation := rfl
@[simp] theorem failingLaw_eqW_role :
    failingLaw .eqW .role = some .licensePreservation := rfl
@[simp] theorem failingLaw_quote_role :
    failingLaw .quote .role = some .licensePreservation := rfl
@[simp] theorem failingLaw_quote_eqW :
    failingLaw .quote .eqW = some .dynamicsPreservation := rfl
@[simp] theorem failingLaw_eqW_quote :
    failingLaw .eqW .quote = none := rfl

/-- Complete six-way transport table: five typed obstructions and one concrete
morphism. -/
theorem expiry_pairwise_transport_table :
    IsEmpty (Hom roleExpiry eqWExpiry) ∧
    IsEmpty (Hom roleExpiry quoteExpiry) ∧
    IsEmpty (Hom eqWExpiry roleExpiry) ∧
    IsEmpty (Hom quoteExpiry roleExpiry) ∧
    IsEmpty (Hom quoteExpiry eqWExpiry) ∧
    Nonempty (Hom eqWExpiry quoteExpiry) :=
  ⟨no_hom_role_eqW, no_hom_role_quote, no_hom_eqW_role,
    no_hom_quote_role, no_hom_quote_eqW, ⟨hom_eqW_quote⟩⟩

/-! ## Closure and consumption refinement -/

/-- Full expiry data add a closure operation and a distinguished consumption
operation to the live expiry object. -/
structure ExpiryObjectFull extends ExpiryObject.{u} where
  close : Carrier → Carrier
  consumeOp : Carrier → Carrier
  close_idem : ∀ x, close (close x) = close x
  close_reaches : ∀ x, Relation.ReflTransGen dynamics x (close x)
  consumeOp_issue : consumeOp issue = consume
  commutes : consumeOp (close issue) = close consume

/-- Full morphisms preserve the ordinary expiry data, closure, and consumption. -/
structure HomFull (A : ExpiryObjectFull.{u}) (B : ExpiryObjectFull.{v})
    extends Hom A.toExpiryObject B.toExpiryObject where
  close_map : ∀ x, toFun (A.close x) = B.close (toFun x)
  consumeOp_map : ∀ x, toFun (A.consumeOp x) = B.consumeOp (toFun x)

namespace HomFull

/-- Identity full morphism. -/
def id (A : ExpiryObjectFull.{u}) : HomFull A A where
  toHom := Hom.id A.toExpiryObject
  close_map := fun _ => rfl
  consumeOp_map := fun _ => rfl

/-- Composition of full morphisms. -/
def comp {A : ExpiryObjectFull.{u}} {B : ExpiryObjectFull.{v}}
    {C : ExpiryObjectFull.{w}} (f : HomFull A B) (g : HomFull B C) :
    HomFull A C where
  toHom := Hom.comp f.toHom g.toHom
  close_map := by
    intro x
    change g.toFun (f.toFun (A.close x)) = C.close (g.toFun (f.toFun x))
    rw [f.close_map, g.close_map]
  consumeOp_map := by
    intro x
    change g.toFun (f.toFun (A.consumeOp x)) = C.consumeOp (g.toFun (f.toFun x))
    rw [f.consumeOp_map, g.consumeOp_map]

/-- Left identity for full expiry morphisms. -/
theorem id_comp {A B : ExpiryObjectFull.{u}} (f : HomFull A B) :
    comp (id A) f = f := by
  cases f
  rfl

/-- Right identity for full expiry morphisms. -/
theorem comp_id {A B : ExpiryObjectFull.{u}} (f : HomFull A B) :
    comp f (id B) = f := by
  cases f
  rfl

/-- Associativity for full expiry morphisms. -/
theorem comp_assoc {A B C D : ExpiryObjectFull.{u}}
    (f : HomFull A B) (g : HomFull B C) (h : HomFull C D) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f
  cases g
  cases h
  rfl

end HomFull

/-- Canonical full refinement of any expiry object: identity closure and a
terminal consumption operation that returns the distinguished consume state. -/
def canonicalFull (A : ExpiryObject.{u}) : ExpiryObjectFull.{u} where
  toExpiryObject := A
  close := id
  consumeOp := fun _ => A.consume
  close_idem := fun _ => rfl
  close_reaches := fun _ => Relation.ReflTransGen.refl
  consumeOp_issue := rfl
  commutes := rfl

/-- Every ordinary expiry morphism lifts to the canonical full refinement. -/
def liftHom {A : ExpiryObject.{u}} {B : ExpiryObject.{v}} (f : Hom A B) :
    HomFull (canonicalFull A) (canonicalFull B) where
  toHom := f
  close_map := fun _ => rfl
  consumeOp_map := fun _ => f.consume_map

/-- Forget the closure and consumption fields of a full morphism. -/
def homFull_to_hom {A : ExpiryObjectFull.{u}} {B : ExpiryObjectFull.{v}}
    (f : HomFull A B) : Hom A.toExpiryObject B.toExpiryObject :=
  f.toHom

/-- Full equality-coalescence expiry object. -/
def eqWExpiryFull : ExpiryObjectFull := canonicalFull eqWExpiry

/-- Full quote/evaluation expiry object. -/
def quoteExpiryFull : ExpiryObjectFull := canonicalFull quoteExpiry

/-- Full role-erasure expiry object. -/
def roleExpiryFull : ExpiryObjectFull := canonicalFull roleExpiry

/-- The positive equality-to-quote transport survives the full refinement. -/
noncomputable def homFull_eqW_quote : HomFull eqWExpiryFull quoteExpiryFull :=
  liftHom hom_eqW_quote

/-- Negative full transport: role to equality. -/
theorem no_homFull_role_eqW : IsEmpty (HomFull roleExpiryFull eqWExpiryFull) := by
  refine ⟨?_⟩
  intro f
  exact no_hom_role_eqW.false (homFull_to_hom f)

/-- Negative full transport: role to quote. -/
theorem no_homFull_role_quote : IsEmpty (HomFull roleExpiryFull quoteExpiryFull) := by
  refine ⟨?_⟩
  intro f
  exact no_hom_role_quote.false (homFull_to_hom f)

/-- Negative full transport: equality to role. -/
theorem no_homFull_eqW_role : IsEmpty (HomFull eqWExpiryFull roleExpiryFull) := by
  refine ⟨?_⟩
  intro f
  exact no_hom_eqW_role.false (homFull_to_hom f)

/-- Negative full transport: quote to role. -/
theorem no_homFull_quote_role : IsEmpty (HomFull quoteExpiryFull roleExpiryFull) := by
  refine ⟨?_⟩
  intro f
  exact no_hom_quote_role.false (homFull_to_hom f)

/-- Negative full transport: quote to equality. -/
theorem no_homFull_quote_eqW : IsEmpty (HomFull quoteExpiryFull eqWExpiryFull) := by
  refine ⟨?_⟩
  intro f
  exact no_hom_quote_eqW.false (homFull_to_hom f)

/-- Category laws for the full expiry refinement. -/
theorem expiry_full_category_laws :
    (∀ {A B : ExpiryObjectFull.{u}} (f : HomFull A B),
      HomFull.comp (HomFull.id A) f = f) ∧
    (∀ {A B : ExpiryObjectFull.{u}} (f : HomFull A B),
      HomFull.comp f (HomFull.id B) = f) ∧
    (∀ {A B C D : ExpiryObjectFull.{u}}
      (f : HomFull A B) (g : HomFull B C) (h : HomFull C D),
      HomFull.comp (HomFull.comp f g) h =
        HomFull.comp f (HomFull.comp g h)) :=
  ⟨HomFull.id_comp, HomFull.comp_id, HomFull.comp_assoc⟩

/-- The complete six-way table survives closure and consumption refinement. -/
theorem expiry_full_pairwise_transport_table :
    IsEmpty (HomFull roleExpiryFull eqWExpiryFull) ∧
    IsEmpty (HomFull roleExpiryFull quoteExpiryFull) ∧
    IsEmpty (HomFull eqWExpiryFull roleExpiryFull) ∧
    IsEmpty (HomFull quoteExpiryFull roleExpiryFull) ∧
    IsEmpty (HomFull quoteExpiryFull eqWExpiryFull) ∧
    Nonempty (HomFull eqWExpiryFull quoteExpiryFull) :=
  ⟨no_homFull_role_eqW, no_homFull_role_quote, no_homFull_eqW_role,
    no_homFull_quote_role, no_homFull_quote_eqW, ⟨homFull_eqW_quote⟩⟩

end OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryTransport
