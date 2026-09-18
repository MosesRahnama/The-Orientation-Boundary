import OperatorKO7.Meta.RDRSReflectedDirectMeasureDSL

/-!
# Mechanically inspectable directness for RDRS direct measures

`Meta/RDRSSemanticDirectMeasure.lean` records directness as five caller-selected `Prop` fields with
caller-supplied proofs. Nothing there ties those propositions to the body of the measure, and
`natConstantDirectMeasure` instantiates all five with `True`. This module supplies the tier that
does have content.

## What is actually proved here

A `MechanicalDirectMeasure` is *closed code*: a single `NatMeasureExpr` field, no `Prop` attestation
fields at all, with evaluation definitionally `code.eval`. Directness is then not attested but
derived, in one precise and deliberately modest sense:

> the evaluator's output is extensionally independent of every slot of an explicitly modeled
> `RouteEnvironment`, which carries a rewrite oracle, a transformed relation, a semantic quotient,
> a dependency-pair processor, and an external-proof artifact.

Each route slot pairs a typed payload with an explicit `Bool` discriminator, so the slot is
constructively non-subsingleton even where the payload's function domain is empty
(`routeEnvironment_slot_nonSubsingleton`). `DifferOnlyAt` is extensional: the discriminator at the
selected route differs while every other discriminator and every typed payload is equal. For each
of the five routes an explicit pair of environments inhabiting `DifferOnlyAt` is constructed, so
`NoRouteDependence` carries its own non-vacuity and is not true merely because no variation exists.

## What is deliberately *not* proved here

This is **closed-code and extensional route-input independence, never historical provenance.** The
theorems say: given the five modeled explicit inputs, varying any one of them leaves the evaluator's
value unchanged. They do not say, and cannot say, how an arbitrary Lean function was constructed,
whether its author consulted a rewrite oracle while writing it, or that some unmodeled side channel
is absent. Route inputs outside the five modeled slots are outside the claim.

## Image strictness

Every `NatMeasureExpr` evaluator is payload-monotone. A non-monotone `SemanticDirectMeasure`
carrying the *same five* nondependence propositions and proofs is constructed, and proved not to be
in the mechanical image. So the mechanical tier is strictly stronger than the semantic certificate
tier: the semantic tier admits measures the mechanical tier cannot express.

## Formal scope

```text
Relation: counterFirstLexRaw_R on Nat x Nat for the classifier corollaries; the route-independence
          theorems are about evaluation only and name no rewriting relation.
Closure:  root single-step where a relation is named at all.
Strategy: not applicable.
Trust:    kernel-only. No sorry, admit, axiom, constant, opaque, unsafe, extern, implemented_by,
          @[csimp], native_decide, bv_decide, or addDeclWithoutChecking.
Imports:  one-way. This file imports the reflected DSL (and through it the semantic file). Neither
          the reflected DSL nor the semantic file imports this file.
```
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSMechanicalDirectness

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticNormalizedRawSyntax
open OperatorKO7.RDRSReflectedDirectMeasureDSL

/-! ## 1. The mechanical measure: closed code, no attestation fields -/

/-- A mechanically inspectable direct measure. The only field is closed reflected code; there is no
caller-chosen `Prop` slot anywhere in this structure, so nothing about it can be self-attested. -/
structure MechanicalDirectMeasure where
  /-- The closed reflected direct-measure code. -/
  code : NatMeasureExpr

/-- Evaluation of a mechanical measure is definitionally the reflected interpreter. -/
def MechanicalDirectMeasure.eval (M : MechanicalDirectMeasure) : Nat × Nat → Nat :=
  M.code.eval

/-- Evaluation is definitionally `code.eval`; nothing is inserted between them. -/
theorem MechanicalDirectMeasure.eval_def (M : MechanicalDirectMeasure) :
    M.eval = M.code.eval := rfl

/-! ## 2. Modeled forbidden-route inputs -/

/-- The five modeled route inputs a direct measure must not consume. -/
inductive ForbiddenRoute where
  /-- A rewrite-closure or term-algebra oracle. -/
  | rewriteOracle
  /-- A transformed relation such as a dependency-pair problem. -/
  | transformedRelation
  /-- An arbitrary semantic quotient used as the payload-forgetting mechanism. -/
  | semanticQuotient
  /-- A dependency-pair processor. -/
  | dpProcessor
  /-- An external proof language or unchecked proof artifact. -/
  | externalProof
deriving DecidableEq, Repr

/-- An explicit environment of modeled route inputs. Every slot carries a typed payload together
with a `Bool` discriminator. The discriminator is what makes the slot constructively
non-subsingleton: a payload whose function domain happens to be empty would otherwise collapse to a
single inhabitant and make every nondependence statement vacuous. -/
structure RouteEnvironment where
  /-- Discriminator for the rewrite-oracle slot. -/
  rewriteOracleFlag : Bool
  /-- Typed payload for the rewrite-oracle slot: a decided rewrite relation on coordinates. -/
  rewriteOracle : Nat × Nat → Nat × Nat → Bool
  /-- Discriminator for the transformed-relation slot. -/
  transformedRelationFlag : Bool
  /-- Typed payload for the transformed-relation slot. -/
  transformedRelation : Nat × Nat → Nat × Nat → Bool
  /-- Discriminator for the semantic-quotient slot. -/
  semanticQuotientFlag : Bool
  /-- Typed payload for the semantic-quotient slot: a quotient code on coordinates. -/
  semanticQuotient : Nat × Nat → Nat
  /-- Discriminator for the DP-processor slot. -/
  dpProcessorFlag : Bool
  /-- Typed payload for the DP-processor slot: a coordinate projection. -/
  dpProcessor : Nat × Nat → Nat × Nat
  /-- Discriminator for the external-proof slot. -/
  externalProofFlag : Bool
  /-- Typed payload for the external-proof slot: an unchecked artifact. -/
  externalProof : String

/-- The discriminator of the named route slot. -/
def RouteEnvironment.flag (E : RouteEnvironment) : ForbiddenRoute → Bool
  | .rewriteOracle => E.rewriteOracleFlag
  | .transformedRelation => E.transformedRelationFlag
  | .semanticQuotient => E.semanticQuotientFlag
  | .dpProcessor => E.dpProcessorFlag
  | .externalProof => E.externalProofFlag

/-- A baseline environment with every discriminator off and every payload trivial. -/
def baseRouteEnvironment : RouteEnvironment where
  rewriteOracleFlag := false
  rewriteOracle := fun _ _ => false
  transformedRelationFlag := false
  transformedRelation := fun _ _ => false
  semanticQuotientFlag := false
  semanticQuotient := fun _ => 0
  dpProcessorFlag := false
  dpProcessor := fun p => p
  externalProofFlag := false
  externalProof := ""

/-- Flip exactly one discriminator, leaving every payload and every other discriminator fixed. -/
def toggleRoute (E : RouteEnvironment) : ForbiddenRoute → RouteEnvironment
  | .rewriteOracle => { E with rewriteOracleFlag := !E.rewriteOracleFlag }
  | .transformedRelation => { E with transformedRelationFlag := !E.transformedRelationFlag }
  | .semanticQuotient => { E with semanticQuotientFlag := !E.semanticQuotientFlag }
  | .dpProcessor => { E with dpProcessorFlag := !E.dpProcessorFlag }
  | .externalProof => { E with externalProofFlag := !E.externalProofFlag }

/-! ## 3. Coordinate projection, lifted evaluation, and extensional route variation -/

/-- A generic term type equipped with a coordinate projection into the canonical
`(counter, payload)` carrier. -/
structure CoordinateProjection (T : Type) where
  /-- The coordinate reading of a term. -/
  coords : T → Nat × Nat

/-- Lifted evaluation: it factors through the coordinates and ignores the route environment by
construction. The route environment is a bound variable the body never mentions. -/
def liftedEval {T : Type} (P : CoordinateProjection T) (e : NatMeasureExpr)
    (t : T) (_E : RouteEnvironment) : Nat :=
  e.eval (P.coords t)

/-- Generic route-blind lifting of any coordinate-free evaluator. -/
def liftedOf {T : Type} (f : T → Nat) (t : T) (_E : RouteEnvironment) : Nat := f t

/-- An evaluator whose output may, in general, depend on the modeled route environment. -/
abbrev RouteEvaluator (T : Type) := T → RouteEnvironment → Nat

/-- Lifted evaluation is the route-blind lifting of the coordinate reading. -/
theorem liftedEval_eq_liftedOf {T : Type} (P : CoordinateProjection T) (e : NatMeasureExpr)
    (t : T) (E : RouteEnvironment) :
    liftedEval P e t E = liftedOf (fun s => e.eval (P.coords s)) t E := rfl

/-- **Extensional single-route variation.** The discriminator at `r` differs, while every other
discriminator and every typed payload agrees. -/
def DifferOnlyAt (r : ForbiddenRoute) (E1 E2 : RouteEnvironment) : Prop :=
  E1.flag r ≠ E2.flag r
    ∧ (∀ r' : ForbiddenRoute, r' ≠ r → E1.flag r' = E2.flag r')
    ∧ E1.rewriteOracle = E2.rewriteOracle
    ∧ E1.transformedRelation = E2.transformedRelation
    ∧ E1.semanticQuotient = E2.semanticQuotient
    ∧ E1.dpProcessor = E2.dpProcessor
    ∧ E1.externalProof = E2.externalProof

/-- An evaluator essentially depends on a route when some single-route variation moves its value. -/
def EssentiallyDependsOnRoute {T : Type} (f : RouteEvaluator T)
    (r : ForbiddenRoute) : Prop :=
  ∃ (t : T) (E1 E2 : RouteEnvironment),
    DifferOnlyAt r E1 E2 ∧ f t E1 ≠ f t E2

/-- **Nondependence, with its own non-vacuity.** The class of single-route variations at `r` is
inhabited, and the evaluator agrees across every one of them. The first conjunct is what stops this
from being true merely because no variation exists. -/
def NoRouteDependence {T : Type} (f : RouteEvaluator T) (r : ForbiddenRoute) : Prop :=
  (∃ E1 E2 : RouteEnvironment, DifferOnlyAt r E1 E2) ∧
    ∀ (t : T) (E1 E2 : RouteEnvironment),
      DifferOnlyAt r E1 E2 → f t E1 = f t E2

/-! ## 4. Inhabited variations, factorization, and the five nondependence theorems -/

/-- Every route slot is constructively non-subsingleton: the discriminator separates two
environments even though every typed payload is identical. -/
theorem routeEnvironment_slot_nonSubsingleton (r : ForbiddenRoute) :
    ∃ E1 E2 : RouteEnvironment, E1.flag r ≠ E2.flag r := by
  refine ⟨baseRouteEnvironment, toggleRoute baseRouteEnvironment r, ?_⟩
  cases r <;> decide

/-- Explicit single-route variation for every route. -/
theorem differOnlyAt_base_toggle (r : ForbiddenRoute) :
    DifferOnlyAt r baseRouteEnvironment (toggleRoute baseRouteEnvironment r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases r <;> decide
  · intro r' hr'
    cases r <;> cases r' <;>
      simp_all [RouteEnvironment.flag, toggleRoute, baseRouteEnvironment]
  · cases r <;> rfl
  · cases r <;> rfl
  · cases r <;> rfl
  · cases r <;> rfl
  · cases r <;> rfl

/-- **The variation class is inhabited at every route.** -/
theorem forbiddenRoute_variation_exists (r : ForbiddenRoute) :
    ∃ E1 E2 : RouteEnvironment, DifferOnlyAt r E1 E2 :=
  ⟨baseRouteEnvironment, toggleRoute baseRouteEnvironment r, differOnlyAt_base_toggle r⟩

/-- A route-sensitive control evaluator. It reads the selected discriminator, showing that
`EssentiallyDependsOnRoute` is itself inhabited and is not definitionally impossible. -/
def selectedRouteFlagEval (r : ForbiddenRoute) : RouteEvaluator Unit :=
  fun _ E => if E.flag r then 1 else 0

/-- The route-sensitive control genuinely depends on every selected route. -/
theorem selectedRouteFlagEval_essentiallyDependsOnRoute (r : ForbiddenRoute) :
    EssentiallyDependsOnRoute (selectedRouteFlagEval r) r := by
  refine ⟨(), baseRouteEnvironment, toggleRoute baseRouteEnvironment r,
    differOnlyAt_base_toggle r, ?_⟩
  cases r <;> decide

/-- **Generic coordinate factorization.** Lifted evaluation depends on the term only through its
coordinates, and on the environment not at all. -/
theorem liftedEval_factors_through_coords {T : Type} (P : CoordinateProjection T)
    (e : NatMeasureExpr) (t : T) (E : RouteEnvironment) :
    liftedEval P e t E = e.eval (P.coords t) := rfl

/-- **Generic locality.** Terms with equal coordinates evaluate equally, under any environments. -/
theorem liftedEval_local {T : Type} (P : CoordinateProjection T) (e : NatMeasureExpr)
    (t t' : T) (E1 E2 : RouteEnvironment) (h : P.coords t = P.coords t') :
    liftedEval P e t E1 = liftedEval P e t' E2 := by
  simp only [liftedEval, h]

/-- Generic route-blindness of any coordinate-free evaluator, with the inhabited variation. -/
theorem noRouteDependence_of_routeBlind {T : Type} (f : T → Nat) (r : ForbiddenRoute) :
    NoRouteDependence (liftedOf f) r :=
  ⟨forbiddenRoute_variation_exists r, fun _ _ _ _ => rfl⟩

/-- Nondependence implies the negation of essential dependence. -/
theorem not_essentiallyDependsOnRoute {T : Type} {f : RouteEvaluator T} {r : ForbiddenRoute}
    (h : NoRouteDependence f r) : ¬ EssentiallyDependsOnRoute f r := by
  rintro ⟨t, E1, E2, hdiff, hne⟩
  exact hne (h.2 t E1 E2 hdiff)

/-- The coordinate reading of a mechanical measure through a projection. -/
def mechanicalCoordEval {T : Type} (P : CoordinateProjection T)
    (M : MechanicalDirectMeasure) : RouteEvaluator T :=
  liftedEval P M.code

/-- Nondependence on the rewrite oracle. -/
theorem mechanical_noRewriteOracle {T : Type} (P : CoordinateProjection T)
    (M : MechanicalDirectMeasure) :
    NoRouteDependence (mechanicalCoordEval P M) .rewriteOracle :=
  noRouteDependence_of_routeBlind (fun t => M.code.eval (P.coords t)) _

/-- Nondependence on a transformed relation. -/
theorem mechanical_noTransformedRelation {T : Type} (P : CoordinateProjection T)
    (M : MechanicalDirectMeasure) :
    NoRouteDependence (mechanicalCoordEval P M) .transformedRelation :=
  noRouteDependence_of_routeBlind (fun t => M.code.eval (P.coords t)) _

/-- Nondependence on an arbitrary semantic quotient. -/
theorem mechanical_noSemanticQuotient {T : Type} (P : CoordinateProjection T)
    (M : MechanicalDirectMeasure) :
    NoRouteDependence (mechanicalCoordEval P M) .semanticQuotient :=
  noRouteDependence_of_routeBlind (fun t => M.code.eval (P.coords t)) _

/-- Nondependence on a dependency-pair processor. -/
theorem mechanical_noDPProcessor {T : Type} (P : CoordinateProjection T)
    (M : MechanicalDirectMeasure) :
    NoRouteDependence (mechanicalCoordEval P M) .dpProcessor :=
  noRouteDependence_of_routeBlind (fun t => M.code.eval (P.coords t)) _

/-- Nondependence on an external proof artifact. -/
theorem mechanical_noExternalProof {T : Type} (P : CoordinateProjection T)
    (M : MechanicalDirectMeasure) :
    NoRouteDependence (mechanicalCoordEval P M) .externalProof :=
  noRouteDependence_of_routeBlind (fun t => M.code.eval (P.coords t)) _

/-- All five together, for every generic coordinate projection. -/
theorem mechanical_noRouteDependence_all {T : Type} (P : CoordinateProjection T)
    (M : MechanicalDirectMeasure) (r : ForbiddenRoute) :
    NoRouteDependence (mechanicalCoordEval P M) r :=
  noRouteDependence_of_routeBlind (fun t => M.code.eval (P.coords t)) _

/-! ### Canonical `Nat × Nat` corollary

The identity projection is a corollary of the generic statements above, never the headline. -/

/-- The identity coordinate projection on the canonical carrier. -/
def natPairProjection : CoordinateProjection (Nat × Nat) where
  coords := fun p => p

/-- Corollary: on the canonical carrier the lifted evaluator is the interpreter itself. -/
theorem natPair_liftedEval_eq_eval (e : NatMeasureExpr) (p : Nat × Nat)
    (E : RouteEnvironment) :
    liftedEval natPairProjection e p E = e.eval p := rfl

/-- Corollary: the canonical coordinate reading of a mechanical measure is its evaluator. -/
theorem natPair_mechanicalCoordEval_eq_eval (M : MechanicalDirectMeasure)
    (p : Nat × Nat) (E : RouteEnvironment) :
    mechanicalCoordEval natPairProjection M p E = M.eval p := rfl

/-! ## 5. Bridge to the legacy semantic certificate -/

/-- Convert a mechanical measure into the legacy `SemanticDirectMeasure` interface.

The five legacy evidence propositions are **exactly** the five nondependence propositions above,
carrying their proofs. No field is `True`.

This proves extensional independence from the five modeled explicit route inputs. It does **not**
prove historical provenance: nothing here constrains how an arbitrary Lean function was constructed,
and route inputs outside the five modeled slots are outside the claim. -/
def toSemanticDirectMeasure (M : MechanicalDirectMeasure) :
    SemanticDirectMeasure (Nat × Nat) where
  data := reflectedMeasureData M.code
  direct :=
    { kind := DirectEvidenceKind.constructorLocalObservation
      note :=
        "closed reflected code; extensional independence from the five modeled route inputs"
      noRewriteOracle :=
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .rewriteOracle
      noRewriteOracle_proof := mechanical_noRewriteOracle natPairProjection M
      noTransformedRelation :=
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .transformedRelation
      noTransformedRelation_proof := mechanical_noTransformedRelation natPairProjection M
      noArbitrarySemanticQuotient :=
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .semanticQuotient
      noArbitrarySemanticQuotient_proof := mechanical_noSemanticQuotient natPairProjection M
      noDPProcessor :=
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .dpProcessor
      noDPProcessor_proof := mechanical_noDPProcessor natPairProjection M
      noExternalProofLanguage :=
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .externalProof
      noExternalProofLanguage_proof := mechanical_noExternalProof natPairProjection M }

/-- The bridge preserves the measure function definitionally. -/
theorem toSemanticDirectMeasure_mu (M : MechanicalDirectMeasure) :
    (toSemanticDirectMeasure M).data.μ = M.eval := rfl

/-- The bridged certificate's evidence propositions are the nondependence propositions, not `True`. -/
theorem toSemanticDirectMeasure_evidence_is_nondependence (M : MechanicalDirectMeasure) :
    (toSemanticDirectMeasure M).direct.noRewriteOracle =
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .rewriteOracle ∧
      (toSemanticDirectMeasure M).direct.noTransformedRelation =
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .transformedRelation ∧
      (toSemanticDirectMeasure M).direct.noArbitrarySemanticQuotient =
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .semanticQuotient ∧
      (toSemanticDirectMeasure M).direct.noDPProcessor =
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .dpProcessor ∧
      (toSemanticDirectMeasure M).direct.noExternalProofLanguage =
        NoRouteDependence (mechanicalCoordEval natPairProjection M) .externalProof :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 6. Image strictness -/

/-- Payload monotonicity on the canonical carrier. -/
def PayloadMonotoneOnPairs (f : Nat × Nat → Nat) : Prop :=
  ∀ c p p' : Nat, p ≤ p' → f (c, p) ≤ f (c, p')

/-- **Every reflected evaluator is payload-monotone.** -/
theorem natMeasureExpr_eval_payloadMonotone (e : NatMeasureExpr) :
    PayloadMonotoneOnPairs e.eval := by
  intro c p p' h
  have hmul : e.payloadCoeff * p ≤ e.payloadCoeff * p' :=
    Nat.mul_le_mul (Nat.le_refl e.payloadCoeff) h
  simp only [NatMeasureExpr.eval]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.le_refl (e.counterCoeff * c)) hmul)
    (Nat.le_refl e.constCoeff)

/-- Every mechanical measure is payload-monotone. -/
theorem mechanical_eval_payloadMonotone (M : MechanicalDirectMeasure) :
    PayloadMonotoneOnPairs M.eval :=
  natMeasureExpr_eval_payloadMonotone M.code

/-- A non-monotone measure function: it drops as the payload coordinate rises. -/
def nonMonotonePayloadMu (p : Nat × Nat) : Nat :=
  if p.snd = 0 then 1 else 0

/-- The non-monotone function evaluates to one at payload zero. -/
theorem nonMonotonePayloadMu_at_zero : nonMonotonePayloadMu (0, 0) = 1 := rfl

/-- The non-monotone function evaluates to zero at payload one. -/
theorem nonMonotonePayloadMu_at_one : nonMonotonePayloadMu (0, 1) = 0 := rfl

/-- The non-monotone function is genuinely not payload-monotone. -/
theorem nonMonotonePayloadMu_not_payloadMonotone :
    ¬ PayloadMonotoneOnPairs nonMonotonePayloadMu := by
  intro h
  have hle := h 0 0 1 (by omega)
  rw [nonMonotonePayloadMu_at_zero, nonMonotonePayloadMu_at_one] at hle
  omega

/-- A `SemanticDirectMeasure` carrying the **same five** nondependence propositions and proofs as
the mechanical bridge, but whose measure function is not payload-monotone. -/
def nonMonotoneSemanticDirectMeasure : SemanticDirectMeasure (Nat × Nat) where
  data :=
    { A := Nat
      ltA := fun a b => a < b
      wf_ltA := Nat.lt_wfRel.wf
      μ := nonMonotonePayloadMu }
  direct :=
    { kind := DirectEvidenceKind.constructorLocalObservation
      note :=
        "non-monotone payload reading with the same five route-nondependence proofs"
      noRewriteOracle := NoRouteDependence (liftedOf nonMonotonePayloadMu) .rewriteOracle
      noRewriteOracle_proof := noRouteDependence_of_routeBlind _ _
      noTransformedRelation := NoRouteDependence (liftedOf nonMonotonePayloadMu) .transformedRelation
      noTransformedRelation_proof := noRouteDependence_of_routeBlind _ _
      noArbitrarySemanticQuotient :=
        NoRouteDependence (liftedOf nonMonotonePayloadMu) .semanticQuotient
      noArbitrarySemanticQuotient_proof := noRouteDependence_of_routeBlind _ _
      noDPProcessor := NoRouteDependence (liftedOf nonMonotonePayloadMu) .dpProcessor
      noDPProcessor_proof := noRouteDependence_of_routeBlind _ _
      noExternalProofLanguage := NoRouteDependence (liftedOf nonMonotonePayloadMu) .externalProof
      noExternalProofLanguage_proof := noRouteDependence_of_routeBlind _ _ }

/-- Membership in the image of the mechanical tier. -/
def InMechanicalImage (M : SemanticDirectMeasure (Nat × Nat)) : Prop :=
  ∃ (hNat : M.data.A = Nat) (D : MechanicalDirectMeasure),
    ∀ p : Nat × Nat, cast hNat (M.data.μ p) = D.eval p

/-- Every bridged mechanical measure is in the mechanical image, so the image is inhabited. -/
theorem toSemanticDirectMeasure_inMechanicalImage (M : MechanicalDirectMeasure) :
    InMechanicalImage (toSemanticDirectMeasure M) :=
  ⟨rfl, M, fun _ => rfl⟩

/-- **Strict image.** The non-monotone semantic measure carries the same five nondependence
propositions and proofs, yet is not in the mechanical image: no reflected code evaluates to a
payload-decreasing function. The mechanical tier is therefore strictly stronger than the semantic
certificate tier. -/
theorem nonMonotoneSemanticDirectMeasure_not_inMechanicalImage :
    ¬ InMechanicalImage nonMonotoneSemanticDirectMeasure := by
  rintro ⟨hNat, D, hEq⟩
  have hNat_eq : hNat = rfl := Subsingleton.elim _ _
  apply nonMonotonePayloadMu_not_payloadMonotone
  have hmono := mechanical_eval_payloadMonotone D
  intro c p p' h
  have h1 : nonMonotonePayloadMu (c, p) = D.eval (c, p) := by
    simpa [hNat_eq] using hEq (c, p)
  have h2 : nonMonotonePayloadMu (c, p') = D.eval (c, p') := by
    simpa [hNat_eq] using hEq (c, p')
  rw [h1, h2]
  exact hmono c p p' h

/-- The semantic certificate tier is strictly larger than the mechanical image. -/
theorem mechanical_image_is_strict :
    (∃ M : SemanticDirectMeasure (Nat × Nat), ¬ InMechanicalImage M) ∧
      (∃ M : SemanticDirectMeasure (Nat × Nat), InMechanicalImage M) :=
  ⟨⟨nonMonotoneSemanticDirectMeasure, nonMonotoneSemanticDirectMeasure_not_inMechanicalImage⟩,
    ⟨toSemanticDirectMeasure ⟨NatMeasureExpr.counter⟩,
      toSemanticDirectMeasure_inMechanicalImage _⟩⟩

/-! ## 7. Classifier connection and non-vacuity -/

/-- The reflected classifier label of a mechanical measure, by construction on its closed code. -/
def MechanicalDirectMeasure.label (M : MechanicalDirectMeasure) : ReflectedMeasureLabel :=
  reflectedClassify M.code

/-- Every mechanical measure receives a label. -/
theorem mechanical_label_total (M : MechanicalDirectMeasure) :
    M.label = ReflectedMeasureLabel.counterDominatedOrientation ∨
      M.label = ReflectedMeasureLabel.payloadSensitiveBlocked ∨
        M.label = ReflectedMeasureLabel.payloadBlindNotOrienting :=
  reflectedClassify_total M.code

/-- The counter projection as a mechanical measure. -/
def counterProjectionMechanicalMeasure : MechanicalDirectMeasure where
  code := NatMeasureExpr.counter

/-- Non-vacuity: the mechanical tier is inhabited. -/
theorem mechanicalDirectMeasure_nonvacuous : Nonempty MechanicalDirectMeasure :=
  ⟨counterProjectionMechanicalMeasure⟩

/-- The counter projection is classified as counter-dominated orientation. -/
theorem counterProjectionMechanicalMeasure_label :
    counterProjectionMechanicalMeasure.label =
      ReflectedMeasureLabel.counterDominatedOrientation := by
  decide

/-- **Non-vacuity witness with content.** The counter projection is a mechanical measure whose
classifier label is counter-dominated, and the reflected soundness theorem then gives its
orientation and counter-domination on `counterFirstLexRaw_R`. -/
theorem counterProjectionMechanicalMeasure_orients :
    Orients counterFirstLexRaw_R
        (reflectedMeasureData counterProjectionMechanicalMeasure.code).μ
        (reflectedMeasureData counterProjectionMechanicalMeasure.code).ltA ∧
      CounterDominated counterFirstLexRaw_R
        (reflectedMeasureData counterProjectionMechanicalMeasure.code) :=
  reflectedClassify_counter_sound counterProjectionMechanicalMeasure.code
    counterProjectionMechanicalMeasure_label

/-- Stable declaration-name string for the mechanical directness tier. -/
def rdrs_mechanical_directness_anchor : String :=
  "OperatorKO7.RDRSMechanicalDirectness.MechanicalDirectMeasure"

end OperatorKO7.RDRSMechanicalDirectness
