import OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary
import OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure
import OperatorKO7.Meta.InformationTheoreticConfession
import OperatorKO7.Meta.ConfessionMethod_UniversalInstances

/-!
# Universal characterisation gives universal witness-channel deficit (Informational Incompleteness, Corollary 8.x / `cor:univ-deficit-via-char`)

`cor:univ-deficit-via-char`: the witness-channel deficit at the direct interface is
universal, holding against the entire H-equivalence class of the canonical
confession move rather than against one representative. The corollary combines two
established sides:

* DIRECT side: at the orientation boundary the direct certificate interface is
  empty, so the witness-channel deficit there is positive
  (`WitnessChannelBoundary`), and on the recursor every orienting semantic measure
  is counter-dominated (`RecursorPayloadErasure`), so no direct measure resolves it.
* ESCAPE side: each of the four theorem-backed confession routes refines the
  canonical move, hence provides a sound certificate at its interface. This is the
  gauge-fixing identity applied to the four-route H-equivalence, so the resolution
  is the single canonical class.

## Audit slots

```
Relation: schema-level witness tower + confession-move surface; not a rewriting
          relation.
Closure:  not applicable.
Trust:    kernel-only.
Scope:    the recursor direct deficit and the four theorem-backed confession routes.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.UnivDeficitViaChar

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower
open OperatorKO7.Meta.InformationalIncompleteness.WitnessChannelBoundary
open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity

/--
Proves: (`cor:univ-deficit-via-char`, direct side) at the orientation boundary the
  witness-channel deficit at the direct interface is positive and the minimal
  witness order exceeds the direct order.
Does not prove: the escape side; see the route-refinement declarations below.
Relation: schema-level witness tower.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every tower and instance at the orientation boundary.
-/
theorem univ_deficit_via_char_direct
    {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (Tw : SchemaWitnessTower S) (x : S.T) (hOB : OB Tw x) :
    witnessChannelDeficitPos Tw x ∧ minimalWitnessOrderGtDirect Tw x :=
  ⟨(OB_iff_no_directWhole Tw x).mp hOB, hOB⟩

/--
Proves: (`cor:univ-deficit-via-char`, recursor direct measures) on the recursor
  every orienting semantic measure is counter-dominated, so no direct semantic
  measure resolves the direct-interface deficit. TOTAL over arbitrary semantic
  measures.
Does not prove: existence of an orienting measure; it constrains those that orient.
Relation: the canonical II recursor.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `SemanticMeasureData (Nat × Nat)` orienting the recursor.
-/
theorem univ_deficit_via_char_recursor
    (M : SemanticMeasureData (Nat × Nat))
    (hOrient : Orients RecursorPayloadErasure.iiRecursor M.μ M.ltA) :
    CounterDominated RecursorPayloadErasure.iiRecursor M :=
  RecursorPayloadErasure.iiRecursor_orienting_measure_counter_dominated M hOrient

/-- Escape side: the dependency-pair route refines the canonical confession move
(a sound certificate at its interface), from the four-route H-equivalence via the
gauge-fixing identity. -/
def univ_deficit_via_char_dp_route_refines :=
  (OperatorKO7.Meta.InformationTheoreticConfession.gauge_fixing_identity
    (OperatorKO7.Meta.ConfessionMethodUniversalInstances.all_existing_confession_routes_are_HEquivalent_to_canonical).1).1

/-- Escape side: the counter-projection route refines the canonical move. -/
def univ_deficit_via_char_ctr_route_refines :=
  (OperatorKO7.Meta.InformationTheoreticConfession.gauge_fixing_identity
    (OperatorKO7.Meta.ConfessionMethodUniversalInstances.all_existing_confession_routes_are_HEquivalent_to_canonical).2.1).1

/-- Escape side: the size-change-termination route refines the canonical move. -/
def univ_deficit_via_char_sct_route_refines :=
  (OperatorKO7.Meta.InformationTheoreticConfession.gauge_fixing_identity
    (OperatorKO7.Meta.ConfessionMethodUniversalInstances.all_existing_confession_routes_are_HEquivalent_to_canonical).2.2.1).1

/-- Escape side: the argument-filtering route refines the canonical move. -/
def univ_deficit_via_char_af_route_refines :=
  (OperatorKO7.Meta.InformationTheoreticConfession.gauge_fixing_identity
    (OperatorKO7.Meta.ConfessionMethodUniversalInstances.all_existing_confession_routes_are_HEquivalent_to_canonical).2.2.2).1

/-- Audit anchor for the universal-deficit-via-characterisation surface. -/
def univ_deficit_via_char_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.UnivDeficitViaChar.univ_deficit_via_char_direct"

end OperatorKO7.Meta.InformationalIncompleteness.UnivDeficitViaChar
