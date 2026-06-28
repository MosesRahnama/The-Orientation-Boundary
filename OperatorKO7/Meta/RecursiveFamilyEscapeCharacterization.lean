import OperatorKO7.Meta.DirectWholeTermObserver

/-!
# Recursive Family Escape Characterization (Phase F.5, schema-generic side)

Schema-generic half of the escape-route characterization. This module turns the
Phase B unconditional barrier theorem into a positive disjunctive
classification at the family level: if any `DirectWholeTermObserver` globally
orients a `DuplicatingRecursiveFamily`, then for every payload coordinate at
least one of the four Phase B preconditions fails. The disjunction is
captured by the inductive `DirectObserverEscape` and packaged as the
`RecursiveFamilyEscapeCharacterization` structure.

This is intentionally a one-way theorem (barrier => escape clause). The
converse direction (escape clause => barrier) is generically false at the
family level because an abstract `DuplicatingRecursiveFamily` may host
orienting observers when, say, the pump field is set to `False` for the
distinguished payload; the converse therefore requires concrete witnesses
and is established only at the KO7 instantiation
(see `Meta/KO7EscapeRouteCharacterization.lean`).

The module preserves every existing public name. It adds:

* `DirectObserverEscape`: the four-clause escape inductive
  (`exposureFailure`, `pumpFailure`, `visibilityFailure`,
  `sensitivityFailure`);
* `RecursiveFamilyEscapeCharacterization F`: the one-way classification
  certificate over a family;
* `recursiveFamily_barrier_implies_escape_one_way`: the central one-way
  classification theorem, proved unconditionally from
  `no_direct_orientation_of_payload_exposure`;
* `recursiveFamily_escape_characterization_certificate`: the canonical
  constructor for the certificate.

No proof placeholders are used and no top-level postulate is declared.
-/

namespace OperatorKO7.StepDuplicating
namespace RecursiveFamilyEscapeCharacterization

/-- The four-clause escape disjunction at the family level. Given a
`DuplicatingRecursiveFamily` `F`, an observer `O`, and a payload coordinate
`i`, the inductive records which of the Phase B preconditions fails at `i`.
A globally orienting observer must fall into at least one clause, since
otherwise `no_direct_orientation_of_payload_exposure` would contradict the
orientation. -/
inductive DirectObserverEscape
    (F : DuplicatingRecursiveFamily)
    (O : DirectWholeTermObserver F)
    (i : F.schema.PayloadCoord) : Prop
  /-- The family does not strictly expose the payload at coordinate `i`. -/
  | exposureFailure :
      ¬ F.ExposesPayloadStrictly i → DirectObserverEscape F O i
  /-- The family does not pump the payload at coordinate `i`. -/
  | pumpFailure :
      ¬ F.HasUnboundedPayloadPump i → DirectObserverEscape F O i
  /-- The observer does not see the payload at coordinate `i`. -/
  | visibilityFailure :
      ¬ O.visiblePayloadCoordinate i → DirectObserverEscape F O i
  /-- The observer is not carrier-sensitive on payload coordinate `i`. -/
  | sensitivityFailure :
      ¬ O.carrierSensitive i → DirectObserverEscape F O i

/-- Schema-generic one-way theorem: if `O` globally orients `F`, then for
every payload coordinate `i` at least one of the four DWO preconditions
fails. The proof is by classical case-split on the four hypotheses; if all
four held, `no_direct_orientation_of_payload_exposure` would refute the
global orientation. -/
theorem recursiveFamily_barrier_implies_escape_one_way
    {F : DuplicatingRecursiveFamily}
    (O : DirectWholeTermObserver F)
    (i : F.schema.PayloadCoord)
    (hOrient : F.GloballyOrients O) :
    DirectObserverEscape F O i := by
  classical
  by_cases hExp : F.ExposesPayloadStrictly i
  · by_cases hPump : F.HasUnboundedPayloadPump i
    · by_cases hVis : O.visiblePayloadCoordinate i
      · by_cases hSens : O.carrierSensitive i
        · exact False.elim <|
            (no_direct_orientation_of_payload_exposure
              (F := F) O hPump hExp hVis hSens) hOrient
        · exact DirectObserverEscape.sensitivityFailure hSens
      · exact DirectObserverEscape.visibilityFailure hVis
    · exact DirectObserverEscape.pumpFailure hPump
  · exact DirectObserverEscape.exposureFailure hExp

/-- The packaged schema-generic escape-route characterization at a family.
Carries the one-way map from "orienting observer at coordinate `i`" to "at
least one DWO assumption fails at `i`". -/
structure RecursiveFamilyEscapeCharacterization
    (F : DuplicatingRecursiveFamily) : Prop where
  /-- One-way map: any orienting observer falls into one of the four
  Phase B escape clauses at every payload coordinate. -/
  one_way :
    ∀ (O : DirectWholeTermObserver F)
      (i : F.schema.PayloadCoord),
      F.GloballyOrients O → DirectObserverEscape F O i

/-- Canonical constructor: every duplicating recursive family admits the
schema-generic one-way escape characterization unconditionally. -/
theorem recursiveFamily_escape_characterization_certificate
    (F : DuplicatingRecursiveFamily) :
    RecursiveFamilyEscapeCharacterization F where
  one_way := fun O i hOrient =>
    recursiveFamily_barrier_implies_escape_one_way (F := F) O i hOrient

end RecursiveFamilyEscapeCharacterization
end OperatorKO7.StepDuplicating
