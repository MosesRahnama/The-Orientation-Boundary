import OperatorKO7.Meta.DuplicatingRecursiveFamily

/-!
# Direct Whole-Term Observer (Phase B)

Phase B of the recursive-family expansion roadmap. This module adds a parallel
generic direct-observer interface alongside the existing schema and KO7 theorem
surface; no existing theorem name or signature is touched.

The module supplies:

- the `DirectWholeTermObserver` interface over a `DuplicatingRecursiveFamily`,
  with `Carrier`, `eval`, `lt`, `visiblePayloadCoordinate`, `carrierSensitive`,
  `constructorLocal`, `pumpMonotone`, and the strengthened structural field
  `orient_forces_payload_drop`;
- a `DuplicatingRecursiveFamily.GloballyOrients` predicate lifting an observer's
  strict comparison along the family's step relation;
- the unconditional barrier theorem `no_direct_orientation_of_payload_exposure`:
  given a payload coordinate that is exposed strictly by the family, pumped,
  visible to the observer, and on which the observer is carrier-sensitive, the
  observer cannot globally orient the family. The proof discharges from the
  family's `exposure_strict_count` certificate and the observer's
  `orient_forces_payload_drop` certificate, with no theorem-local bridge
  argument;
- the canonical additive direct observer `payloadCountObserver`, whose `eval`
  is the distinguished payload count and whose `lt` is the natural-number
  strict order, instantiating the strengthened observer interface directly;
- the additive corollary `no_additive_orients_dup_step_via_DWO` obtained by
  applying the main theorem to `payloadCountObserver` without any explicit
  bridge hypothesis at the call site.

The observer's structural certificate `orient_forces_payload_drop` is the
proved bridge promoted out of the previous theorem-local hypothesis: it states
that on any coordinate the observer claims to see and on which the observer
claims to be carrier-sensitive, a strict orientation of the rule's rhs over
the rule's lhs forces a strict payload-count drop at that coordinate.
Concrete observers (additive, affine, max-plus, matrix-scalarized, etc.)
discharge this certificate by exhibiting how their carrier value depends on
the relevant payload count.

Existing schema and KO7 theorems are not touched. This module adds a parallel
generic-observer layer only.
-/

namespace OperatorKO7.StepDuplicating

/--
A direct whole-term observer over a `DuplicatingRecursiveFamily`.

The field layout extends the roadmap signature with one structural certificate
field: a carrier type, an evaluator from the family's term carrier into the
observer's carrier, a strict order on that carrier, predicates marking the
payload coordinates the observer can see and is sensitive to, a constructor-
locality flag, a pump-monotonicity predicate per payload coordinate, and a
proof bridge `orient_forces_payload_drop` connecting strict orientation of
the rule to a strict payload-count drop on every visible carrier-sensitive
coordinate. Concrete observers (additive, affine, max-plus, matrix-scalarized,
etc.) refine this interface by specifying the carrier and the order and by
discharging the relevant predicates and the bridge. -/
structure DirectWholeTermObserver (F : DuplicatingRecursiveFamily) where
  /-- The observer's carrier type. -/
  Carrier : Type
  /-- The evaluator from the family's term carrier into the observer's carrier. -/
  eval : F.schema.Term → Carrier
  /-- The observer's strict order on its carrier. -/
  lt : Carrier → Carrier → Prop
  /-- The observer is visible on the named payload coordinate, in a sense to be
  refined by concrete observers (typically: the carrier reflects every payload
  occurrence at that coordinate). -/
  visiblePayloadCoordinate : F.schema.PayloadCoord → Prop
  /-- The observer is carrier-sensitive on the named payload coordinate, in a
  sense to be refined by concrete observers (typically: extra payload
  occurrences strictly change the carrier value). -/
  carrierSensitive : F.schema.PayloadCoord → Prop
  /-- The observer's evaluator is constructor-local, in a sense to be refined by
  concrete observers (typically: `eval` factors through a constructor-by-
  constructor recursion on the term carrier). -/
  constructorLocal : Prop
  /-- The observer is monotone under the family's payload pump on the named
  coordinate, in a sense to be refined by concrete observers. -/
  pumpMonotone : F.schema.PayloadCoord → Prop
  /-- Structural certificate: on every payload coordinate the observer claims
  to see and on which the observer claims to be carrier-sensitive, a strict
  orientation of the rule's rhs below the lhs in the observer forces a strict
  drop in the payload count at that coordinate. Concrete observers discharge
  this from their explicit dependence on `payloadCount`. -/
  orient_forces_payload_drop :
    ∀ {i : F.schema.PayloadCoord},
      visiblePayloadCoordinate i →
        carrierSensitive i →
          lt (eval F.schema.rhs) (eval F.schema.lhs) →
            F.schema.payloadCount i F.schema.rhs <
              F.schema.payloadCount i F.schema.lhs

namespace DuplicatingRecursiveFamily

variable (F : DuplicatingRecursiveFamily)

/-- The observer `O` globally orients the family if every family step `a → b`
strictly decreases the observer's evaluation: `O.lt (O.eval b) (O.eval a)`.

The direction matches the well-founded termination convention: every step makes
the carrier value smaller. -/
def GloballyOrients (O : DirectWholeTermObserver F) : Prop :=
  ∀ {a b : F.schema.Term}, F.Step a b → O.lt (O.eval b) (O.eval a)

end DuplicatingRecursiveFamily

/--
Phase B unconditional barrier theorem.

If a direct whole-term observer `O` over a duplicating recursive family `F`
has a payload coordinate `i` that is pumped (`hPump`), strictly exposed by the
family (`hExposure`), visible to the observer (`hVisible`), and on which the
observer is carrier-sensitive (`hSensitive`), then `O` cannot globally orient
`F`.

The proof combines two structural certificates:

* the family's `exposure_strict_count` turns `hExposure` into a strict
  rhs-over-lhs payload-count rise at coordinate `i`;
* the observer's `orient_forces_payload_drop` turns the hypothetical strict
  orientation at coordinate `i` (entailed by `hVisible`, `hSensitive`, and
  `GloballyOrients`) into a strict rhs-below-lhs payload-count drop at the
  same coordinate.

The two strict comparisons on `Nat` contradict each other via `omega`. No
theorem-local bridge argument is required.

The `hPump` hypothesis is carried as part of the family-level theorem contract
even though it is not arithmetically consumed at Phase B; later phases that
pump beyond one rewrite step exploit it directly. -/
theorem no_direct_orientation_of_payload_exposure
    {F : DuplicatingRecursiveFamily}
    (O : DirectWholeTermObserver F)
    {i : F.schema.PayloadCoord}
    (hPump : F.HasUnboundedPayloadPump i)
    (hExposure : F.ExposesPayloadStrictly i)
    (hVisible : O.visiblePayloadCoordinate i)
    (hSensitive : O.carrierSensitive i) :
    ¬ F.GloballyOrients O := by
  -- `hPump` is part of the contract but not consumed at Phase B.
  let _ := hPump
  intro hOrient
  have hOriented : O.lt (O.eval F.schema.rhs) (O.eval F.schema.lhs) :=
    hOrient F.duplicating_step
  have hRise :
      F.schema.payloadCount i F.schema.lhs <
        F.schema.payloadCount i F.schema.rhs :=
    F.exposure_strict_count hExposure
  have hDrop :
      F.schema.payloadCount i F.schema.rhs <
        F.schema.payloadCount i F.schema.lhs :=
    O.orient_forces_payload_drop hVisible hSensitive hOriented
  omega

/--
The canonical additive direct observer.

`payloadCountObserver F` is the direct whole-term observer whose carrier is
`Nat`, whose evaluator is the distinguished payload count
`F.schema.payloadCount F.distinguishedPayload`, and whose strict order is the
natural-number strict order. The visibility and carrier-sensitivity predicates
fire exactly on the distinguished payload coordinate; `constructorLocal` and
`pumpMonotone` are set to `True` because counting occurrences of a single
named coordinate is, by construction, a constructor-local pump-monotone
operation.

The strengthened structural certificate `orient_forces_payload_drop` is
discharged by rewriting `i` to the distinguished payload coordinate using the
visibility witness and then identifying the observer's strict order with the
natural-number `<` on the distinguished payload count.

This observer is the minimal additive instance against which the direct-
orientation barrier is exhibited. Other named direct classes (additive,
affine, max-plus, matrix-scalarized, etc.) factor through this observer or
through their own refinements of `DirectWholeTermObserver`. -/
def payloadCountObserver (F : DuplicatingRecursiveFamily) :
    DirectWholeTermObserver F where
  Carrier := Nat
  eval := fun t => F.schema.payloadCount F.distinguishedPayload t
  lt := fun m n => m < n
  visiblePayloadCoordinate := fun p => p = F.distinguishedPayload
  carrierSensitive := fun p => p = F.distinguishedPayload
  constructorLocal := True
  pumpMonotone := fun _ => True
  orient_forces_payload_drop := by
    intro i hVisible _hSensitive hOriented
    -- `hVisible` is a propositional equality `i = F.distinguishedPayload`.
    -- Rewrite `i` to the distinguished coordinate so the observer's strict
    -- order reduces to `<` on the distinguished payload count.
    cases hVisible
    exact hOriented

/--
Additive corollary: the canonical payload-count observer cannot globally
orient the duplicating step at the family's distinguished payload coordinate.

The corollary instantiates the strengthened main theorem directly: the family
ships a `distinguished_exposed` witness for the distinguished coordinate, and
`payloadCountObserver F` ships `visiblePayloadCoordinate` and `carrierSensitive`
witnesses (both reduce to `rfl` at the distinguished coordinate) together with
its `orient_forces_payload_drop` certificate.

The corollary uses a new name `no_additive_orients_dup_step_via_DWO` per the
roadmap's stable-theorem-name policy; the existing
`no_additive_orients_dup_step` family-specific theorems in other modules are
left untouched. The hypothesis `hPump` is supplied externally; the family's
distinguished payload coordinate is exposed and visible by construction. -/
theorem no_additive_orients_dup_step_via_DWO
    (F : DuplicatingRecursiveFamily)
    (hPump : F.HasUnboundedPayloadPump F.distinguishedPayload) :
    ¬ F.GloballyOrients (payloadCountObserver F) :=
  no_direct_orientation_of_payload_exposure
    (payloadCountObserver F)
    (i := F.distinguishedPayload)
    hPump
    F.distinguished_exposed
    (rfl)
    (rfl)

end OperatorKO7.StepDuplicating
