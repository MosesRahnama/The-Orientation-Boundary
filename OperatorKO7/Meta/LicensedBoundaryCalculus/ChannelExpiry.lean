import OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryTransport
import OperatorKO7.Meta.BoundaryGeneral.PersistentExogeny
import OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance

/-!
# Channel endogenization: the fourth live license-expiry object

`LicenseExpiryCategory` carries three live expiry objects: the coalescing
equality guard, the quote/evaluation peak, and role erasure. `PersistentExogeny`
proves a fourth expiry law, `license_expiry_iff_reachable_echo`, but does not
present its carrier as an object of that category. This module supplies the
missing object.

The license is exogeny: the channel reads the object coordinate. It expires when
the dynamics carries the state to an echo, where the answer no longer depends on
the object. The witness is the comparator episode of `EchoLawInstance`: the
issue state is an off-diagonal pair, whose answer tracks the probe; one collapse
step reaches the diagonal, where the answer is constant.

The construction is not a bare `ExpiryObject.mk`. `consume_unlicensed` is
derived from `EchoLaw.echoAt_iff_not_informativeAt` applied to
`eqwEpisode_echo_on_diagonal`, and `channelExpiry_issue_license_expires`
discharges the expiry through the headline theorem
`license_expiry_iff_reachable_echo`, so the object's two distinguished states are
the issue and consume points of that theorem and not an independent pair.

## Transport verdicts computed here

| direction | verdict | reason |
|---|---|---|
| channel to equality-coalescence | blocked | source consume self-loops, target consume has no outgoing `PairStep` |
| channel to quote/evaluation | blocked | source consume self-loops, a quote value has no outgoing step |
| channel to role erasure | **inhabited** | explicit map sending distinct pairs to the active occurrence |

## Claim typing (binding)

* PROVEN: every theorem below.
* SCOPE: the positive direction is a morphism of expiry objects, not an
  isomorphism and not a claim that channel endogenization and role erasure are
  the same phenomenon. The map is not injective: the four-state pair carrier is
  sent onto the two-state occurrence carrier. The reverse direction is not
  computed in this module.
* SCOPE: the carrier is the two-element comparator episode `eqwEpisode Bool`.
  A different episode gives a different object; nothing here quantifies over all
  episodes.

## Audit slots

- Relation: `channelCollapseStep` on `Bool × Bool`; `PairStep`,
  `QuoteEvalStep true`, and `RoleCollapseStep` at the targets.
- Closure: one-step for the morphism laws; `Relation.ReflTransGen` inside
  `PersistentExogenous`.
- Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.ChannelExpiry

open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryCategory
open OperatorKO7.Meta.LicensedBoundaryCalculus.LicenseExpiryTransport
open OperatorKO7.Meta.BoundaryGeneral.EchoLaw
open OperatorKO7.Meta.BoundaryGeneral.PersistentExogeny
open OperatorKO7.Meta.BoundaryGeneral.EchoLawInstance

/-! ## The endogenizing dynamics -/

/-- **Channel collapse.** One step overwrites the first component with the
second, so every successor is diagonal. This is the informational form of guard
expiry: the coordinate the channel was reading is erased. -/
def channelCollapseStep (x y : Bool × Bool) : Prop := y = (x.2, x.2)

/-- The diagonal is reached in one step from anywhere. -/
theorem channelCollapseStep_target_diagonal {x y : Bool × Bool}
    (h : channelCollapseStep x y) : y.1 = y.2 := by
  rw [h]

/-- Every diagonal pair of the comparator episode is an echo state. -/
theorem echo_of_diagonal {p : Bool × Bool} (h : p.1 = p.2) :
    EchoAt (eqwEpisode Bool) p := by
  intro o o'
  simp [eqwEpisode, h]

/-- Exogeny forces the pair to be off diagonal: a diagonal answer is constant. -/
theorem offDiagonal_of_exogenous {p : Bool × Bool}
    (h : Exogenous (eqwEpisode Bool) p) : p.1 ≠ p.2 := by
  intro hdiag
  exact (echoAt_iff_not_informativeAt (eqwEpisode Bool) p).mp (echo_of_diagonal hdiag) h

/-! ## The object -/

/-- The issue state is exogenous: the answer tracks the object probe. -/
theorem channel_issue_exogenous : Exogenous (eqwEpisode Bool) (true, false) :=
  eqwEpisode_informative_off_diagonal (by decide)

/-- The consume state is an echo. -/
theorem channel_consume_echo : EchoAt (eqwEpisode Bool) (false, false) :=
  eqwEpisode_echo_on_diagonal false

/-- The consume state is not exogenous, derived from the echo law rather than
asserted. -/
theorem channel_consume_not_exogenous : ¬ Exogenous (eqwEpisode Bool) (false, false) :=
  (echoAt_iff_not_informativeAt (eqwEpisode Bool) (false, false)).mp channel_consume_echo

/-- **The fourth live expiry object.** Exogeny holds at an off-diagonal issue
state and fails at the diagonal consume state one collapse step later. -/
def channelExpiry : ExpiryObject where
  Carrier := Bool × Bool
  dynamics := channelCollapseStep
  license := Exogenous (eqwEpisode Bool)
  issue := (true, false)
  consume := (false, false)
  crossing := rfl
  issue_licensed := channel_issue_exogenous
  consume_unlicensed := channel_consume_not_exogenous

/-- **The object realizes the expiry theorem.** The issue state carries no
persistent exogeny license along the collapse dynamics, discharged through
`license_expiry_iff_reachable_echo`. The object's two distinguished states are
the issue and consume points of that theorem. -/
theorem channelExpiry_issue_license_expires :
    ¬ PersistentExogenous (eqwEpisode Bool) channelCollapseStep (true, false) :=
  (license_expiry_iff_reachable_echo channel_issue_exogenous).mpr
    ⟨(false, false), Relation.ReflTransGen.single rfl, channel_consume_echo⟩

/-- The consume state has a genuine dynamics self-loop: collapse is idempotent
on the diagonal. -/
theorem channel_consume_self_loop :
    channelExpiry.dynamics channelExpiry.consume channelExpiry.consume := rfl

/-! ## Transport verdicts -/

/-- Channel expiry cannot map to equality expiry: the source consume state has a
self-loop while the target consume state has no outgoing `PairStep`. -/
theorem no_hom_channel_eqW : IsEmpty (Hom channelExpiry eqWExpiry) := by
  refine ⟨?_⟩
  intro f
  have hstep := f.dynamics_preserve channel_consume_self_loop
  rw [f.consume_map] at hstep
  exact no_pairStep_from_consume hstep

/-- Channel expiry cannot map to quote expiry: the source consume state has a
self-loop while a quote value has no outgoing step. -/
theorem no_hom_channel_quote : IsEmpty (Hom channelExpiry quoteExpiry) := by
  refine ⟨?_⟩
  intro f
  have hstep := f.dynamics_preserve channel_consume_self_loop
  rw [f.consume_map] at hstep
  exact no_quoteStep_from_consume hstep

/-- The carrier map: a distinct pair is the live occurrence, a diagonal pair the
frame occurrence. -/
def channelToRole (p : Bool × Bool) : Occ Unit :=
  if p.1 = p.2 then ((), Role.frame) else ((), Role.active)

/-- The map sends every diagonal pair to the frame occurrence. -/
theorem channelToRole_diagonal {p : Bool × Bool} (h : p.1 = p.2) :
    channelToRole p = ((), Role.frame) := by
  unfold channelToRole
  rw [if_pos h]

/-- **The positive direction.** Channel endogenization transports into role
erasure: exogeny maps to activity and the collapse step maps to role collapse.
This is a morphism of expiry objects, not an isomorphism. -/
def homChannelRole : Hom channelExpiry roleExpiry where
  toFun := channelToRole
  issue_map := by
    show channelToRole (true, false) = ((), Role.active)
    simp [channelToRole]
  consume_map := by
    show channelToRole (false, false) = ((), Role.frame)
    simp [channelToRole]
  dynamics_preserve := by
    intro x y h
    show channelToRole y = roleCollapse (channelToRole x)
    rw [channelToRole_diagonal (channelCollapseStep_target_diagonal h)]
    unfold roleCollapse
    rfl
  license_preserve := by
    intro x hx
    show isActive (channelToRole x)
    unfold channelToRole
    rw [if_neg (offDiagonal_of_exogenous hx)]
    rfl

/-- The channel-to-role transport is inhabited. -/
theorem hom_channel_role_nonempty : Nonempty (Hom channelExpiry roleExpiry) :=
  ⟨homChannelRole⟩

/-! ## The four-object bundle -/

/-- All four live expiry objects are non-vacuous: each licenses its issue state
and refuses its consume state. This extends `three_live_expiry_witnesses` with
the channel row. -/
theorem four_live_expiry_witnesses :
    eqWExpiry.license eqWExpiry.issue ∧ ¬ eqWExpiry.license eqWExpiry.consume ∧
    quoteExpiry.license quoteExpiry.issue ∧ ¬ quoteExpiry.license quoteExpiry.consume ∧
    roleExpiry.license roleExpiry.issue ∧ ¬ roleExpiry.license roleExpiry.consume ∧
    channelExpiry.license channelExpiry.issue ∧
      ¬ channelExpiry.license channelExpiry.consume :=
  ⟨eqWExpiry.issue_licensed, eqWExpiry.consume_unlicensed,
   quoteExpiry.issue_licensed, quoteExpiry.consume_unlicensed,
   roleExpiry.issue_licensed, roleExpiry.consume_unlicensed,
   channelExpiry.issue_licensed, channelExpiry.consume_unlicensed⟩

/-- **The fourth-object law.** Channel endogenization is a live expiry object:
its issue state is exogenous, its consume state is an echo and therefore
unlicensed, the issue state carries no persistent license along the collapse
dynamics, transport to the equality-coalescence and quote/evaluation objects is
blocked, and transport to role erasure is inhabited. -/
theorem channel_expiry_is_fourth_object :
    Exogenous (eqwEpisode Bool) channelExpiry.issue ∧
    EchoAt (eqwEpisode Bool) channelExpiry.consume ∧
    ¬ Exogenous (eqwEpisode Bool) channelExpiry.consume ∧
    ¬ PersistentExogenous (eqwEpisode Bool) channelCollapseStep (true, false) ∧
    IsEmpty (Hom channelExpiry eqWExpiry) ∧
    IsEmpty (Hom channelExpiry quoteExpiry) ∧
    Nonempty (Hom channelExpiry roleExpiry) :=
  ⟨channel_issue_exogenous, channel_consume_echo, channel_consume_not_exogenous,
   channelExpiry_issue_license_expires, no_hom_channel_eqW, no_hom_channel_quote,
   hom_channel_role_nonempty⟩

end OperatorKO7.Meta.LicensedBoundaryCalculus.ChannelExpiry
