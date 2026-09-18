/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
import OperatorKO7.Meta.DependencyPairs_Works

/-!
# DP channel instance (Roadmap 09, F2)

Weld 2's generic channel theorems live in `RoleErasureInstance`. This module
instantiates them at the compiled KO7 `rec_succ` extraction.

Direct-form attempt: `MetaDependencyPairs.DPPair` is an inductive relation
(`Trace → Trace → Prop`), not a function `Trace → Trace`. The certificate
`rec_succ_extracts_dependency_pair` packages `Step.R_rec_succ` with
`DPPair.rec_succ`. No in-tree map sends an arbitrary kernel term to its
extracted pairs.

Licensed fallback: the certificate induces a function on the `R_rec_succ`
family only, `extractRecSuccDP b s n := recΔ b s n`, certified by
`DPPair.rec_succ`. Bounded follow-up: a total functional extraction covering
all eight kernel rules (the gap already named
`noCompleteExtractionAndProcessorSoundness` in the closed-carrier ledger).

Encoding of the reduct `app s (recΔ b s n)`:
* frame occurrence carries `s` at the applied position;
* active occurrence carries the recursive call `recΔ b s n`.

The role-erasure carrier for one family is `Occ Unit` (same dummy value, two
roles). `encodedTerm` recovers the Trace at each role. `actualDPChannel`
asks whether that Trace equals the extracted callee. Crown:
`decodeActive ∘ actualDPChannel = isActive` on every occurrence of that
carrier, which is exactly the encoded pair. The two Weld 2 corollaries are
`exact` applications of the generic theorems.

NameGated (read, not edited):
`MetaDependencyPairs.DPPair`, `DPPair.rec_succ`,
`rec_succ_extracts_dependency_pair`, `Role.frame`, `Role.active`, `Occ`,
`isActive`, `dp_license_is_exogenous_separator`,
`dp_license_not_value_factored`.

Relation: `Step` / `DPPair` on the `rec_succ` family. Closure: not applicable
(channel, not a rewrite closure). Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

namespace OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance

/-! ## Induced extraction on the `R_rec_succ` family -/

/-- Function induced by `DPPair.rec_succ`: the extracted callee of
`recΔ b s (delta n) → app s (recΔ b s n)` is the recursive call. -/
def extractRecSuccDP (b s n : Trace) : Trace :=
  recΔ b s n

/-- The induced function is exactly the compiled `rec_succ` certificate. -/
theorem extractRecSuccDP_certified (b s n : Trace) :
    Step (recΔ b s (delta n)) (app s (extractRecSuccDP b s n)) ∧
      DPPair (recΔ b s (delta n)) (extractRecSuccDP b s n) :=
  rec_succ_extracts_dependency_pair b s n

/-- The applied step term is never the extracted recursive call (inductive
acyclicity). -/
theorem step_ne_extracted : ∀ (b s n : Trace), s ≠ recΔ b s n
  | _, void, _, h => nomatch h
  | _, delta _, _, h => nomatch h
  | _, integrate _, _, h => nomatch h
  | _, merge _ _, _, h => nomatch h
  | _, app _ _, _, h => nomatch h
  | _, eqW _ _, _, h => nomatch h
  | _, recΔ b' s' n', _, h => by
      injection h with _ hs _
      exact step_ne_extracted b' s' n' hs

/-! ## Encoding of the reduct as occurrences -/

/-- Frame occurrence: `s` at the applied position of `app s (recΔ b s n)`. -/
def encodeFrame (_b s _n : Trace) : Occ Trace :=
  (s, Role.frame)

/-- Active occurrence: the recursive call selected by `DPPair.rec_succ`. -/
def encodeActive (b s n : Trace) : Occ Trace :=
  (recΔ b s n, Role.active)

/-- Trace carried by a role in the encoded pair. The role-erasure carrier is
`Occ Unit`; this map reads the encoding back as kernel terms. -/
def encodedTerm (b s n : Trace) (o : Occ Unit) : Trace :=
  match o.2 with
  | Role.frame => s
  | Role.active => recΔ b s n

theorem encodedTerm_frame (b s n : Trace) :
    encodedTerm b s n (((), Role.frame) : Occ Unit) = (encodeFrame b s n).1 :=
  rfl

theorem encodedTerm_active (b s n : Trace) :
    encodedTerm b s n (((), Role.active) : Occ Unit) = (encodeActive b s n).1 :=
  rfl

/-! ## Channel and crown -/

/-- The extraction map read through the encoding: selected iff the occurrence's
encoded Trace equals the induced callee. -/
def actualDPChannel (b s n : Trace) (o : Occ Unit) : Bool :=
  decide (encodedTerm b s n o = extractRecSuccDP b s n)

/-- Active-role decoding of a Boolean channel flag. -/
def decodeActive (flag : Bool) : Prop :=
  flag = true

/-- **Crown.** On the encoded occurrence pair (the whole carrier `Occ Unit`
for one family), decoding the actual DP channel recovers activity. -/
theorem actualDPChannel_decodes_isActive (b s n : Trace) :
    ∀ o : Occ Unit, decodeActive (actualDPChannel b s n o) ↔ isActive o := by
  intro o
  rcases o with ⟨u, r⟩
  cases u
  cases r with
  | frame =>
      simp [actualDPChannel, decodeActive, encodedTerm, extractRecSuccDP,
        isActive, step_ne_extracted b s n]
  | active =>
      simp [actualDPChannel, decodeActive, encodedTerm, extractRecSuccDP,
        isActive]

/-- Weld 2 separator, specialized to `actualDPChannel`. No re-proof. -/
theorem actual_dp_license_is_exogenous_separator (b s n : Trace) :
    actualDPChannel b s n (((), Role.frame) : Occ Unit) ≠
      actualDPChannel b s n (((), Role.active) : Occ Unit) :=
  dp_license_is_exogenous_separator () (actualDPChannel b s n) decodeActive
    (actualDPChannel_decodes_isActive b s n)

/-- Weld 2 externality, specialized to `actualDPChannel`. No re-proof. -/
theorem actual_dp_license_not_value_factored (b s n : Trace) :
    ¬ ∃ g : Unit → Bool, ∀ o : Occ Unit, actualDPChannel b s n o = g o.1 :=
  dp_license_not_value_factored () (actualDPChannel b s n) decodeActive
    (actualDPChannel_decodes_isActive b s n)

/-! ## R5: encoded instance `b = s = n = void` -/

theorem r5_frame_not_selected :
    actualDPChannel void void void (((), Role.frame) : Occ Unit) = false := by
  change decide (void = recΔ void void void) = false
  exact decide_eq_false (step_ne_extracted void void void)

theorem r5_active_selected :
    actualDPChannel void void void (((), Role.active) : Occ Unit) = true := by
  simp [actualDPChannel, encodedTerm, extractRecSuccDP]

theorem r5_crown :
    (decodeActive (actualDPChannel void void void (((), Role.frame) : Occ Unit)) ↔
      isActive (encodeFrame void void void)) ∧
    (decodeActive (actualDPChannel void void void (((), Role.active) : Occ Unit)) ↔
      isActive (encodeActive void void void)) := by
  constructor
  · simp [decodeActive, r5_frame_not_selected, isActive, encodeFrame]
  · simp [decodeActive, r5_active_selected, isActive, encodeActive]

end OperatorKO7.Meta.DistinctionBoundary.DPChannelInstance
