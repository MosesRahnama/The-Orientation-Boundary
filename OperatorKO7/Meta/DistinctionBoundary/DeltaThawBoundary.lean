/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced
import OperatorKO7.Meta.SafeStep_Core

/-!
# Delta-thaw boundary (P-09-1)

For `EqGuardedStep`, confluence does not mention `delta`. The compiled
crown is `ConfluentOn S EqGuardedStep ↔ (¬ S eqW ∧ (S recD → S app))`.
Freezing only `eqW` already enables `delta` congruence and is confluent
(`fullMinusEqW_confluent`). Delta-thaw of the surgical relation is
therefore a theorem, not a conjecture.

The certified relation `SafeStep` is different: `deltaFlag` blocks
`R_merge_void_*` exactly on the recursor-successor shape
`recΔ _ _ (delta _)`. That guard is measure-forced (`kappaM` /
`deltaFlag`), isomorphic to the `recD → app` alignment, not to an extra
confluence freeze of `delta` on `EqGuardedStep`.

The remaining conjecture is contextual closure of `SafeStep` with delta
congruence. This module names the split. It does not reopen Weld 1.
-/

set_option autoImplicit false

open OperatorKO7 Trace
open OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced
open OperatorKO7.EqGuardedConfluence
open MetaSN_KO7

namespace OperatorKO7.Meta.DistinctionBoundary.DeltaThawBoundary

/-- Delta is enabled in the least `eqW` freeze. -/
theorem freezeOnlyEqW_enables_delta :
    (fun c : Ctor => c ≠ Ctor.eqW) Ctor.delta :=
  Ctor.noConfusion

/-- P-09-1, EqGuardedStep half: delta thaw does not break confluence. -/
theorem delta_thaw_does_not_break_eqGuarded :
    ConfluentOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep ∧
      (fun c : Ctor => c ≠ Ctor.eqW) Ctor.delta :=
  ⟨fullMinusEqW_confluent, freezeOnlyEqW_enables_delta⟩

/-- The confluence iff never constrains `S Ctor.delta`. -/
theorem eqGuarded_confluence_independent_of_delta (S : Ctor → Prop)
    (heqW : ¬ S Ctor.eqW) (halign : S Ctor.recD → S Ctor.app) :
    ConfluentOn S EqGuardedStep :=
  (confluentOn_eqGuarded_iff S).mpr ⟨heqW, halign⟩

/-- `deltaFlag` is 1 exactly on the recursor-successor shape. -/
theorem deltaFlag_eq_one_iff (t : Trace) :
    deltaFlag t = 1 ↔ ∃ b s n : Trace, t = recΔ b s (delta n) := by
  constructor
  · intro h
    cases t with
    | recΔ b s n =>
        cases n with
        | delta n => exact ⟨b, s, n, rfl⟩
        | void => simp [deltaFlag] at h
        | integrate n => simp [deltaFlag] at h
        | merge a b' => simp [deltaFlag] at h
        | app a b' => simp [deltaFlag] at h
        | recΔ b' s' n' => simp [deltaFlag] at h
        | eqW a b' => simp [deltaFlag] at h
    | void => simp [deltaFlag] at h
    | delta t => simp [deltaFlag] at h
    | integrate t => simp [deltaFlag] at h
    | merge a b => simp [deltaFlag] at h
    | app a b => simp [deltaFlag] at h
    | eqW a b => simp [deltaFlag] at h
  · rintro ⟨b, s, n, rfl⟩
    rfl

theorem safe_merge_void_left_requires_deltaFlag {t : Trace}
    (h : SafeStep (merge void t) t) :
    deltaFlag t = 0 := by
  cases h with
  | R_merge_void_left _ hδ => exact hδ
  | R_merge_void_right _ hδ => exact hδ
  | R_merge_cancel _ hδ _ => exact hδ

/-- Unconditional kernel step has no such guard. The two relations are
not the same object. -/
theorem step_merge_void_left_unconditional (t : Trace) :
    Step (merge void t) t :=
  Step.R_merge_void_left t

/-- Named remaining conjecture: contextual `SafeStep` with delta
congruence. Kill: a nonjoinable peak. This file does not settle it. -/
def safeStepDeltaCongruenceConfluent : Prop :=
  ConfluentOn (fun c : Ctor => c ≠ Ctor.eqW) SafeStep

end OperatorKO7.Meta.DistinctionBoundary.DeltaThawBoundary
