/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.FreezePositions

/-!
# Write-dependency closure for positional freeze sets

The live positional confluence crown proves that thawing the `recD` context
forces both positions written by its contracta, `appL` and `appR`. This module
turns that dependency into a closure operator and computes the least confluent
repair of an arbitrary requested thaw set: first freeze `eqW`, then close under
the live write dependencies.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.WriteClosure

open OperatorKO7
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.FreezePositions

/-- Pointwise inclusion of positional selections. -/
def SelectionLE (S T : CtorPos → Prop) : Prop :=
  ∀ c, S c → T c

/-- A positional selection contains every context position written by each
thawed rule family. For the live equality-guarded KO7 relation, `recD` writes
to both application positions. -/
def WriteClosed (S : CtorPos → Prop) : Prop :=
  (S .recD → S .appL) ∧ (S .recD → S .appR)

/-- Least closure under the live KO7 write dependencies. -/
def writeClosure (S : CtorPos → Prop) : CtorPos → Prop
  | .appL => S .appL ∨ S .recD
  | .appR => S .appR ∨ S .recD
  | c => S c

/-- Every requested position belongs to its write closure. -/
theorem writeClosure_extensive (S : CtorPos → Prop) :
    SelectionLE S (writeClosure S) := by
  intro c hc
  cases c <;> simp only [writeClosure]
  · exact hc
  · exact hc
  · exact hc
  · exact hc
  · exact Or.inl hc
  · exact Or.inl hc
  · exact hc
  · exact hc

/-- Write closure is monotone in the requested thaw set. -/
theorem writeClosure_monotone {S T : CtorPos → Prop}
    (hST : SelectionLE S T) :
    SelectionLE (writeClosure S) (writeClosure T) := by
  intro c hc
  cases c <;> simp only [writeClosure] at hc ⊢
  · exact hST .void hc
  · exact hST .delta hc
  · exact hST .integrate hc
  · exact hST .merge hc
  · exact hc.elim (fun h => Or.inl (hST .appL h))
      (fun h => Or.inr (hST .recD h))
  · exact hc.elim (fun h => Or.inl (hST .appR h))
      (fun h => Or.inr (hST .recD h))
  · exact hST .recD hc
  · exact hST .eqW hc

/-- The closure contains no new `recD` membership. -/
theorem writeClosure_recD_iff (S : CtorPos → Prop) :
    writeClosure S .recD ↔ S .recD := by
  rfl

/-- The closure contains no new `eqW` membership. -/
theorem writeClosure_eqW_iff (S : CtorPos → Prop) :
    writeClosure S .eqW ↔ S .eqW := by
  rfl

/-- Applying write closure once produces a write-closed selection. -/
theorem writeClosure_closed (S : CtorPos → Prop) :
    WriteClosed (writeClosure S) := by
  constructor
  · intro h
    exact Or.inr h
  · intro h
    exact Or.inr h

/-- Write closure is idempotent. -/
theorem writeClosure_idempotent (S : CtorPos → Prop) :
    writeClosure (writeClosure S) = writeClosure S := by
  funext c
  apply propext
  cases c <;> simp [writeClosure]

/-- Write closure is the least write-closed extension of the input. -/
theorem writeClosure_least {S T : CtorPos → Prop}
    (hExt : SelectionLE S T) (hClosed : WriteClosed T) :
    SelectionLE (writeClosure S) T := by
  intro c hc
  cases c <;> simp only [writeClosure] at hc
  · exact hExt .void hc
  · exact hExt .delta hc
  · exact hExt .integrate hc
  · exact hExt .merge hc
  · exact hc.elim (hExt .appL) (fun h => hClosed.1 (hExt .recD h))
  · exact hc.elim (hExt .appR) (fun h => hClosed.2 (hExt .recD h))
  · exact hExt .recD hc
  · exact hExt .eqW hc

/-- Freeze the unique position whose congruence necessarily destroys
confluence, while preserving every other requested position. -/
def freezeEqW (S : CtorPos → Prop) (c : CtorPos) : Prop :=
  S c ∧ c ≠ .eqW

/-- The canonical repair: freeze `eqW`, then add every forced write position. -/
def confluenceRepair (S : CtorPos → Prop) : CtorPos → Prop :=
  writeClosure (freezeEqW S)

/-- The repair preserves every requested position other than `eqW`. -/
theorem confluenceRepair_extends_nonEqW (S : CtorPos → Prop) :
    ∀ c, S c → c ≠ .eqW → confluenceRepair S c := by
  intro c hc hne
  exact writeClosure_extensive (freezeEqW S) c ⟨hc, hne⟩

/-- The repair freezes `eqW`. -/
theorem confluenceRepair_freezes_eqW (S : CtorPos → Prop) :
    ¬ confluenceRepair S .eqW := by
  intro h
  exact h.2 rfl

/-- The repair is write closed. -/
theorem confluenceRepair_writeClosed (S : CtorPos → Prop) :
    WriteClosed (confluenceRepair S) :=
  writeClosure_closed (freezeEqW S)

/-- The canonical repair is confluent for the live equality-guarded relation. -/
theorem confluenceRepair_confluent (S : CtorPos → Prop) :
    ConfluentOnPos (confluenceRepair S) EqGuardedStep := by
  apply freeze_eqW_recAppPosAligned_restores_confluence
  · exact confluenceRepair_freezes_eqW S
  · exact (confluenceRepair_writeClosed S).1
  · exact (confluenceRepair_writeClosed S).2

/-- Every confluent selection containing the requested non-`eqW` positions
contains the canonical repair. This is leastness in the admissible extension
order, not an enum-order claim. -/
theorem confluenceRepair_least {S T : CtorPos → Prop}
    (hT : ConfluentOnPos T EqGuardedStep)
    (hExt : ∀ c, S c → c ≠ .eqW → T c) :
    SelectionLE (confluenceRepair S) T := by
  have hCharacterization := (confluentOnPos_eqGuarded_iff T).mp hT
  apply writeClosure_least
  · intro c hc
    exact hExt c hc.1 hc.2
  · exact ⟨hCharacterization.2.1, hCharacterization.2.2⟩

/-- Freezing `eqW` is idempotent. -/
theorem freezeEqW_idempotent (S : CtorPos → Prop) :
    freezeEqW (freezeEqW S) = freezeEqW S := by
  funext c
  apply propext
  simp [freezeEqW]

/-- If `eqW` is already frozen, `freezeEqW` changes nothing. -/
theorem freezeEqW_eq_self_of_eqW_frozen {S : CtorPos → Prop}
    (hEqW : ¬ S .eqW) :
    freezeEqW S = S := by
  funext c
  apply propext
  constructor
  · exact fun h => h.1
  · intro hc
    refine ⟨hc, ?_⟩
    intro hceq
    subst hceq
    exact hEqW hc

/-- The canonical confluence repair is idempotent. -/
theorem confluenceRepair_idempotent (S : CtorPos → Prop) :
    confluenceRepair (confluenceRepair S) = confluenceRepair S := by
  have hEqW : ¬ confluenceRepair S .eqW := confluenceRepair_freezes_eqW S
  rw [confluenceRepair, freezeEqW_eq_self_of_eqW_frozen hEqW]
  exact writeClosure_idempotent (freezeEqW S)

/-- Seed that requests only the `recD` context. -/
def recDSeed (c : CtorPos) : Prop :=
  c = .recD

/-- Exact computation of the closure generated by `recD`. -/
theorem writeClosure_recDSeed_exact (c : CtorPos) :
    writeClosure recDSeed c ↔
      c = .recD ∨ c = .appL ∨ c = .appR := by
  cases c <;> simp [writeClosure, recDSeed]

/-- The `recD` seed already freezes `eqW`, so its canonical repair is exactly
its write closure. -/
theorem confluenceRepair_recDSeed_eq_writeClosure :
    confluenceRepair recDSeed = writeClosure recDSeed := by
  rw [confluenceRepair, freezeEqW_eq_self_of_eqW_frozen]
  intro h
  change CtorPos.eqW = CtorPos.recD at h
  cases h

/-- The raw `recD` history and its write-closed history are genuinely distinct. -/
theorem recDSeed_ne_writeClosure :
    recDSeed ≠ writeClosure recDSeed := by
  intro h
  have happL : writeClosure recDSeed .appL := Or.inr rfl
  rw [← h] at happL
  change CtorPos.appL = CtorPos.recD at happL
  cases happL

/-- `confluenceRepair` loses history: the raw seed and its already-closed image
compile to the same repaired record. -/
theorem recDSeed_two_histories_same_repair :
    confluenceRepair recDSeed =
      confluenceRepair (writeClosure recDSeed) := by
  have hid := confluenceRepair_idempotent recDSeed
  rw [confluenceRepair_recDSeed_eq_writeClosure] at hid
  rw [confluenceRepair_recDSeed_eq_writeClosure]
  exact hid.symm

/-- Before write closure, the `recD`-only seed is not confluent. -/
theorem recDSeed_not_confluent :
    ¬ ConfluentOnPos recDSeed EqGuardedStep := by
  apply recD_thaw_appR_freeze_breaks_confluence
  · rfl
  · intro h
    cases h

/-- Write closure repairs the concrete `recD` seed. -/
theorem writeClosure_recDSeed_confluent :
    ConfluentOnPos (writeClosure recDSeed) EqGuardedStep := by
  apply freeze_eqW_recAppPosAligned_restores_confluence
  · intro h
    change CtorPos.eqW = CtorPos.recD at h
    cases h
  · exact (writeClosure_closed recDSeed).1
  · exact (writeClosure_closed recDSeed).2

/-- Concrete R5 receipt: closing the exact write set changes the live
confluence outcome from false to true. -/
theorem recDSeed_writeClosure_changes_outcome :
    (¬ ConfluentOnPos recDSeed EqGuardedStep) ∧
      ConfluentOnPos (writeClosure recDSeed) EqGuardedStep :=
  ⟨recDSeed_not_confluent, writeClosure_recDSeed_confluent⟩

end OperatorKO7.Meta.DistinctionBoundary.WriteClosure
