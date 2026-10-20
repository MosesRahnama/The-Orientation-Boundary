import OperatorKO7.Kernel
import OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import OperatorKO7.Meta.SafeStep.GaugeFixingGuard
import OperatorKO7.Meta.EqW_Guard_Barrier

set_option autoImplicit false

/-!
# Distinction Inexpressibility + Confluence-Axis Witness Order (WAVE2-E)

Self-contained reusable wrapper file. Two honest parts, nothing
re-proved: every headline result is discharged by citing an existing
unconditional theorem in the tree.

## Part 1 — named inexpressibility predicate

`DistinctionInexpressible` is a reusable named `Prop`, parameterised by
the evaluator/signature triple actually used by
`OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional`
(the `SigmaFreeAlgebra.SigmaTerm` algebra and its substitution evaluator
`evalSigma`). It says: no single signature term `t` computes the
disequality `a ≠ b` as the predicate `evalSigma a b t ≠ void`. The KO7
instance `ko7_distinctionInexpressible` is the unconditional theorem,
re-wrapped under the named predicate.

## Part 2 — confluence-axis witness order (SCOPED & HONEST)

This is the confluence-axis analogue of the orientation-axis
`OperatorKO7.WitnessOrder` `WLevel`/`kappaGt` shape, scoped to exactly
what is provable here. The minimal claim is:

 raw object-level witness (unguarded `Step`) is INADEQUATE for diagonal
 local confluence, while the external-license witness (SafeStep guard)
 is ADEQUATE; hence the minimal adequate confluence-witness level is
 nonzero.

We do NOT build a fully-inhabited D0/D1/D2/D3 ladder. Only two levels are
named: `CWLevel.raw` (the object-level `Step` peak) and `CWLevel.license`
(the SafeStep external-distinction guard). Inadequacy of `raw` is
`OperatorKO7.Meta.EqW_Guard_Barrier.not_localJoinStep_eqW_refl`; adequacy
of `license` is
`OperatorKO7.Meta.SafeStep.GaugeFixingGuard.safestep_guard_restores_local_confluence`.
The order facts `kappaDist_pos` / `kappaDist_ge_one` package
"raw inadequate ∧ license adequate ⟹ witness order nonzero".

No `sorry`, `admit`, `axiom`, `native_decide`, `@[csimp]`, `unsafe`,
`partial`, or `opaque`. `GenericDiagonalFork` is NOT imported. No existing
file is modified.
-/

open OperatorKO7 Trace

namespace OperatorKO7.Meta.SafeStep.DistinctionInexpressible

open OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
open OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

/-! ## Part 1 — named inexpressibility predicate -/

/-- Reusable named predicate capturing "no direct signature term computes
disequality". Parameterised by an abstract carrier `S`, a designated
collapse point `nil : S`, and a three-argument evaluator
`ev : S → S → S → S` reading `ev a b t` as "term `t` evaluated with its
two predicate slots bound to `a` and `b`".

`IsDistinctionInexpressible ev nil` holds when there is NO single signature
term `t` whose induced predicate `ev a b t ≠ nil` coincides, for every
pair `(a, b)`, with the disequality `a ≠ b`. This is the abstract shape of
the classification claim; the KO7 instance below pins `S`, `nil`, `ev`
to the real `SigmaFreeAlgebra` types. -/
def IsDistinctionInexpressible {S : Type} (ev : S → S → S → S) (nil : S) : Prop :=
  ¬ ∃ t : S, ∀ a b : S, (a ≠ b) ↔ (ev a b t ≠ nil)

/-- The KO7 instance of `IsDistinctionInexpressible`, specialised to the
`SigmaFreeAlgebra.SigmaTerm` signature algebra, its substitution evaluator
`evalSigma`, and the `void` collapse point. Proven by citing the
unconditional theorem
`disequality_not_sigma_expressible_unconditional`; nothing is re-proved. -/
theorem ko7_distinctionInexpressible :
    IsDistinctionInexpressible (S := SigmaTerm) evalSigma SigmaTerm.void :=
  disequality_not_sigma_expressible_unconditional

/-- Convenience unfolding: the KO7 instance is definitionally the
unconditional non-expressibility statement over `SigmaTerm`. -/
theorem ko7_distinctionInexpressible_iff :
    IsDistinctionInexpressible (S := SigmaTerm) evalSigma SigmaTerm.void
      ↔ ¬ ∃ t : SigmaTerm, ∀ a b : SigmaTerm,
            (a ≠ b) ↔ (evalSigma a b t ≠ SigmaTerm.void) :=
  Iff.rfl

/-! ## Part 2 — confluence-axis witness order (SCOPED & HONEST) -/

/-- Coarse confluence-axis witness levels. SCOPED: only the two genuinely
inhabited-and-distinguished levels are named. `raw` is the object-level
unguarded `Step` peak; `license` is the external SafeStep distinction
guard that supplies the disequality decision from outside the rewriting
layer. This mirrors the orientation-axis `OperatorKO7.WitnessOrder.WLevel`
shape (an `inductive` with a `toNat` grade and `LE`/`LT` instances) but is
deliberately a small local definition rather than a full D0..D3 ladder,
because only these two levels are provably adequate/inadequate here. -/
inductive CWLevel
  | raw
  | license
deriving DecidableEq, Repr

namespace CWLevel

/-- Numeric grade: `raw = 0` (object level), `license = 1` (external
distinction license). -/
def toNat : CWLevel → Nat
  | raw => 0
  | license => 1

instance : LE CWLevel := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance : LT CWLevel := ⟨fun a b => a.toNat < b.toNat⟩

instance (a b : CWLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))
instance (a b : CWLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

@[simp] theorem toNat_raw : toNat raw = 0 := rfl
@[simp] theorem toNat_license : toNat license = 1 := rfl

end CWLevel

/-- Adequacy of a confluence-witness level for the diagonal `eqW`
critical pair, scoped to exactly what each level can do.

 * `raw`: adequate iff the unguarded object-level `Step` peak at
 `eqW a a` is locally joinable for every `a`. (It is NOT — that is
 `not_localJoinStep_eqW_refl`.)
 * `license`: adequate iff, given an external distinction guard
 `SafeStepGuard a b`, the SafeStep peak at `eqW a b` is locally
 joinable. (It IS — that is `safestep_guard_restores_local_confluence`.)

This is a layer-honest definition: it asks each level for precisely the
join it is responsible for, no more. -/
def DiagAdequate : CWLevel → Prop
  | CWLevel.raw =>
      ∀ a : Trace, MetaSN_KO7.LocalJoinStep (eqW a a)
  | CWLevel.license =>
      ∀ {a b : Trace},
        OperatorKO7.Meta.SafeStep.GaugeFixingGuard.SafeStepGuard a b →
          MetaSN_KO7.LocalJoinSafe (eqW a b)

/-- The raw object-level witness is INADEQUATE for diagonal local
confluence: the unguarded `Step` peak at `eqW a a` is never locally
joinable. Cites `EqW_Guard_Barrier.not_localJoinStep_eqW_refl`; nothing
re-proved. -/
theorem raw_inadequate : ¬ DiagAdequate CWLevel.raw := by
  intro h
  exact OperatorKO7.Meta.EqW_Guard_Barrier.not_localJoinStep_eqW_refl void (h void)

/-- The external-license witness is ADEQUATE: the SafeStep distinction
guard restores local confluence at the (off-diagonal) `eqW a b` peak.
Cites `GaugeFixingGuard.safestep_guard_restores_local_confluence`;
nothing re-proved. -/
theorem license_adequate : DiagAdequate CWLevel.license := by
  intro a b g
  exact OperatorKO7.Meta.SafeStep.GaugeFixingGuard.safestep_guard_restores_local_confluence g

/-- The minimal adequate confluence-witness level, as a relation between a
level and the pair of facts "raw inadequate" and "this level adequate".
Honest content only: it records that some level `ℓ` is diagonally adequate
while the `raw` object level is not. -/
def MinimalAdequateAt (ℓ : CWLevel) : Prop :=
  ¬ DiagAdequate CWLevel.raw ∧ DiagAdequate ℓ

/-- `license` is a minimal-adequate confluence-witness level: raw is
inadequate, license is adequate. -/
theorem license_minimalAdequate : MinimalAdequateAt CWLevel.license :=
  ⟨raw_inadequate, license_adequate⟩

/-- `κ_dist > 0`: the minimal adequate confluence-witness level is strictly
above the raw object level. Packaged honestly as: raw is inadequate while
the strictly-higher `license` level is adequate, so the adequate level
cannot be `raw`. The numeric witness is `CWLevel.raw < CWLevel.license`. -/
theorem kappaDist_pos :
    ¬ DiagAdequate CWLevel.raw
      ∧ DiagAdequate CWLevel.license
      ∧ CWLevel.raw < CWLevel.license := by
  refine ⟨raw_inadequate, license_adequate, ?_⟩
  decide

/-- `κ_dist ≥ 1`: restated on the numeric grade. The grade of a
minimal adequate level (`license`, grade `1`) is at least `1`, strictly
above the raw grade (`0`). The unguarded diagonal query must climb above
the raw object level. -/
theorem kappaDist_ge_one :
    1 ≤ CWLevel.license.toNat ∧ CWLevel.raw.toNat < CWLevel.license.toNat := by
  decide

/-- Confluence-axis summary, the scoped analogue of
`OperatorKO7.WitnessOrder.ko7_three_kappa_summary`: raw object-level
witness inadequate for the diagonal `eqW` peak, external-license witness
adequate, hence the minimal adequate confluence-witness level is nonzero. -/
theorem ko7_confluence_witnessOrder_nonzero :
    ¬ DiagAdequate CWLevel.raw
      ∧ DiagAdequate CWLevel.license
      ∧ MinimalAdequateAt CWLevel.license
      ∧ CWLevel.raw < CWLevel.license :=
  ⟨raw_inadequate, license_adequate, license_minimalAdequate, by decide⟩

/-- **`κ_dist = 1` (the minimal adequate level is exactly one, not merely nonzero).**
On the two-level grade, every diagonally adequate level has numeric grade at least one,
since the only grade-zero level is `raw` and it is inadequate; and the grade-one level
`license` is adequate. The minimal adequate confluence-witness grade is therefore
exactly one: the external disequality license is the minimal level that repairs the
diagonal, and no object-level (grade-zero) witness suffices. -/
theorem kappaDist_eq_one :
    (∀ ℓ : CWLevel, DiagAdequate ℓ → 1 ≤ ℓ.toNat) ∧ DiagAdequate CWLevel.license := by
  refine ⟨?_, license_adequate⟩
  intro ℓ h
  cases ℓ with
  | raw => exact absurd h raw_inadequate
  | license => decide

#print axioms kappaDist_eq_one

#print axioms ko7_distinctionInexpressible
#print axioms raw_inadequate
#print axioms license_adequate
#print axioms kappaDist_pos
#print axioms kappaDist_ge_one
#print axioms ko7_confluence_witnessOrder_nonzero

end OperatorKO7.Meta.SafeStep.DistinctionInexpressible
